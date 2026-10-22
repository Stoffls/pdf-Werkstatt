// PDF Werkstatt – Bildverarbeitung für das Scannen
// Blatterkennung, perspektivische Entzerrung und Lesbarkeits-Filter.
// Reine Rechenfunktionen ohne Bedienoberfläche.

export const A4 = { w: 595.28, h: 841.89 };
const SQRT2 = Math.SQRT2;

/** Lädt ein Foto (berücksichtigt die Aufnahme-Ausrichtung) und verkleinert es auf maxSide. */
export async function loadPhoto(file, maxSide = 2800) {
  let bmp;
  try {
    bmp = await createImageBitmap(file, { imageOrientation: 'from-image' });
  } catch {
    bmp = await new Promise((resolve, reject) => {
      const url = URL.createObjectURL(file);
      const img = new Image();
      img.onload = () => { URL.revokeObjectURL(url); resolve(img); };
      img.onerror = () => { URL.revokeObjectURL(url); reject(new Error('Bild kann nicht gelesen werden')); };
      img.src = url;
    });
  }
  const w0 = bmp.width;
  const h0 = bmp.height;
  if (!w0 || !h0) throw new Error('Bild ist leer');
  const s = Math.min(1, maxSide / Math.max(w0, h0));
  const c = document.createElement('canvas');
  c.width = Math.max(1, Math.round(w0 * s));
  c.height = Math.max(1, Math.round(h0 * s));
  const ctx = c.getContext('2d', { willReadFrequently: true });
  ctx.drawImage(bmp, 0, 0, c.width, c.height);
  if (bmp.close) bmp.close();
  return c;
}

/** Dreht ein Canvas um Vielfache von 90° im Uhrzeigersinn. */
export function rotateCanvas(src, deg) {
  const d = ((deg % 360) + 360) % 360;
  if (!d) return src;
  const c = document.createElement('canvas');
  const swap = d === 90 || d === 270;
  c.width = swap ? src.height : src.width;
  c.height = swap ? src.width : src.height;
  const ctx = c.getContext('2d');
  ctx.translate(c.width / 2, c.height / 2);
  ctx.rotate((d * Math.PI) / 180);
  ctx.drawImage(src, -src.width / 2, -src.height / 2);
  return c;
}

// ------------------------------------------------------------------ Blatterkennung
function otsu(hist, total) {
  let sum = 0;
  for (let i = 0; i < 256; i++) sum += i * hist[i];
  let sumB = 0, wB = 0, best = 0, thr = 128;
  for (let t = 0; t < 256; t++) {
    wB += hist[t];
    if (!wB) continue;
    const wF = total - wB;
    if (!wF) break;
    sumB += t * hist[t];
    const mB = sumB / wB;
    const mF = (sum - sumB) / wF;
    const between = wB * wF * (mB - mF) * (mB - mF);
    if (between > best) { best = between; thr = t; }
  }
  return thr;
}
function boxBlur(src, w, h, r) {
  const tmp = new Float32Array(w * h);
  const out = new Float32Array(w * h);
  for (let y = 0; y < h; y++) {
    for (let x = 0; x < w; x++) {
      let s = 0, n = 0;
      for (let k = -r; k <= r; k++) { const xx = x + k; if (xx >= 0 && xx < w) { s += src[y * w + xx]; n++; } }
      tmp[y * w + x] = s / n;
    }
  }
  for (let y = 0; y < h; y++) {
    for (let x = 0; x < w; x++) {
      let s = 0, n = 0;
      for (let k = -r; k <= r; k++) { const yy = y + k; if (yy >= 0 && yy < h) { s += tmp[yy * w + x]; n++; } }
      out[y * w + x] = s / n;
    }
  }
  return out;
}
function convexHull(pts) {
  pts.sort((a, b) => a[0] - b[0] || a[1] - b[1]);
  const cross = (o, a, b) => (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0]);
  const lower = [];
  for (const p of pts) {
    while (lower.length >= 2 && cross(lower[lower.length - 2], lower[lower.length - 1], p) <= 0) lower.pop();
    lower.push(p);
  }
  const upper = [];
  for (let i = pts.length - 1; i >= 0; i--) {
    const p = pts[i];
    while (upper.length >= 2 && cross(upper[upper.length - 2], upper[upper.length - 1], p) <= 0) upper.pop();
    upper.push(p);
  }
  upper.pop();
  lower.pop();
  return lower.concat(upper);
}
function triArea(a, b, c) { return Math.abs((b[0] - a[0]) * (c[1] - a[1]) - (c[0] - a[0]) * (b[1] - a[1])) / 2; }
function polyArea(p) {
  let s = 0;
  for (let i = 0; i < p.length; i++) { const a = p[i], b = p[(i + 1) % p.length]; s += a[0] * b[1] - b[0] * a[1]; }
  return Math.abs(s) / 2;
}
/** Reduziert die konvexe Hülle auf 4 Ecken (entfernt jeweils den Punkt mit dem kleinsten Flächenverlust). */
function hullToQuad(hull) {
  const p = hull.slice();
  while (p.length > 4) {
    let bi = 0, bv = Infinity;
    for (let i = 0; i < p.length; i++) {
      const v = triArea(p[(i - 1 + p.length) % p.length], p[i], p[(i + 1) % p.length]);
      if (v < bv) { bv = v; bi = i; }
    }
    p.splice(bi, 1);
  }
  return p;
}
/** Gerade durch Punkte (kleinste senkrechte Abstände): gibt Punkt und Richtung zurück. */
function fitLine(pts) {
  const n = pts.length;
  let mx = 0, my = 0;
  for (const [x, y] of pts) { mx += x; my += y; }
  mx /= n; my /= n;
  let sxx = 0, syy = 0, sxy = 0;
  for (const [x, y] of pts) { const dx = x - mx, dy = y - my; sxx += dx * dx; syy += dy * dy; sxy += dx * dy; }
  const ang = 0.5 * Math.atan2(2 * sxy, sxx - syy);
  return { p: [mx, my], d: [Math.cos(ang), Math.sin(ang)] };
}
function intersect(l1, l2) {
  const den = l1.d[0] * l2.d[1] - l1.d[1] * l2.d[0];
  if (Math.abs(den) < 1e-6) return null;
  const t = ((l2.p[0] - l1.p[0]) * l2.d[1] - (l2.p[1] - l1.p[1]) * l2.d[0]) / den;
  return [l1.p[0] + t * l1.d[0], l1.p[1] + t * l1.d[1]];
}
/**
 * Verfeinert die Ecken: Randpixel der Blattfläche werden den vier Kanten zugeordnet,
 * je Kante wird eine Gerade angepasst, die Ecken sind die Schnittpunkte.
 */
function refineByEdges(q, label, lab, w, h) {
  const edges = [[], [], [], []];
  const size = Math.sqrt(polyArea(q));
  const tol = Math.max(3, size * 0.04);
  const segs = [0, 1, 2, 3].map((i) => [q[i], q[(i + 1) % 4]]);
  for (let y = 1; y < h - 1; y++) {
    for (let x = 1; x < w - 1; x++) {
      const k = y * w + x;
      if (label[k] !== lab) continue;
      if (label[k - 1] === lab && label[k + 1] === lab && label[k - w] === lab && label[k + w] === lab) continue;
      let best = -1, bd = tol;
      for (let i = 0; i < 4; i++) {
        const [a, b] = segs[i];
        const vx = b[0] - a[0], vy = b[1] - a[1];
        const L2 = vx * vx + vy * vy;
        const t = ((x - a[0]) * vx + (y - a[1]) * vy) / L2;
        if (t < 0.12 || t > 0.88) continue; // Eckbereiche auslassen
        const dd = Math.abs((x - a[0]) * vy - (y - a[1]) * vx) / Math.sqrt(L2);
        if (dd < bd) { bd = dd; best = i; }
      }
      if (best >= 0) edges[best].push([x + 0.5, y + 0.5]);
    }
  }
  if (edges.some((e) => e.length < 8)) return null;
  const lines = edges.map(fitLine);
  const out = [];
  for (let i = 0; i < 4; i++) {
    const c = intersect(lines[(i + 3) % 4], lines[i]); // Ecke i liegt zwischen Kante i-1 und Kante i
    if (!c || Math.hypot(c[0] - q[i][0], c[1] - q[i][1]) > size * 0.08) return null;
    out.push(c);
  }
  return out;
}

/** Sortiert 4 Punkte als oben-links, oben-rechts, unten-rechts, unten-links. */
export function orderQuad(q) {
  const cx = q.reduce((s, p) => s + p[0], 0) / 4;
  const cy = q.reduce((s, p) => s + p[1], 0) / 4;
  const sorted = q.slice().sort((a, b) => Math.atan2(a[1] - cy, a[0] - cx) - Math.atan2(b[1] - cy, b[0] - cx));
  // atan2 aufsteigend im Bildkoordinatensystem (y nach unten) = im Uhrzeigersinn
  let start = 0, best = Infinity;
  sorted.forEach((p, i) => { const v = p[0] + p[1]; if (v < best) { best = v; start = i; } });
  return [0, 1, 2, 3].map((k) => sorted[(start + k) % 4]);
}
export function defaultQuad(w, h) {
  const m = Math.round(Math.min(w, h) * 0.04);
  return [[m, m], [w - m, m], [w - m, h - m], [m, h - m]];
}
/**
 * Sucht das helle Blatt im Foto. Gibt 4 Ecken in Bildkoordinaten zurück
 * oder null, wenn kein Blatt sicher erkannt wurde.
 */
export function detectQuad(canvas) {
  const W = canvas.width, H = canvas.height;
  const s = Math.min(1, 480 / Math.max(W, H));
  const w = Math.max(8, Math.round(W * s));
  const h = Math.max(8, Math.round(H * s));
  const c = document.createElement('canvas');
  c.width = w; c.height = h;
  const ctx = c.getContext('2d', { willReadFrequently: true });
  ctx.drawImage(canvas, 0, 0, w, h);
  const d = ctx.getImageData(0, 0, w, h).data;
  const g = new Float32Array(w * h);
  for (let i = 0, j = 0; i < g.length; i++, j += 4) g[i] = 0.299 * d[j] + 0.587 * d[j + 1] + 0.114 * d[j + 2];
  const b = boxBlur(g, w, h, 2);
  const hist = new Uint32Array(256);
  for (let i = 0; i < b.length; i++) hist[Math.min(255, b[i] | 0)]++;
  const thr = otsu(hist, b.length);
  const mask = new Uint8Array(w * h);
  for (let i = 0; i < b.length; i++) mask[i] = b[i] > thr ? 1 : 0;
  // größte zusammenhängende helle Fläche
  const label = new Int32Array(w * h).fill(-1);
  const queue = new Int32Array(w * h);
  let bestLabel = -1, bestSize = 0, cur = 0;
  for (let i = 0; i < mask.length; i++) {
    if (!mask[i] || label[i] !== -1) continue;
    let qh = 0, qt = 0;
    queue[qt++] = i;
    label[i] = cur;
    let size = 0;
    while (qh < qt) {
      const k = queue[qh++];
      size++;
      const x = k % w, y = (k - x) / w;
      if (x > 0 && mask[k - 1] && label[k - 1] === -1) { label[k - 1] = cur; queue[qt++] = k - 1; }
      if (x < w - 1 && mask[k + 1] && label[k + 1] === -1) { label[k + 1] = cur; queue[qt++] = k + 1; }
      if (y > 0 && mask[k - w] && label[k - w] === -1) { label[k - w] = cur; queue[qt++] = k - w; }
      if (y < h - 1 && mask[k + w] && label[k + w] === -1) { label[k + w] = cur; queue[qt++] = k + w; }
    }
    if (size > bestSize) { bestSize = size; bestLabel = cur; }
    cur++;
  }
  const frac = bestSize / (w * h);
  if (bestLabel < 0 || frac < 0.12 || frac > 0.97) return null;
  // Randpunkte sammeln (je Zeile äußerster linker/rechter Punkt reicht für die Hülle)
  const pts = [];
  for (let y = 0; y < h; y++) {
    let lx = -1, rx = -1;
    for (let x = 0; x < w; x++) if (label[y * w + x] === bestLabel) { if (lx < 0) lx = x; rx = x; }
    if (lx >= 0) { pts.push([lx, y]); if (rx !== lx) pts.push([rx, y]); }
  }
  if (pts.length < 4) return null;
  const hull = convexHull(pts);
  if (hull.length < 4) return null;
  let quad = hullToQuad(hull);
  const area = polyArea(quad);
  // Plausibilität: Viereck muss den Großteil der Fläche abdecken und darf nicht entartet sein
  if (area < 0.1 * w * h || area < 0.8 * bestSize) return null;
  quad = orderQuad(quad);
  const refined = refineByEdges(quad, label, bestLabel, w, h);
  if (refined) quad = refined;
  const ordered = quad.map(([x, y]) => [
    Math.min(W, Math.max(0, (x + 0.5) / s)),
    Math.min(H, Math.max(0, (y + 0.5) / s)),
  ]);
  return ordered;
}

// ------------------------------------------------------------------ Entzerrung
/** Homographie, die (0,0),(w,0),(w,h),(0,h) auf das Viereck q abbildet. */
function homography(w, h, q) {
  const src = [[0, 0], [w, 0], [w, h], [0, h]];
  const A = [];
  const B = [];
  for (let i = 0; i < 4; i++) {
    const [x, y] = src[i];
    const [u, v] = q[i];
    A.push([x, y, 1, 0, 0, 0, -u * x, -u * y]); B.push(u);
    A.push([0, 0, 0, x, y, 1, -v * x, -v * y]); B.push(v);
  }
  // Gauß-Elimination
  const n = 8;
  for (let col = 0; col < n; col++) {
    let piv = col;
    for (let r = col + 1; r < n; r++) if (Math.abs(A[r][col]) > Math.abs(A[piv][col])) piv = r;
    [A[col], A[piv]] = [A[piv], A[col]];
    [B[col], B[piv]] = [B[piv], B[col]];
    const p = A[col][col];
    if (Math.abs(p) < 1e-12) throw new Error('Ecken liegen auf einer Linie');
    for (let r = 0; r < n; r++) {
      if (r === col) continue;
      const f = A[r][col] / p;
      if (!f) continue;
      for (let k = col; k < n; k++) A[r][k] -= f * A[col][k];
      B[r] -= f * B[col];
    }
  }
  const hv = B.map((bv, i) => bv / A[i][i]);
  return [hv[0], hv[1], hv[2], hv[3], hv[4], hv[5], hv[6], hv[7], 1];
}
const dist = (a, b) => Math.hypot(a[0] - b[0], a[1] - b[1]);

/**
 * Berechnet Ausgabegröße und Seitenformat.
 * „Automatisch A4“: hoch oder quer nach Blattform; liegt das Seitenverhältnis
 * nahe an A4 (±10 %), wird exakt auf A4 entzerrt, sonst unverzerrt auf A4 eingepasst.
 */
/**
 * Echtes Seitenverhältnis (Breite/Höhe) eines fotografierten Rechtecks.
 * Verfahren nach Zhang (Whiteboard-Scanning): schätzt die Brennweite aus der Perspektive.
 * Liefert null, wenn die Schätzung unsicher ist.
 */
function trueAspect(q, imgW, imgH) {
  const u0 = imgW / 2, v0 = imgH / 2;
  const P = (p) => [p[0] - u0, p[1] - v0, 1];
  const m1 = P(q[0]), m2 = P(q[1]), m3 = P(q[3]), m4 = P(q[2]); // oben-links, oben-rechts, unten-links, unten-rechts
  const cross = (a, b) => [a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]];
  const dot = (a, b) => a[0] * b[0] + a[1] * b[1] + a[2] * b[2];
  const d2 = dot(cross(m2, m4), m3);
  const d3 = dot(cross(m3, m4), m2);
  if (Math.abs(d2) < 1e-9 || Math.abs(d3) < 1e-9) return null;
  const k2 = dot(cross(m1, m4), m3) / d2;
  const k3 = dot(cross(m1, m4), m2) / d3;
  const n2 = [k2 * m2[0] - m1[0], k2 * m2[1] - m1[1], k2 * m2[2] - m1[2]];
  const n3 = [k3 * m3[0] - m1[0], k3 * m3[1] - m1[1], k3 * m3[2] - m1[2]];
  const maxDim = Math.max(imgW, imgH);
  const nearlyParallel = Math.abs(n2[2]) < 1e-6 || Math.abs(n3[2]) < 1e-6 || Math.abs(k2 - 1) < 0.01 || Math.abs(k3 - 1) < 0.01;
  if (nearlyParallel) {
    const r = Math.sqrt((n2[0] ** 2 + n2[1] ** 2) / (n3[0] ** 2 + n3[1] ** 2));
    return Number.isFinite(r) && r > 0 ? r : null;
  }
  const f2 = -(n2[0] * n3[0] + n2[1] * n3[1]) / (n2[2] * n3[2]);
  if (!(f2 > 0)) return null;
  const f = Math.sqrt(f2);
  if (f < 0.3 * maxDim || f > 6 * maxDim) return null; // unplausible Brennweite
  const r = Math.sqrt(((n2[0] ** 2 + n2[1] ** 2) / f2 + n2[2] ** 2) / ((n3[0] ** 2 + n3[1] ** 2) / f2 + n3[2] ** 2));
  return Number.isFinite(r) && r > 0 ? r : null;
}

export function planOutput(q, imgW = 0, imgH = 0, maxLong = 2339) {
  let wEst = (dist(q[0], q[1]) + dist(q[3], q[2])) / 2;
  let hEst = (dist(q[0], q[3]) + dist(q[1], q[2])) / 2;
  const asp = imgW && imgH ? trueAspect(q, imgW, imgH) : null;
  if (asp) {
    // Größe beibehalten, Seitenverhältnis aus der Perspektive übernehmen
    const area = wEst * hEst;
    wEst = Math.sqrt(area * asp);
    hEst = Math.sqrt(area / asp);
  }
  const portrait = hEst >= wEst;
  let ratio = Math.max(wEst, hEst) / Math.max(1, Math.min(wEst, hEst)); // ≥ 1
  const snap = Math.abs(ratio - SQRT2) / SQRT2 < 0.15;
  if (snap) ratio = SQRT2;
  const long = Math.round(Math.min(maxLong, Math.max(1200, Math.max(wEst, hEst) * 1.15)));
  const short = Math.round(long / ratio);
  const outW = portrait ? short : long;
  const outH = portrait ? long : short;
  const page = portrait ? { w: A4.w, h: A4.h } : { w: A4.h, h: A4.w };
  return { outW, outH, page, snap };
}

/** Entzerrt das Viereck q aus src in ein Rechteck outW × outH (bilineare Abtastung). */
export function warp(src, q, outW, outH) {
  const sctx = src.getContext('2d', { willReadFrequently: true });
  const sw = src.width, sh = src.height;
  const sd = sctx.getImageData(0, 0, sw, sh).data;
  const out = document.createElement('canvas');
  out.width = outW; out.height = outH;
  const octx = out.getContext('2d');
  const img = octx.createImageData(outW, outH);
  const od = img.data;
  const M = homography(outW, outH, q);
  let o = 0;
  for (let y = 0; y < outH; y++) {
    const yy = y + 0.5;
    for (let x = 0; x < outW; x++, o += 4) {
      const xx = x + 0.5;
      const den = M[6] * xx + M[7] * yy + M[8];
      let u = (M[0] * xx + M[1] * yy + M[2]) / den - 0.5;
      let v = (M[3] * xx + M[4] * yy + M[5]) / den - 0.5;
      if (u < 0) u = 0; else if (u > sw - 1) u = sw - 1;
      if (v < 0) v = 0; else if (v > sh - 1) v = sh - 1;
      const x0 = u | 0, y0 = v | 0;
      const x1 = x0 + 1 < sw ? x0 + 1 : x0;
      const y1 = y0 + 1 < sh ? y0 + 1 : y0;
      const fx = u - x0, fy = v - y0;
      const i00 = (y0 * sw + x0) * 4, i10 = (y0 * sw + x1) * 4, i01 = (y1 * sw + x0) * 4, i11 = (y1 * sw + x1) * 4;
      for (let c = 0; c < 3; c++) {
        const a = sd[i00 + c] + (sd[i10 + c] - sd[i00 + c]) * fx;
        const b = sd[i01 + c] + (sd[i11 + c] - sd[i01 + c]) * fx;
        od[o + c] = a + (b - a) * fy;
      }
      od[o + 3] = 255;
    }
  }
  octx.putImageData(img, 0, 0);
  return out;
}

// ------------------------------------------------------------------ Filter
/** Lokaler Mittelwert über ein Integralbild (Fenstergröße 2r+1). */
function localMean(gray, w, h, r) {
  const W1 = w + 1;
  const integ = new Float64Array(W1 * (h + 1));
  for (let y = 0; y < h; y++) {
    let row = 0;
    for (let x = 0; x < w; x++) {
      row += gray[y * w + x];
      integ[(y + 1) * W1 + x + 1] = integ[y * W1 + x + 1] + row;
    }
  }
  const mean = new Float32Array(w * h);
  for (let y = 0; y < h; y++) {
    const y0 = Math.max(0, y - r), y1 = Math.min(h, y + r + 1);
    for (let x = 0; x < w; x++) {
      const x0 = Math.max(0, x - r), x1 = Math.min(w, x + r + 1);
      const s = integ[y1 * W1 + x1] - integ[y0 * W1 + x1] - integ[y1 * W1 + x0] + integ[y0 * W1 + x0];
      mean[y * w + x] = s / ((y1 - y0) * (x1 - x0));
    }
  }
  return mean;
}
/** Hintergrundhelligkeit schätzen: lokales Maximum-ähnliches Mittel der hellen Bereiche. */
function background(gray, w, h) {
  // Verkleinerte Karte: je Kachel das 90-%-Quantil, danach geglättet und hochskaliert
  const tile = Math.max(16, Math.round(Math.min(w, h) / 24));
  const tw = Math.ceil(w / tile), th = Math.ceil(h / tile);
  const small = new Float32Array(tw * th);
  const buf = [];
  for (let ty = 0; ty < th; ty++) {
    for (let tx = 0; tx < tw; tx++) {
      buf.length = 0;
      const step = Math.max(1, Math.floor(tile / 8));
      for (let y = ty * tile; y < Math.min(h, (ty + 1) * tile); y += step) {
        for (let x = tx * tile; x < Math.min(w, (tx + 1) * tile); x += step) buf.push(gray[y * w + x]);
      }
      buf.sort((a, b) => a - b);
      small[ty * tw + tx] = buf.length ? buf[Math.floor(buf.length * 0.9)] : 255;
    }
  }
  const sm = boxBlur(small, tw, th, 1);
  const bg = new Float32Array(w * h);
  for (let y = 0; y < h; y++) {
    const fy = Math.min(th - 1, Math.max(0, (y + 0.5) / tile - 0.5));
    const y0 = Math.floor(fy), y1 = Math.min(th - 1, y0 + 1), ay = fy - y0;
    for (let x = 0; x < w; x++) {
      const fx = Math.min(tw - 1, Math.max(0, (x + 0.5) / tile - 0.5));
      const x0 = Math.floor(fx), x1 = Math.min(tw - 1, x0 + 1), ax = fx - x0;
      const a = sm[y0 * tw + x0] + (sm[y0 * tw + x1] - sm[y0 * tw + x0]) * ax;
      const b = sm[y1 * tw + x0] + (sm[y1 * tw + x1] - sm[y1 * tw + x0]) * ax;
      bg[y * w + x] = Math.max(40, a + (b - a) * ay);
    }
  }
  return bg;
}
/**
 * Wendet einen Lesbarkeits-Filter an:
 * 'bw'    – Dokument Schwarz/Weiß (Schatten und Grauschleier verschwinden)
 * 'gray'  – Graustufen, Hintergrund aufgehellt
 * 'color' – Farbe, Hintergrund aufgehellt
 */
export function applyFilter(canvas, mode) {
  const w = canvas.width, h = canvas.height;
  const ctx = canvas.getContext('2d', { willReadFrequently: true });
  const img = ctx.getImageData(0, 0, w, h);
  const d = img.data;
  const n = w * h;
  const gray = new Float32Array(n);
  for (let i = 0, j = 0; i < n; i++, j += 4) gray[i] = 0.299 * d[j] + 0.587 * d[j + 1] + 0.114 * d[j + 2];
  const bg = background(gray, w, h);
  if (mode === 'bw') {
    const r = Math.max(7, Math.round(Math.min(w, h) / 60));
    const mean = localMean(gray, w, h, r);
    for (let i = 0, j = 0; i < n; i++, j += 4) {
      const norm = gray[i] / bg[i]; // 1 = Papier
      const loc = mean[i] / bg[i];
      const ink = norm < 0.6 || (norm < loc - 0.1 && norm < 0.85);
      const v = ink ? 0 : 255;
      d[j] = d[j + 1] = d[j + 2] = v;
    }
  } else if (mode === 'gray') {
    for (let i = 0, j = 0; i < n; i++, j += 4) {
      let v = (gray[i] / bg[i] - 0.2) / 0.72;
      v = v < 0 ? 0 : v > 1 ? 1 : v;
      v = Math.pow(v, 1.4) * 255;
      d[j] = d[j + 1] = d[j + 2] = v;
    }
  } else {
    for (let i = 0, j = 0; i < n; i++, j += 4) {
      const gain = 245 / bg[i];
      for (let c = 0; c < 3; c++) {
        let v = d[j + c] * gain;
        v = (v - 25) * 1.1;
        d[j + c] = v < 0 ? 0 : v > 255 ? 255 : v;
      }
    }
  }
  ctx.putImageData(img, 0, 0);
  return canvas;
}

/** Canvas als Bilddaten für die PDF: S/W als PNG (scharf, klein), sonst JPEG. */
export function encodeCanvas(canvas, mode) {
  const type = mode === 'bw' ? 'image/png' : 'image/jpeg';
  return new Promise((resolve, reject) => {
    canvas.toBlob((b) => {
      if (!b) { reject(new Error('Bild konnte nicht erzeugt werden')); return; }
      b.arrayBuffer().then((buf) => resolve({ bytes: new Uint8Array(buf), type }), reject);
    }, type, 0.82);
  });
}
