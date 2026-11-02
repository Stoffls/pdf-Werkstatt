// PDF Werkstatt – Messen: reine Rechenfunktionen (ohne Bedienoberfläche)
// Einheiten: PDF-Koordinaten in pt (1 pt = 25,4/72 mm auf dem Papier), echte Längen in mm.

export const PT_MM = 25.4 / 72;
export const A4 = { w: 595.28, h: 841.89 };

const PAPERS = [
  ['A0', 841, 1189], ['A1', 594, 841], ['A2', 420, 594], ['A3', 297, 420], ['A4', 210, 297], ['A5', 148, 210],
];

/** Verkleinerungsfaktor beim Druck „an Seite anpassen“ auf A4 (hoch oder quer, je nachdem was besser passt). Kleinere Seiten: 1. */
export function a4Factor(w, h) {
  const f = Math.max(Math.min(A4.w / w, A4.h / h), Math.min(A4.w / h, A4.h / w));
  return f >= 0.999 ? 1 : f;
}

/** Papierformat-Name, z. B. „A3 quer (420 × 297 mm)“ */
export function paperName(w, h) {
  const wm = w * PT_MM, hm = h * PT_MM;
  const size = `${Math.round(wm)} × ${Math.round(hm)} mm`;
  for (const [name, a, b] of PAPERS) {
    const tol = 0.03;
    if (Math.abs(wm - a) / a < tol && Math.abs(hm - b) / b < tol) return `${name} hoch (${size})`;
    if (Math.abs(wm - b) / b < tol && Math.abs(hm - a) / a < tol) return `${name} quer (${size})`;
  }
  return size;
}

/** Zahl deutsch formatiert: 1.234,56 */
export function fmtNum(v, dec = 2) {
  const neg = v < 0;
  const [i, d] = Math.abs(v).toFixed(dec).split('.');
  const grouped = i.replace(/\B(?=(\d{3})+(?!\d))/g, '.');
  return (neg && Number(v.toFixed(dec)) !== 0 ? '-' : '') + grouped + (d ? ',' + d : '');
}
export function fmtLen(mm, unit) {
  return unit === 'cm' ? `${fmtNum(mm / 10)} cm` : `${fmtNum(mm / 1000)} m`;
}
export function fmtArea(mm2, unit) {
  return unit === 'cm' ? `${fmtNum(mm2 / 100)} cm²` : `${fmtNum(mm2 / 1e6)} m²`;
}

/** Maßstabszahl N (1:N) aus mm je pt */
export function scaleN(mmPerPt) { return mmPerPt / PT_MM; }

/** Eingabe wie „100“, „1:100“, „1 : 50“ → 100 bzw. null */
export function parseScale(str) {
  const s = String(str || '').trim().replace(/\s+/g, '').replace(',', '.');
  const m = s.match(/^(?:1:)?(\d+(?:\.\d+)?)$/);
  if (!m) return null;
  const n = Number(m[1]);
  return n >= 1 && n <= 100000 ? n : null;
}
/** Zahleneingabe mit Komma oder Punkt → Zahl oder null */
export function parseNum(str) {
  const s = String(str || '').trim().replace(/\s+/g, '').replace(/\.(?=\d{3}(\D|$))/g, '').replace(',', '.');
  if (!/^\d*\.?\d+$/.test(s)) return null;
  const n = Number(s);
  return n > 0 && Number.isFinite(n) ? n : null;
}

export const dist = (a, b) => Math.hypot(a[0] - b[0], a[1] - b[1]);
export function polyLen(pts, closed = false) {
  let s = 0;
  for (let i = 1; i < pts.length; i++) s += dist(pts[i - 1], pts[i]);
  if (closed && pts.length > 2) s += dist(pts[pts.length - 1], pts[0]);
  return s;
}
export function polyArea(pts) {
  let s = 0;
  for (let i = 0; i < pts.length; i++) { const a = pts[i], b = pts[(i + 1) % pts.length]; s += a[0] * b[1] - b[0] * a[1]; }
  return Math.abs(s) / 2;
}
export function centroid(pts) {
  let a = 0, cx = 0, cy = 0;
  for (let i = 0; i < pts.length; i++) {
    const p = pts[i], q = pts[(i + 1) % pts.length];
    const c = p[0] * q[1] - q[0] * p[1];
    a += c; cx += (p[0] + q[0]) * c; cy += (p[1] + q[1]) * c;
  }
  if (Math.abs(a) < 1e-9) {
    const n = pts.length;
    return [pts.reduce((s, p) => s + p[0], 0) / n, pts.reduce((s, p) => s + p[1], 0) / n];
  }
  return [cx / (3 * a), cy / (3 * a)];
}
/** Winkel bei v zwischen a und b in Grad (0–180) */
export function angleDeg(a, v, b) {
  const ax = a[0] - v[0], ay = a[1] - v[1], bx = b[0] - v[0], by = b[1] - v[1];
  const la = Math.hypot(ax, ay), lb = Math.hypot(bx, by);
  if (la < 1e-9 || lb < 1e-9) return null;
  const c = Math.max(-1, Math.min(1, (ax * bx + ay * by) / (la * lb)));
  return (Math.acos(c) * 180) / Math.PI;
}
/** Kreis durch drei Punkte → {c, r} oder null (Punkte auf einer Linie) */
export function circle3(p1, p2, p3) {
  const [ax, ay] = p1, [bx, by] = p2, [cx, cy] = p3;
  const d = 2 * (ax * (by - cy) + bx * (cy - ay) + cx * (ay - by));
  const scale = Math.max(dist(p1, p2), dist(p2, p3), dist(p1, p3));
  if (scale < 1e-9 || Math.abs(d) < 1e-6 * scale * scale) return null;
  const a2 = ax * ax + ay * ay, b2 = bx * bx + by * by, c2 = cx * cx + cy * cy;
  const ux = (a2 * (by - cy) + b2 * (cy - ay) + c2 * (ay - by)) / d;
  const uy = (a2 * (cx - bx) + b2 * (ax - cx) + c2 * (bx - ax)) / d;
  return { c: [ux, uy], r: dist([ux, uy], p1) };
}

/** Wie viele Punkte braucht eine Messart (0 = beliebig viele, mit „Fertig“) */
export const NEED = { len: 2, angle: 3, radius: 3, area: 0, ref: 2 };

/**
 * Beschriftung einer Messung. cal = {mmPerPt} oder null.
 * Gibt {lines, contents, missing} zurück; missing = Maßstab fehlt.
 */
export function measText(kind, pts, cal, unit, f = 1) {
  const k = cal && cal.mmPerPt > 0 ? cal.mmPerPt : null;
  switch (kind) {
    case 'len': {
      if (!k) return { lines: ['Maßstab fehlt'], contents: 'Länge (Maßstab fehlt)', missing: true };
      const t = fmtLen(polyLen(pts) * k, unit);
      return { lines: [t], contents: `Länge ${t}` };
    }
    case 'area': {
      if (!k) return { lines: ['Maßstab fehlt'], contents: 'Fläche (Maßstab fehlt)', missing: true };
      const a = fmtArea(polyArea(pts) * k * k, unit);
      const u = fmtLen(polyLen(pts, true) * k, unit);
      return { lines: [`A = ${a}`, `U = ${u}`], contents: `Fläche ${a}, Umfang ${u}` };
    }
    case 'angle': {
      const d = angleDeg(pts[0], pts[1], pts[2]);
      const t = d == null ? '–' : `${fmtNum(d)}°`;
      return { lines: [t], contents: `Winkel ${t}` };
    }
    case 'radius': {
      const c = circle3(pts[0], pts[1], pts[2]);
      if (!c) return { lines: ['Punkte auf einer Linie'], contents: 'Radius (ungültig)', missing: true };
      if (!k) return { lines: ['Maßstab fehlt'], contents: 'Radius (Maßstab fehlt)', missing: true };
      const t = fmtLen(c.r * k, unit);
      return { lines: [`R = ${t}`], contents: `Radius ${t}` };
    }
    case 'scale': {
      if (!k) return { lines: ['Maßstab fehlt'], contents: 'Maßstab fehlt', missing: true };
      const n = Math.round(scaleN(k));
      const lines = [`M 1:${n}`];
      if (f < 1) lines.push(`Druck auf A4: M 1:${Math.round(n / f)}`);
      return { lines, contents: lines.join(', ') };
    }
    default:
      return { lines: [], contents: '' };
  }
}

/** Länge des Maßstabsbalkens: runder Wert, der im A4-Druck etwa 30–60 mm lang ist. */
export function barLength(mmPerPt, f) {
  const steps = [100, 200, 500, 1000, 2000, 5000, 10000, 20000, 50000, 100000, 200000, 500000];
  let best = steps[0];
  for (const mm of steps) {
    const printedMm = (mm / mmPerPt) * f * PT_MM;
    best = mm;
    if (printedMm >= 30) break;
  }
  return best; // echte Länge in mm
}
