// PDF Werkstatt – Stufe 1
// Ansehen, Text kopieren, Markieren, Stift, Textfeld, Notiz, Seiten verwalten, Speichern.
// Alles läuft im Browser; Dateien verlassen das Gerät nicht.

import * as pdfjsLib from './lib/pdf.min.js';

const {
  PDFDocument, StandardFonts, PDFName, PDFString, PDFHexString, PDFArray, PDFDict, degrees,
} = window.PDFLib;

const TARGET = window.__PDFW_TARGET || 'github';
const BUILD = window.__PDFW_BUILD || '';
const BASE = new URL('./', location.href).href;

pdfjsLib.GlobalWorkerOptions.workerSrc = new URL('lib/pdf.worker.js', BASE).href;
const DOC_OPTS = {
  standardFontDataUrl: new URL('lib/standard_fonts/', BASE).href,
  wasmUrl: new URL('lib/wasm/', BASE).href,
  iccUrl: new URL('lib/iccs/', BASE).href,
  isEvalSupported: false,
  enableXfa: false,
};

// ---------------------------------------------------------------- constants
const PALETTES = {
  hl: [['Gelb', '#ffe14d'], ['Grün', '#8be07f'], ['Blau', '#86ccff'], ['Rosa', '#ff9ccc'], ['Orange', '#ffb466'], ['Rot', '#ff8f86']],
  ink: [['Schwarz', '#1b1b1b'], ['Rot', '#d92121'], ['Blau', '#1f5fd6'], ['Grün', '#178a3c'], ['Orange', '#e8590c'], ['Violett', '#7b3fc4']],
  note: [['Gelb', '#ffd43b'], ['Grün', '#69db7c'], ['Blau', '#74c0fc'], ['Rosa', '#f783ac'], ['Orange', '#ffa94d']],
};
PALETTES.text = PALETTES.ink;
const INK_WIDTHS = [['Fein', 1], ['Mittel', 2], ['Dick', 4]];
const TEXT_SIZES = [10, 12, 16, 20];
const NOTE_SIZE = 20; // Kantenlänge des Notiz-Symbols in pt
const MIN_ZOOM = 0.25;
const MAX_ZOOM = 6;
const MAX_CANVAS_PX = 8_000_000; // iOS-Speichergrenze für Canvas beachten
const SEL_COLOR = '#1f6feb';
const ANNOT_KEY = 'StofflAnno'; // eigener Schlüssel: macht unsere Anmerkungen beim Wiederöffnen bearbeitbar

// ---------------------------------------------------------------- helpers
const $ = (s, r = document) => r.querySelector(s);
const $$ = (s, r = document) => [...r.querySelectorAll(s)];
const uid = () => Math.random().toString(36).slice(2, 10) + Date.now().toString(36).slice(-4);
const clamp = (v, a, b) => Math.min(b, Math.max(a, v));
const r2 = (n) => Math.round(n * 100) / 100;
const pdfNum = (n) => String(Math.round(n * 1000) / 1000);
const norm360 = (d) => ((Math.round(d / 90) * 90) % 360 + 360) % 360;
const pad2 = (n) => String(n).padStart(2, '0');
const todayStamp = () => { const d = new Date(); return `${d.getFullYear()}_${pad2(d.getMonth() + 1)}_${pad2(d.getDate())}`; };
const pdfDate = () => { const d = new Date(); return `D:${d.getFullYear()}${pad2(d.getMonth() + 1)}${pad2(d.getDate())}${pad2(d.getHours())}${pad2(d.getMinutes())}${pad2(d.getSeconds())}`; };
const hexRgb = (hex) => [1, 3, 5].map((i) => parseInt(hex.slice(i, i + 2), 16) / 255);
const rgbOp = (hex) => hexRgb(hex).map(pdfNum).join(' ');
const fmtSize = (b) => (b < 1024 * 1024 ? `${Math.max(1, Math.round(b / 1024))} KB` : `${(b / 1024 / 1024).toFixed(1).replace('.', ',')} MB`);
const SVGNS = 'http://www.w3.org/2000/svg';
function svg(tag, attrs = {}, parent) {
  const el = document.createElementNS(SVGNS, tag);
  for (const k in attrs) el.setAttribute(k, attrs[k]);
  if (parent) parent.appendChild(el);
  return el;
}
class UserError extends Error {}
class Cancelled extends Error {}

// Richtung „rechts“ und „unten“ der Ansicht im PDF-Koordinatensystem bei Drehung rc
const FRAMES = {
  0: { right: [1, 0], down: [0, -1] },
  90: { right: [0, 1], down: [1, 0] },
  180: { right: [-1, 0], down: [0, 1] },
  270: { right: [0, -1], down: [-1, 0] },
};

// ---------------------------------------------------------------- state
const S = {
  pages: [], // {uid, src, idx, rot, annots:[]}
  fileName: '',
  dirty: false,
  tool: 'read',
  zoom: 1,
  sel: null, // {uid, id}
  gridSel: new Set(),
  opts: loadOpts(),
};
const sources = new Map(); // id -> {id, name, bytes, pdf, lib, libError, proxies}
const H = { undo: [], redo: [] };
let helvMeasure = null; // pdf-lib Helvetica nur zum Messen von Textbreiten
const charOk = new Map();

function loadOpts() {
  const def = {
    hl: { color: PALETTES.hl[0][1] },
    ink: { color: PALETTES.ink[1][1], w: 2 },
    text: { color: PALETTES.text[0][1], size: 12, bg: false },
    note: { color: PALETTES.note[0][1] },
  };
  try {
    const o = JSON.parse(localStorage.getItem('pdfw-opts') || 'null');
    if (o && typeof o === 'object') {
      for (const k of Object.keys(def)) if (o[k] && typeof o[k] === 'object') Object.assign(def[k], o[k]);
    }
  } catch { /* ohne Speicher weiterarbeiten */ }
  return def;
}
function saveOpts() { try { localStorage.setItem('pdfw-opts', JSON.stringify(S.opts)); } catch { /* egal */ } }

// ---------------------------------------------------------------- UI basics
let toastTimer = 0;
function toast(msg, ms = 2800) {
  const t = $('#toast');
  t.textContent = msg;
  t.classList.add('show');
  clearTimeout(toastTimer);
  toastTimer = setTimeout(() => t.classList.remove('show'), ms);
}
let busyDepth = 0;
function busy(text) { busyDepth++; $('#busyText').textContent = text; $('#busy').hidden = false; }
function unbusy() { busyDepth = Math.max(0, busyDepth - 1); if (!busyDepth) $('#busy').hidden = true; }

let modalOpen = 0;
/** Eigener Dialog (alert/confirm/prompt sind in manchen Umgebungen gesperrt). */
function modal({ title, text, content, buttons, stack = false, onOpen }) {
  return new Promise((resolve) => {
    modalOpen++;
    const scrim = document.createElement('div');
    scrim.className = 'scrim';
    const box = document.createElement('div');
    box.className = 'modal';
    box.setAttribute('role', 'dialog');
    box.setAttribute('aria-modal', 'true');
    if (title) { const h = document.createElement('h2'); h.textContent = title; box.appendChild(h); }
    if (text) { const p = document.createElement('p'); p.textContent = text; box.appendChild(p); }
    if (content) box.appendChild(content);
    const row = document.createElement('div');
    row.className = 'mrow' + (stack ? ' stack' : '');
    let done = false;
    const close = (val) => {
      if (done) return;
      done = true;
      modalOpen--;
      document.removeEventListener('keydown', onKey, true);
      scrim.remove();
      resolve(val);
    };
    for (const b of buttons) {
      const btn = document.createElement('button');
      btn.type = 'button';
      btn.className = 'btn' + (b.kind ? ' ' + b.kind : '');
      btn.textContent = b.label;
      btn.addEventListener('click', () => close(typeof b.value === 'function' ? b.value() : b.value));
      row.appendChild(btn);
    }
    box.appendChild(row);
    scrim.appendChild(box);
    scrim.addEventListener('pointerdown', (e) => { if (e.target === scrim) close(null); });
    const onKey = (e) => {
      if (e.key === 'Escape') { e.preventDefault(); close(null); }
      if (e.key === 'Enter' && (e.metaKey || e.ctrlKey)) {
        const prim = buttons.find((b) => b.kind === 'primary');
        if (prim) { e.preventDefault(); close(typeof prim.value === 'function' ? prim.value() : prim.value); }
      }
    };
    document.addEventListener('keydown', onKey, true);
    document.body.appendChild(scrim);
    if (onOpen) onOpen(box, close);
  });
}
function errorDialog(err) {
  if (!(err instanceof UserError)) console.error(err);
  const msg = err instanceof UserError ? err.message
    : 'Das hat nicht geklappt. Bitte versuche es noch einmal. Falls der Fehler bleibt, schick mir die Meldung: ' + (err?.message || String(err));
  return modal({ title: 'Hinweis', text: msg, buttons: [{ label: 'OK', value: true, kind: 'primary' }] });
}

// ---------------------------------------------------------------- storage (IndexedDB)
const idb = {
  db: null,
  failed: false,
  open() {
    if (this.db || this.failed) return Promise.resolve(this.db);
    return new Promise((resolve) => {
      try {
        const req = indexedDB.open('pdf-werkstatt', 1);
        req.onupgradeneeded = () => {
          const db = req.result;
          if (!db.objectStoreNames.contains('sources')) db.createObjectStore('sources', { keyPath: 'id' });
          if (!db.objectStoreNames.contains('state')) db.createObjectStore('state');
        };
        req.onsuccess = () => { this.db = req.result; resolve(this.db); };
        req.onerror = () => { this.failed = true; resolve(null); };
        req.onblocked = () => { this.failed = true; resolve(null); };
      } catch { this.failed = true; resolve(null); }
    });
  },
  async run(store, mode, fn) {
    const db = await this.open();
    if (!db) return undefined;
    return new Promise((resolve) => {
      try {
        const tx = db.transaction(store, mode);
        const req = fn(tx.objectStore(store));
        tx.oncomplete = () => resolve(req ? req.result : true);
        tx.onerror = () => resolve(undefined);
        tx.onabort = () => resolve(undefined);
      } catch { resolve(undefined); }
    });
  },
  put(store, val, key) { return this.run(store, 'readwrite', (s) => (key === undefined ? s.put(val) : s.put(val, key))); },
  get(store, key) { return this.run(store, 'readonly', (s) => s.get(key)); },
  del(store, key) { return this.run(store, 'readwrite', (s) => s.delete(key)); },
  clear(store) { return this.run(store, 'readwrite', (s) => s.clear()); },
};
let persistTimer = 0;
function persistSoon() {
  clearTimeout(persistTimer);
  persistTimer = setTimeout(persistNow, 600);
}
function persistNow() {
  clearTimeout(persistTimer);
  if (!S.pages.length) return Promise.resolve();
  return idb.put('state', {
    pages: S.pages,
    fileName: S.fileName,
    dirty: S.dirty,
    savedAt: Date.now(),
    sourceIds: [...new Set(S.pages.map((p) => p.src))],
  }, 'session');
}

// ---------------------------------------------------------------- history
function snapshot() { return structuredClone(S.pages); }
function checkpoint() {
  H.undo.push(snapshot());
  if (H.undo.length > 100) H.undo.shift();
  H.redo.length = 0;
  updateChrome();
}
function undo() {
  if (!H.undo.length) return;
  H.redo.push(snapshot());
  restoreSnapshot(H.undo.pop());
}
function redo() {
  if (!H.redo.length) return;
  H.undo.push(snapshot());
  restoreSnapshot(H.redo.pop());
}
function restoreSnapshot(pages) {
  S.pages = pages;
  S.sel = null;
  S.gridSel = new Set([...S.gridSel].filter((u) => pages.some((p) => p.uid === u)));
  changed({ structure: true });
}
/** Nach jeder Änderung: neu zeichnen, merken, als ungespeichert markieren. */
function changed({ structure = false, uidOnly = null } = {}) {
  S.dirty = true;
  if (structure) {
    if (S.tool === 'pages') { renderGrid(); needLayout = true; } else layout();
  } else if (uidOnly) {
    const el = pageEl(uidOnly);
    if (el) drawAnnots(el);
  } else {
    for (const el of pagesEl.children) drawAnnots(el);
  }
  updateChrome();
  persistSoon();
}

// ---------------------------------------------------------------- text helpers
function canEncodeChar(ch) {
  if (charOk.has(ch)) return charOk.get(ch);
  let ok = true;
  try { helvMeasure.encodeText(ch); helvMeasure.widthOfTextAtSize(ch, 10); } catch { ok = false; }
  charOk.set(ch, ok);
  return ok;
}
/** Helvetica (Standard-PDF-Schrift) kennt nur westeuropäische Zeichen; Rest wird ersetzt. */
function sanitizeText(str) {
  let replaced = false;
  let out = '';
  for (const ch of str.replace(/\r\n?/g, '\n').replace(/\t/g, '    ')) {
    if (ch === '\n' || canEncodeChar(ch)) out += ch;
    else { out += '?'; replaced = true; }
  }
  return { text: out, replaced };
}
function measure(line, fs) {
  try { return helvMeasure.widthOfTextAtSize(line, fs); } catch { return line.length * fs * 0.55; }
}
function textLayout(a) {
  const fs = a.size;
  const lines = a.text.split('\n');
  const pad = fs * 0.35;
  const lh = fs * 1.2;
  const asc = fs * 0.718;
  let w = 0;
  for (const l of lines) w = Math.max(w, measure(l, fs));
  w = Math.max(w + 2 * pad, fs);
  const h = 2 * pad + (lines.length - 1) * lh + fs * 0.93;
  return { lines, w, h, pad, lh, asc, fs };
}
/** Lokales Textfeld-Koordinatensystem (u nach rechts, v nach unten) → PDF-Koordinaten */
function textMatrix(a) {
  const { right, down } = FRAMES[a.rc] || FRAMES[0];
  return [right[0], right[1], down[0], down[1], a.x, a.y];
}
function textCorners(a, L) {
  const [ax, ay, cx, cy, e, f] = textMatrix(a);
  return [[0, 0], [L.w, 0], [L.w, L.h], [0, L.h]].map(([u, v]) => [ax * u + cx * v + e, ay * u + cy * v + f]);
}

// ---------------------------------------------------------------- annotation model
function cleanAnnot(a) {
  if (!a || typeof a !== 'object') return null;
  const num = (v) => typeof v === 'number' && Number.isFinite(v);
  const color = typeof a.color === 'string' && /^#[0-9a-f]{6}$/i.test(a.color) ? a.color.toLowerCase() : '#000000';
  const id = typeof a.id === 'string' && a.id ? a.id : uid();
  switch (a.type) {
    case 'hl':
      if (!Array.isArray(a.rect) || a.rect.length !== 4 || !a.rect.every(num)) return null;
      return { id, type: 'hl', color, rect: normRect(a.rect) };
    case 'ink':
      if (!Array.isArray(a.pts) || !a.pts.length || !a.pts.every((p) => Array.isArray(p) && p.length === 2 && num(p[0]) && num(p[1]))) return null;
      return { id, type: 'ink', color, w: num(a.w) && a.w > 0 ? a.w : 2, pts: a.pts.map((p) => [p[0], p[1]]) };
    case 'text':
      if (!num(a.x) || !num(a.y) || typeof a.text !== 'string' || !a.text) return null;
      return { id, type: 'text', color, x: a.x, y: a.y, text: a.text, size: num(a.size) ? clamp(a.size, 4, 96) : 12, rc: norm360(num(a.rc) ? a.rc : 0), bg: !!a.bg };
    case 'note':
      if (!num(a.x) || !num(a.y) || typeof a.text !== 'string') return null;
      return { id, type: 'note', color, x: a.x, y: a.y, text: a.text };
    default:
      return null;
  }
}
function normRect([a, b, c, d]) { return [Math.min(a, c), Math.min(b, d), Math.max(a, c), Math.max(b, d)]; }
function moveAnnot(a, dx, dy) {
  switch (a.type) {
    case 'hl': return { ...a, rect: [a.rect[0] + dx, a.rect[1] + dy, a.rect[2] + dx, a.rect[3] + dy].map(r2) };
    case 'ink': return { ...a, pts: a.pts.map(([x, y]) => [r2(x + dx), r2(y + dy)]) };
    default: return { ...a, x: r2(a.x + dx), y: r2(a.y + dy) };
  }
}
function annotBounds(a) {
  switch (a.type) {
    case 'hl': return a.rect;
    case 'ink': {
      let x1 = Infinity, y1 = Infinity, x2 = -Infinity, y2 = -Infinity;
      for (const [x, y] of a.pts) { x1 = Math.min(x1, x); y1 = Math.min(y1, y); x2 = Math.max(x2, x); y2 = Math.max(y2, y); }
      const m = a.w / 2 + 1;
      return [x1 - m, y1 - m, x2 + m, y2 + m];
    }
    case 'text': {
      const c = textCorners(a, textLayout(a));
      const xs = c.map((p) => p[0]); const ys = c.map((p) => p[1]);
      return [Math.min(...xs), Math.min(...ys), Math.max(...xs), Math.max(...ys)];
    }
    case 'note': { const h = NOTE_SIZE / 2; return [a.x - h, a.y - h, a.x + h, a.y + h]; }
    default: return [0, 0, 0, 0];
  }
}
function distSeg(px, py, ax, ay, bx, by) {
  const dx = bx - ax, dy = by - ay;
  const l2 = dx * dx + dy * dy;
  let t = l2 ? ((px - ax) * dx + (py - ay) * dy) / l2 : 0;
  t = clamp(t, 0, 1);
  return Math.hypot(px - (ax + t * dx), py - (ay + t * dy));
}
function hitAnnot(p, [x, y], tol) {
  for (let i = p.annots.length - 1; i >= 0; i--) {
    const a = p.annots[i];
    if (a.type === 'hl') {
      const [x1, y1, x2, y2] = a.rect;
      if (x >= x1 - tol && x <= x2 + tol && y >= y1 - tol && y <= y2 + tol) return a;
    } else if (a.type === 'ink') {
      const lim = a.w / 2 + tol;
      if (a.pts.length === 1 && Math.hypot(x - a.pts[0][0], y - a.pts[0][1]) <= lim) return a;
      for (let k = 1; k < a.pts.length; k++) {
        if (distSeg(x, y, a.pts[k - 1][0], a.pts[k - 1][1], a.pts[k][0], a.pts[k][1]) <= lim) return a;
      }
    } else if (a.type === 'text') {
      const L = textLayout(a);
      const { right, down } = FRAMES[a.rc] || FRAMES[0];
      const u = (x - a.x) * right[0] + (y - a.y) * right[1];
      const v = (x - a.x) * down[0] + (y - a.y) * down[1];
      if (u >= -tol && u <= L.w + tol && v >= -tol && v <= L.h + tol) return a;
    } else if (a.type === 'note') {
      if (Math.abs(x - a.x) <= NOTE_SIZE / 2 + tol && Math.abs(y - a.y) <= NOTE_SIZE / 2 + tol) return a;
    }
  }
  return null;
}

// ---------------------------------------------------------------- loading
function looksLikePdf(bytes) {
  const head = new TextDecoder('latin1').decode(bytes.subarray(0, Math.min(bytes.length, 1024)));
  return head.includes('%PDF-');
}
async function askPassword(name, wrong) {
  const input = document.createElement('input');
  input.type = 'password';
  input.autocomplete = 'off';
  input.id = 'pwInput';
  const res = await modal({
    title: wrong ? 'Passwort falsch' : 'Passwort erforderlich',
    text: `„${name}“ ist mit einem Passwort geschützt.`,
    content: input,
    buttons: [{ label: 'Abbrechen', value: null }, { label: 'Öffnen', value: () => input.value, kind: 'primary' }],
    onOpen: () => input.focus(),
  });
  return res;
}
async function openPdfjs(bytes, name) {
  let password;
  let wrong = false;
  for (;;) {
    const task = pdfjsLib.getDocument({ ...DOC_OPTS, data: bytes.slice(), password });
    try {
      return await task.promise;
    } catch (e) {
      if (e && e.name === 'PasswordException') {
        password = await askPassword(name, wrong);
        if (password == null) throw new Cancelled();
        wrong = true;
        continue;
      }
      throw new UserError(`„${name}“ lässt sich nicht öffnen. Die Datei ist beschädigt oder keine gültige PDF.`);
    }
  }
}
/** Liest unsere eigenen Anmerkungen aus und entfernt sie aus der Datei, damit sie bearbeitbar bleiben. */
function extractOwnAnnots(lib) {
  const found = new Map();
  const key = PDFName.of(ANNOT_KEY);
  lib.getPages().forEach((page, idx) => {
    const annots = page.node.lookupMaybe(PDFName.of('Annots'), PDFArray);
    if (!annots) return;
    const keep = [];
    const mine = [];
    for (let i = 0; i < annots.size(); i++) {
      const raw = annots.get(i);
      const dict = lib.context.lookup(raw);
      let data;
      if (dict instanceof PDFDict) data = dict.get(key);
      if (data instanceof PDFHexString || data instanceof PDFString) {
        try {
          const a = cleanAnnot(JSON.parse(data.decodeText()));
          if (a) { mine.push(a); continue; }
        } catch { /* fremde oder kaputte Daten: Anmerkung bleibt unverändert */ }
      }
      keep.push(raw);
    }
    if (mine.length) {
      found.set(idx, mine);
      if (keep.length) page.node.set(PDFName.of('Annots'), lib.context.obj(keep));
      else page.node.delete(PDFName.of('Annots'));
    }
  });
  return found;
}
async function loadSource(name, rawBytes, { id = uid(), persist = true } = {}) {
  let lib = null;
  let libError = null;
  let bytes = rawBytes;
  let extracted = new Map();
  try {
    lib = await PDFDocument.load(rawBytes, { updateMetadata: false });
    extracted = extractOwnAnnots(lib);
    if (extracted.size) bytes = await lib.save({ useObjectStreams: false, updateFieldAppearances: false });
  } catch (e) {
    lib = null;
    libError = /encrypt/i.test(e?.name || '') || /encrypt/i.test(e?.message || '') ? 'encrypted' : 'unsupported';
  }
  const pdf = await openPdfjs(bytes, name);
  const proxies = [];
  for (let i = 1; i <= pdf.numPages; i++) proxies.push(await pdf.getPage(i));
  const src = { id, name, bytes, pdf, lib, libError, proxies };
  sources.set(id, src);
  if (persist) idb.put('sources', { id, name, bytes });
  return { src, extracted };
}
function dropSource(id) {
  const s = sources.get(id);
  if (!s) return;
  try { s.pdf.destroy(); } catch { /* egal */ }
  sources.delete(id);
  idb.del('sources', id);
}
let blankSourceId = null;
async function blankSource() {
  if (blankSourceId && sources.has(blankSourceId)) return sources.get(blankSourceId);
  const doc = await PDFDocument.create();
  doc.addPage([595.28, 841.89]);
  doc.addPage([841.89, 595.28]);
  const bytes = await doc.save();
  const { src } = await loadSource('Leere Seiten', bytes);
  blankSourceId = src.id;
  return src;
}

function warnIfLocked(src) {
  if (src.libError === 'encrypted') {
    modal({
      title: 'Geschützte PDF',
      text: `„${src.name}“ ist vom Ersteller geschützt. Ansehen und Text kopieren funktioniert, Speichern mit Änderungen ist bei dieser Datei nicht möglich.`,
      buttons: [{ label: 'Verstanden', value: true, kind: 'primary' }],
    });
  } else if (src.libError) {
    toast('Hinweis: Diese Datei kann angesehen, aber nicht gespeichert werden.', 4000);
  }
}

async function confirmDiscard() {
  if (!S.pages.length || !S.dirty) return true;
  const r = await modal({
    title: 'Änderungen nicht gespeichert',
    text: `„${S.fileName}“ hat ungespeicherte Änderungen. Wenn du fortfährst, gehen sie verloren.`,
    buttons: [{ label: 'Abbrechen', value: false }, { label: 'Verwerfen', value: true, kind: 'danger' }],
  });
  return !!r;
}

async function openDocumentFromBytes(name, bytes) {
  if (!looksLikePdf(bytes)) throw new UserError(`„${name}“ ist keine PDF-Datei.`);
  const oldIds = [...sources.keys()];
  const { src, extracted } = await loadSource(name, bytes);
  for (const id of oldIds) dropSource(id);
  blankSourceId = null;
  S.fileName = name;
  S.pages = src.proxies.map((_, i) => ({ uid: uid(), src: src.id, idx: i, rot: 0, annots: extracted.get(i) || [] }));
  S.dirty = false;
  S.sel = null;
  S.gridSel = new Set();
  S.zoom = 1;
  H.undo.length = 0;
  H.redo.length = 0;
  clearViewer();
  showDocument();
  if (S.tool === 'pages') setTool('read');
  layout();
  viewer.scrollTop = 0;
  viewer.scrollLeft = 0;
  updateChrome();
  await persistNow();
  warnIfLocked(src);
}
async function openFile(file) {
  if (!(await confirmDiscard())) return;
  busy('Datei wird geöffnet …');
  try {
    const bytes = new Uint8Array(await file.arrayBuffer());
    await openDocumentFromBytes(file.name || 'Dokument.pdf', bytes);
  } catch (e) {
    if (!(e instanceof Cancelled)) await errorDialog(e);
  } finally { unbusy(); }
}
async function openSample() {
  if (!(await confirmDiscard())) return;
  busy('Beispiel wird erstellt …');
  try {
    const bytes = await makeSamplePdf();
    await openDocumentFromBytes(`Besprechungsprotokoll_Beispiel_${todayStamp()}.pdf`, bytes);
  } catch (e) {
    if (!(e instanceof Cancelled)) await errorDialog(e);
  } finally { unbusy(); }
}
async function closeDocument() {
  if (!(await confirmDiscard())) return;
  for (const id of [...sources.keys()]) dropSource(id);
  blankSourceId = null;
  S.pages = [];
  S.fileName = '';
  S.dirty = false;
  S.sel = null;
  S.gridSel = new Set();
  H.undo.length = 0;
  H.redo.length = 0;
  clearViewer();
  await idb.clear('state');
  await idb.clear('sources');
  setTool('read');
  showStart();
}
async function resumeSession() {
  busy('Letzte Sitzung wird geladen …');
  try {
    const sess = await idb.get('state', 'session');
    if (!sess || !Array.isArray(sess.pages) || !sess.pages.length) throw new UserError('Es ist keine gespeicherte Sitzung mehr vorhanden.');
    const ids = [...new Set(sess.pages.map((p) => p.src))];
    for (const id of ids) {
      if (sources.has(id)) continue;
      const rec = await idb.get('sources', id);
      if (!rec || !rec.bytes) throw new UserError('Die letzte Sitzung ist unvollständig und kann nicht geladen werden. Bitte öffne die Datei neu.');
      const { src, extracted } = await loadSource(rec.name, new Uint8Array(rec.bytes), { id, persist: false });
      if (rec.name === 'Leere Seiten') blankSourceId = id;
      if (extracted.size) { /* gespeicherte Quellen enthalten keine eigenen Anmerkungen mehr */ }
      void src;
    }
    S.pages = sess.pages.map((p) => ({
      uid: p.uid || uid(), src: p.src, idx: p.idx, rot: norm360(p.rot || 0),
      annots: (p.annots || []).map(cleanAnnot).filter(Boolean),
    })).filter((p) => sources.has(p.src) && p.idx >= 0 && p.idx < sources.get(p.src).proxies.length);
    if (!S.pages.length) throw new UserError('Die letzte Sitzung enthält keine Seiten.');
    S.fileName = sess.fileName || 'Dokument.pdf';
    S.dirty = !!sess.dirty;
    S.sel = null;
    S.gridSel = new Set();
    S.zoom = 1;
    H.undo.length = 0;
    H.redo.length = 0;
    clearViewer();
    showDocument();
    layout();
    updateChrome();
  } catch (e) {
    await errorDialog(e);
  } finally { unbusy(); }
}

// ---------------------------------------------------------------- sample document
async function makeSamplePdf() {
  const doc = await PDFDocument.create();
  doc.setTitle('Besprechungsprotokoll Nr. 12 (Beispiel)');
  const f = await doc.embedFont(StandardFonts.Helvetica);
  const fb = await doc.embedFont(StandardFonts.HelveticaBold);
  const grey = { type: 'RGB', red: 0.35, green: 0.38, blue: 0.42 };
  const ink = { type: 'RGB', red: 0.1, green: 0.11, blue: 0.13 };
  const rgbC = (c) => window.PDFLib.rgb(c.red, c.green, c.blue);

  const p1 = doc.addPage([595.28, 841.89]);
  let y = 780;
  p1.drawText('Besprechungsprotokoll Nr. 12', { x: 56, y, size: 20, font: fb, color: rgbC(ink) });
  y -= 22;
  p1.drawText('Bauvorhaben Wohnanlage Lindenweg · Beispieldatei', { x: 56, y, size: 11, font: f, color: rgbC(grey) });
  y -= 34;
  const meta = [['Datum', '08.10.2026, 09:00 – 10:30'], ['Ort', 'Baubüro, Container 2'], ['Teilnehmer', 'Bauleitung, Statik, Elektro, HLS, Baumeister'], ['Verteiler', 'alle Teilnehmer, Bauherr']];
  for (const [k, v] of meta) {
    p1.drawText(k, { x: 56, y, size: 10, font: fb, color: rgbC(ink) });
    p1.drawText(v, { x: 150, y, size: 10, font: f, color: rgbC(ink) });
    y -= 16;
  }
  y -= 14;
  const cols = [56, 96, 360, 460];
  const head = ['Pkt.', 'Thema', 'Zuständig', 'Termin'];
  p1.drawRectangle({ x: 50, y: y - 6, width: 495, height: 20, color: window.PDFLib.rgb(0.93, 0.94, 0.95) });
  head.forEach((h, i) => p1.drawText(h, { x: cols[i], y, size: 10, font: fb, color: rgbC(ink) }));
  y -= 24;
  const rows = [
    ['12.1', 'Bewehrungsabnahme Decke über EG', 'Statik', '14.10.2026'],
    ['12.2', 'Leerverrohrung Elektro im 1. OG prüfen', 'Elektro', '16.10.2026'],
    ['12.3', 'Schlitze und Durchbrüche HLS freigeben', 'HLS', '20.10.2026'],
    ['12.4', 'Fenster: Naturmaße nehmen und melden', 'Bauleitung', '22.10.2026'],
    ['12.5', 'Gerüst Nordseite um eine Lage erhöhen', 'Baumeister', '13.10.2026'],
    ['12.6', 'Nächste Besprechung', 'alle', '15.10.2026'],
  ];
  for (const r of rows) {
    r.forEach((t, i) => p1.drawText(t, { x: cols[i], y, size: 10, font: f, color: rgbC(ink) }));
    p1.drawLine({ start: { x: 50, y: y - 8 }, end: { x: 545, y: y - 8 }, thickness: 0.5, color: window.PDFLib.rgb(0.8, 0.82, 0.85) });
    y -= 24;
  }
  y -= 16;
  const para = [
    'Zu 12.1: Die Abnahme erfolgt durch den Statiker vor Ort. Betonieren ist erst nach',
    'schriftlicher Freigabe erlaubt. Das Betonierprotokoll wird dem Bauherrn übermittelt.',
    'Zu 12.4: Abweichungen über 2 cm zum Plan sind sofort der Bauleitung zu melden.',
  ];
  for (const l of para) { p1.drawText(l, { x: 56, y, size: 10, font: f, color: rgbC(ink) }); y -= 15; }
  p1.drawText('Beispieldatei der PDF Werkstatt. Alle Angaben sind frei erfunden.', { x: 56, y: 40, size: 8, font: f, color: rgbC(grey) });

  // Seite 2: kleiner Grundriss im Maßstab 1:50
  const p2 = doc.addPage([841.89, 595.28]);
  p2.drawText('Grundriss EG (Beispiel)', { x: 56, y: 540, size: 16, font: fb, color: rgbC(ink) });
  p2.drawText('M 1:50', { x: 56, y: 520, size: 11, font: f, color: rgbC(grey) });
  const mm = 72 / 25.4;
  const sx = 160, sy = 140;
  const W = 8000 / 50 * mm, Hh = 5000 / 50 * mm, t = 300 / 50 * mm;
  const dark = window.PDFLib.rgb(0.15, 0.15, 0.17);
  p2.drawRectangle({ x: sx, y: sy, width: W, height: Hh, borderColor: dark, borderWidth: t });
  p2.drawLine({ start: { x: sx + W * 0.55, y: sy }, end: { x: sx + W * 0.55, y: sy + Hh * 0.62 }, thickness: t * 0.6, color: dark });
  p2.drawText('Wohnen 24,6 m²', { x: sx + 40, y: sy + Hh / 2, size: 10, font: f, color: rgbC(ink) });
  p2.drawText('Küche 12,2 m²', { x: sx + W * 0.62, y: sy + Hh * 0.35, size: 10, font: f, color: rgbC(ink) });
  // Maßketten
  const dy = sy - 30;
  p2.drawLine({ start: { x: sx, y: dy }, end: { x: sx + W, y: dy }, thickness: 0.6, color: dark });
  for (const x of [sx, sx + W]) p2.drawLine({ start: { x: x - 4, y: dy - 4 }, end: { x: x + 4, y: dy + 4 }, thickness: 0.8, color: dark });
  p2.drawText('8,00', { x: sx + W / 2 - 10, y: dy + 4, size: 9, font: f, color: rgbC(ink) });
  const dx = sx + W + 30;
  p2.drawLine({ start: { x: dx, y: sy }, end: { x: dx, y: sy + Hh }, thickness: 0.6, color: dark });
  for (const yy of [sy, sy + Hh]) p2.drawLine({ start: { x: dx - 4, y: yy - 4 }, end: { x: dx + 4, y: yy + 4 }, thickness: 0.8, color: dark });
  p2.drawText('5,00', { x: dx + 6, y: sy + Hh / 2, size: 9, font: f, color: rgbC(ink) });
  return doc.save();
}

// ---------------------------------------------------------------- viewer
const viewer = $('#viewer');
const pagesEl = $('#pages');
let fitAvail = 600;
let needLayout = false;
const visible = new Set();
const pageByUid = (u) => S.pages.find((p) => p.uid === u);
const pageEl = (u) => pagesEl.querySelector(`.pg[data-uid="${u}"]`);
const proxyOf = (p) => sources.get(p.src).proxies[p.idx];
const totalRot = (p) => norm360(proxyOf(p).rotate + p.rot);
const vpOf = (p, scale) => proxyOf(p).getViewport({ scale, rotation: totalRot(p) });
// Jede Seite füllt die Bildschirmbreite (wie in der Dateien-App), höchstens 2 px je pt
const scaleOf = (p) => Math.min(2, fitAvail / vpOf(p, 1).width) * S.zoom;

const io = new IntersectionObserver((entries) => {
  for (const en of entries) {
    const el = en.target;
    if (en.isIntersecting) visible.add(el);
    else { visible.delete(el); releasePage(el); }
  }
  pump();
}, { root: viewer, rootMargin: '100% 50%' });

function computeFit() {
  fitAvail = Math.max(120, viewer.clientWidth - 24);
}
function createPageEl(p) {
  const el = document.createElement('div');
  el.className = 'pg';
  el.dataset.uid = p.uid;
  const hl = svg('svg', { class: 'hl' });
  const top = svg('svg', { class: 'top' });
  const hit = document.createElement('div');
  hit.className = 'hit';
  const num = document.createElement('span');
  num.className = 'pnum';
  el.append(hl, top, hit, num);
  el._hl = hl;
  el._top = top;
  io.observe(el);
  return el;
}
function sizePageEl(el, p, scale) {
  const vp = vpOf(p, scale);
  el._vp = vp;
  el.style.width = vp.width + 'px';
  el.style.height = vp.height + 'px';
  el.style.setProperty('--total-scale-factor', String(vp.scale));
  const key = `${scale.toFixed(5)}|${vp.rotation}|${p.src}|${p.idx}`;
  if (el._key !== key) {
    if (el._shapeKey !== `${vp.rotation}|${p.src}|${p.idx}`) {
      // falsche Ausrichtung/Seite: altes Bild sofort entfernen
      releasePage(el);
    }
    el._key = null;
    el._wantKey = key;
  }
  el._shapeKey = `${vp.rotation}|${p.src}|${p.idx}`;
  drawAnnots(el);
}
function layout() {
  needLayout = false;
  if (!S.pages.length) return;
  computeFit();
  const existing = new Map();
  for (const el of pagesEl.children) existing.set(el.dataset.uid, el);
  S.pages.forEach((p, i) => {
    let el = existing.get(p.uid);
    if (el) existing.delete(p.uid); else el = createPageEl(p);
    el.querySelector('.pnum').textContent = `${i + 1}`;
    sizePageEl(el, p, scaleOf(p));
    if (pagesEl.children[i] !== el) pagesEl.insertBefore(el, pagesEl.children[i] || null);
  });
  for (const el of existing.values()) { io.unobserve(el); visible.delete(el); releasePage(el); el.remove(); }
  $('#zoomPct').textContent = `${Math.round(S.zoom * 100)} %`;
  updateIndicator();
  pump();
}
function clearViewer() {
  for (const el of [...pagesEl.children]) { io.unobserve(el); releasePage(el); el.remove(); }
  visible.clear();
}
function releasePage(el) {
  if (el._task) { try { el._task.cancel(); } catch { /* egal */ } el._task = null; }
  if (el._tl) { try { el._tl.cancel(); } catch { /* egal */ } el._tl = null; }
  const c = el.querySelector('canvas.pc');
  if (c) { c.width = 0; c.height = 0; c.remove(); }
  const t = el.querySelector('.textLayer');
  if (t) t.remove();
  el._key = null;
  el._rendering = null;
}

let pumping = false;
async function pump() {
  if (pumping) return;
  pumping = true;
  try {
    for (;;) {
      const center = viewer.scrollTop + viewer.clientHeight / 2;
      let best = null;
      let bestD = Infinity;
      for (const el of visible) {
        if (!el.isConnected || el._key === el._wantKey) continue;
        const d = Math.abs(el.offsetTop + el.offsetHeight / 2 - center);
        if (d < bestD) { bestD = d; best = el; }
      }
      if (!best) break;
      await renderPage(best);
    }
  } finally { pumping = false; }
}
async function renderPage(el) {
  const p = pageByUid(el.dataset.uid);
  if (!p || !sources.has(p.src)) { el._key = el._wantKey; return; }
  const key = el._wantKey;
  const vp = el._vp;
  const proxy = proxyOf(p);
  const dpr = window.devicePixelRatio || 1;
  let out = dpr;
  if (vp.width * vp.height * out * out > MAX_CANVAS_PX) out = Math.sqrt(MAX_CANVAS_PX / (vp.width * vp.height));
  const canvas = document.createElement('canvas');
  canvas.className = 'pc';
  canvas.width = Math.max(1, Math.floor(vp.width * out));
  canvas.height = Math.max(1, Math.floor(vp.height * out));
  const task = proxy.render({
    canvas,
    viewport: vp,
    transform: out !== 1 ? [out, 0, 0, out, 0, 0] : undefined,
    annotationMode: pdfjsLib.AnnotationMode.ENABLE,
  });
  el._task = task;
  try {
    await task.promise;
  } catch (e) {
    canvas.width = 0; canvas.height = 0;
    if (e?.name !== 'RenderingCancelledException') { console.warn(e); el._key = key; }
    return;
  } finally { if (el._task === task) el._task = null; }
  if (el._wantKey !== key || !el.isConnected) { canvas.width = 0; canvas.height = 0; return; }
  const old = el.querySelector('canvas.pc');
  if (old) { old.width = 0; old.height = 0; old.remove(); }
  el.insertBefore(canvas, el.firstChild);
  el._key = key;
  // Textebene zum Markieren und Kopieren
  const oldTl = el.querySelector('.textLayer');
  if (oldTl) oldTl.remove();
  const tl = document.createElement('div');
  tl.className = 'textLayer';
  el.insertBefore(tl, el._top);
  try {
    const layer = new pdfjsLib.TextLayer({ textContentSource: proxy.streamTextContent(), container: tl, viewport: vp });
    el._tl = layer;
    await layer.render();
    const end = document.createElement('div');
    end.className = 'endOfContent';
    tl.appendChild(end);
  } catch (e) {
    if (e?.name !== 'AbortException') console.warn(e);
  } finally { el._tl = null; }
}

// ---------------------------------------------------------------- drawing annotations
function drawAnnotsInto(hlSvg, topSvg, p, vp, { selId = null, interactive = true } = {}) {
  hlSvg.replaceChildren();
  topSvg.replaceChildren();
  for (const s of [hlSvg, topSvg]) { s.setAttribute('width', vp.width); s.setAttribute('height', vp.height); }
  const m = `matrix(${vp.transform.join(' ')})`;
  const gH = svg('g', { transform: m }, hlSvg);
  const gT = svg('g', { transform: m }, topSvg);
  const notes = [];
  for (const a of p.annots) {
    if (a.type === 'hl') {
      const [x1, y1, x2, y2] = a.rect;
      svg('rect', { x: x1, y: y1, width: x2 - x1, height: y2 - y1, fill: a.color }, gH);
    } else if (a.type === 'ink') {
      svg('path', { d: inkPath(a.pts), fill: 'none', stroke: a.color, 'stroke-width': a.w, 'stroke-linecap': 'round', 'stroke-linejoin': 'round' }, gT);
    } else if (a.type === 'text') {
      const L = textLayout(a);
      const g = svg('g', { transform: `matrix(${textMatrix(a).join(' ')})` }, gT);
      if (a.bg) svg('rect', { x: 0, y: 0, width: L.w, height: L.h, fill: '#ffffff' }, g);
      const t = svg('text', { 'font-family': 'Helvetica, Arial, sans-serif', 'font-size': L.fs, fill: a.color }, g);
      t.style.whiteSpace = 'pre';
      L.lines.forEach((line, i) => {
        const ts = svg('tspan', { x: L.pad, y: L.pad + L.asc + i * L.lh }, t);
        ts.textContent = line;
      });
    } else if (a.type === 'note') {
      notes.push(a);
    }
  }
  for (const a of notes) {
    const [cx, cy] = vp.convertToViewportPoint(a.x, a.y);
    const s = NOTE_SIZE * vp.scale;
    const g = svg('g', { transform: `translate(${cx - s / 2} ${cy - s / 2}) scale(${s / 20})`, class: interactive ? 'noteicon' : '' }, topSvg);
    g.dataset.id = a.id;
    svg('path', { d: 'M3 2.5h14a1.5 1.5 0 0 1 1.5 1.5v9a1.5 1.5 0 0 1-1.5 1.5H9l-4.5 3.5v-3.5H3A1.5 1.5 0 0 1 1.5 13V4A1.5 1.5 0 0 1 3 2.5z', fill: a.color, stroke: '#3a3a3a', 'stroke-width': 1 }, g);
    svg('path', { d: 'M5 6.5h10M5 9.5h7', stroke: '#3a3a3a', 'stroke-width': 1.2, 'stroke-linecap': 'round' }, g);
  }
  if (selId) {
    const a = p.annots.find((x) => x.id === selId);
    if (a) drawSelection(gT, topSvg, a, vp);
  }
  return { gH, gT };
}
function drawSelection(gT, topSvg, a, vp) {
  const sw = 1.5 / vp.scale;
  const dash = `${4 / vp.scale} ${3 / vp.scale}`;
  if (a.type === 'text') {
    const c = textCorners(a, textLayout(a));
    svg('polygon', { points: c.map((q) => q.join(',')).join(' '), fill: 'none', stroke: SEL_COLOR, 'stroke-width': sw, 'stroke-dasharray': dash }, gT);
  } else if (a.type === 'note') {
    const [cx, cy] = vp.convertToViewportPoint(a.x, a.y);
    const s = NOTE_SIZE * vp.scale + 8;
    svg('rect', { x: cx - s / 2, y: cy - s / 2, width: s, height: s, rx: 4, fill: 'none', stroke: SEL_COLOR, 'stroke-width': 1.5, 'stroke-dasharray': '4 3' }, topSvg);
  } else {
    const [x1, y1, x2, y2] = annotBounds(a);
    const m = 2 / vp.scale;
    svg('rect', { x: x1 - m, y: y1 - m, width: x2 - x1 + 2 * m, height: y2 - y1 + 2 * m, fill: 'none', stroke: SEL_COLOR, 'stroke-width': sw, 'stroke-dasharray': dash }, gT);
  }
}
function inkPath(pts) {
  if (pts.length === 1) return `M${pts[0][0]} ${pts[0][1]}l0.01 0`;
  return 'M' + pts.map((q) => `${q[0]} ${q[1]}`).join('L');
}
function drawAnnots(el) {
  const p = pageByUid(el.dataset.uid);
  if (!p || !el._vp) return;
  const selId = S.sel && S.sel.uid === p.uid ? S.sel.id : null;
  const g = drawAnnotsInto(el._hl, el._top, p, el._vp, { selId });
  el._gH = g.gH;
  el._gT = g.gT;
}

// ---------------------------------------------------------------- tools & pointer input
const tools = ['read', 'select', 'hl', 'ink', 'text', 'note', 'pages'];
function setTool(t) {
  if (!tools.includes(t)) return;
  const prev = S.tool;
  S.tool = t;
  for (const b of $$('#toolbar .tool')) b.setAttribute('aria-pressed', String(b.dataset.tool === t));
  viewer.className = 'mode-' + (t === 'pages' ? 'read' : t);
  if (t !== 'select' && S.sel) setSel(null);
  if (t !== 'read') { const s = window.getSelection(); if (s && s.rangeCount) s.removeAllRanges(); }
  renderToolOpts();
  if (t === 'pages') { showGrid(); } else if (prev === 'pages') { hideGrid(); }
  updateChrome();
}

function renderToolOpts() {
  const box = $('#toolOpts');
  box.replaceChildren();
  const t = S.tool;
  if (!S.pages.length || !['hl', 'ink', 'text', 'note'].includes(t)) { box.hidden = true; return; }
  box.hidden = false;
  const o = S.opts[t];
  const sw = document.createElement('div');
  sw.className = 'swatches';
  for (const [name, col] of PALETTES[t]) {
    const b = document.createElement('button');
    b.type = 'button';
    b.className = 'sw';
    b.style.background = col;
    b.title = name;
    b.setAttribute('aria-label', name);
    b.setAttribute('aria-pressed', String(o.color === col));
    b.addEventListener('click', () => { o.color = col; saveOpts(); renderToolOpts(); });
    sw.appendChild(b);
  }
  box.appendChild(sw);
  if (t === 'ink') {
    box.appendChild(Object.assign(document.createElement('span'), { className: 'sep' }));
    const sz = document.createElement('div');
    sz.className = 'sizes';
    for (const [name, w] of INK_WIDTHS) {
      const b = document.createElement('button');
      b.type = 'button';
      b.className = 'sz';
      b.title = name;
      b.setAttribute('aria-label', `Strichstärke ${name}`);
      b.setAttribute('aria-pressed', String(o.w === w));
      const d = document.createElement('span');
      d.className = 'dot';
      d.style.width = d.style.height = `${3 + w * 2}px`;
      b.appendChild(d);
      b.addEventListener('click', () => { o.w = w; saveOpts(); renderToolOpts(); });
      sz.appendChild(b);
    }
    box.appendChild(sz);
  }
  if (t === 'text') {
    box.appendChild(Object.assign(document.createElement('span'), { className: 'sep' }));
    const sz = document.createElement('div');
    sz.className = 'sizes';
    for (const s of TEXT_SIZES) {
      const b = document.createElement('button');
      b.type = 'button';
      b.className = 'sz';
      b.textContent = `${s} pt`;
      b.setAttribute('aria-pressed', String(o.size === s));
      b.addEventListener('click', () => { o.size = s; saveOpts(); renderToolOpts(); });
      sz.appendChild(b);
    }
    box.appendChild(sz);
    const tg = document.createElement('button');
    tg.type = 'button';
    tg.className = 'toggle';
    tg.textContent = 'Weiß hinterlegt';
    tg.title = 'Text auf weißem Grund, zum Abdecken und Ausbessern';
    tg.setAttribute('aria-pressed', String(!!o.bg));
    tg.addEventListener('click', () => { o.bg = !o.bg; saveOpts(); renderToolOpts(); });
    box.appendChild(tg);
  }
  const hint = document.createElement('span');
  hint.className = 'optlabel';
  hint.textContent = {
    hl: 'Über den Text ziehen',
    ink: 'Mit Finger oder Stift zeichnen',
    text: 'Auf die Stelle tippen',
    note: 'Auf die Stelle tippen',
  }[t];
  box.appendChild(hint);
}

let gesture = null;
const activePointers = new Set();
function toPdfPt(el, e) {
  const r = el.getBoundingClientRect();
  const sx = el._vp.width / r.width || 1;
  const sy = el._vp.height / r.height || 1;
  const [x, y] = el._vp.convertToPdfPoint((e.clientX - r.left) * sx, (e.clientY - r.top) * sy);
  return [r2(x), r2(y)];
}
function cancelGesture() {
  if (!gesture) return;
  const g = gesture;
  gesture = null;
  if (g.dragStarted && g.before) {
    // Verschieben abbrechen: Ausgangszustand wiederherstellen
    S.pages = g.before;
    H.undo.pop();
    layout();
  } else if (g.el.isConnected) drawAnnots(g.el);
}
pagesEl.addEventListener('pointerdown', (e) => {
  const hit = e.target.closest('.hit');
  if (!hit || S.tool === 'read' || S.tool === 'pages' || modalOpen) return;
  activePointers.add(e.pointerId);
  if (activePointers.size > 1 || pinch.active) { cancelGesture(); return; }
  if (e.pointerType === 'mouse' && e.button !== 0) return;
  e.preventDefault();
  const el = hit.parentElement;
  const p = pageByUid(el.dataset.uid);
  if (!p || !el._vp) return;
  try { hit.setPointerCapture(e.pointerId); } catch { /* egal */ }
  const pt = toPdfPt(el, e);
  gesture = { el, p, id: e.pointerId, start: pt, cx: e.clientX, cy: e.clientY, moved: false };
  if (S.tool === 'hl') {
    gesture.preview = svg('rect', { fill: S.opts.hl.color, x: pt[0], y: pt[1], width: 0, height: 0 }, el._gH);
  } else if (S.tool === 'ink') {
    gesture.pts = [pt];
    gesture.lastClient = [e.clientX, e.clientY];
    gesture.preview = svg('path', { d: inkPath(gesture.pts), fill: 'none', stroke: S.opts.ink.color, 'stroke-width': S.opts.ink.w, 'stroke-linecap': 'round', 'stroke-linejoin': 'round' }, el._gT);
  } else if (S.tool === 'select') {
    const a = hitAnnot(p, pt, 12 / el._vp.scale);
    if (a) {
      setSel({ uid: p.uid, id: a.id });
      gesture.drag = { id: a.id, orig: a };
    } else {
      setSel(null);
    }
  }
});
pagesEl.addEventListener('pointermove', (e) => {
  const g = gesture;
  if (!g || e.pointerId !== g.id) return;
  e.preventDefault();
  if (!g.moved && Math.hypot(e.clientX - g.cx, e.clientY - g.cy) > 4) g.moved = true;
  if (S.tool === 'hl' && g.preview) {
    const pt = toPdfPt(g.el, e);
    const [x1, y1, x2, y2] = normRect([g.start[0], g.start[1], pt[0], pt[1]]);
    g.cur = pt;
    g.preview.setAttribute('x', x1); g.preview.setAttribute('y', y1);
    g.preview.setAttribute('width', x2 - x1); g.preview.setAttribute('height', y2 - y1);
  } else if (S.tool === 'ink' && g.pts) {
    const evs = typeof e.getCoalescedEvents === 'function' ? e.getCoalescedEvents() : [];
    for (const ev of (evs.length ? evs : [e])) {
      if (Math.hypot(ev.clientX - g.lastClient[0], ev.clientY - g.lastClient[1]) < 1.5) continue;
      g.lastClient = [ev.clientX, ev.clientY];
      g.pts.push(toPdfPt(g.el, ev));
    }
    g.preview.setAttribute('d', inkPath(g.pts));
  } else if (S.tool === 'select' && g.drag && g.moved) {
    const pt = toPdfPt(g.el, e);
    if (!g.dragStarted) { g.before = snapshot(); checkpoint(); g.dragStarted = true; }
    const i = g.p.annots.findIndex((a) => a.id === g.drag.id);
    if (i >= 0) {
      g.p.annots[i] = moveAnnot(g.drag.orig, pt[0] - g.start[0], pt[1] - g.start[1]);
      drawAnnots(g.el);
    }
  }
});
function endGesture(e) {
  activePointers.delete(e.pointerId);
  const g = gesture;
  if (!g || e.pointerId !== g.id) return;
  gesture = null;
  const { el, p } = g;
  if (e.type === 'pointercancel') { drawAnnots(el); if (g.dragStarted) { S.pages = g.before; H.undo.pop(); layout(); updateChrome(); } return; }
  if (S.tool === 'hl') {
    const end = g.cur || g.start;
    const r = normRect([g.start[0], g.start[1], end[0], end[1]]);
    const minPdf = 3 / el._vp.scale;
    if (r[2] - r[0] < minPdf || r[3] - r[1] < minPdf) {
      drawAnnots(el);
      toast('Zum Markieren mit dem Finger über den Text ziehen.');
      return;
    }
    checkpoint();
    p.annots.push({ id: uid(), type: 'hl', color: S.opts.hl.color, rect: r.map(r2) });
    changed({ uidOnly: p.uid });
  } else if (S.tool === 'ink') {
    checkpoint();
    p.annots.push({ id: uid(), type: 'ink', color: S.opts.ink.color, w: S.opts.ink.w, pts: g.pts });
    changed({ uidOnly: p.uid });
  } else if (S.tool === 'text' && !g.moved) {
    newText(el, p, g.start);
  } else if (S.tool === 'note' && !g.moved) {
    newNote(el, p, g.start);
  } else if (S.tool === 'select') {
    if (g.dragStarted) changed({ uidOnly: p.uid });
  }
}
window.addEventListener('pointerup', endGesture);
window.addEventListener('pointercancel', endGesture);

// Notiz im Lesemodus antippen → öffnen
pagesEl.addEventListener('click', (e) => {
  if (S.tool !== 'read') return;
  const ic = e.target.closest('.noteicon');
  if (!ic) return;
  const el = ic.closest('.pg');
  const p = pageByUid(el.dataset.uid);
  const a = p && p.annots.find((x) => x.id === ic.dataset.id);
  if (a) editNote(p, a);
});

// ---------------------------------------------------------------- text & note dialogs
function pickerRow(palette, current, onPick) {
  const row = document.createElement('div');
  row.className = 'swatches';
  const btns = [];
  for (const [name, col] of palette) {
    const b = document.createElement('button');
    b.type = 'button';
    b.className = 'sw';
    b.style.background = col;
    b.title = name;
    b.setAttribute('aria-label', name);
    b.setAttribute('aria-pressed', String(current === col));
    b.addEventListener('click', () => { btns.forEach((x) => x.setAttribute('aria-pressed', String(x === b))); onPick(col); });
    btns.push(b);
    row.appendChild(b);
  }
  return row;
}
function textEditorContent(init) {
  const wrap = document.createElement('div');
  wrap.style.display = 'flex';
  wrap.style.flexDirection = 'column';
  wrap.style.gap = '12px';
  const ta = document.createElement('textarea');
  ta.id = 'textInput';
  ta.value = init.text || '';
  ta.placeholder = 'Text eingeben';
  wrap.appendChild(ta);
  const state = { color: init.color, size: init.size, bg: init.bg };
  wrap.appendChild(pickerRow(PALETTES.text, state.color, (c) => { state.color = c; }));
  const sizes = document.createElement('div');
  sizes.className = 'sizes';
  sizes.style.flexWrap = 'wrap';
  const sbtns = [];
  for (const s of TEXT_SIZES) {
    const b = document.createElement('button');
    b.type = 'button';
    b.className = 'sz';
    b.textContent = `${s} pt`;
    b.setAttribute('aria-pressed', String(state.size === s));
    b.addEventListener('click', () => { state.size = s; sbtns.forEach((x) => x.setAttribute('aria-pressed', String(x === b))); });
    sbtns.push(b);
    sizes.appendChild(b);
  }
  const tg = document.createElement('button');
  tg.type = 'button';
  tg.className = 'toggle';
  tg.textContent = 'Weiß hinterlegt';
  tg.setAttribute('aria-pressed', String(!!state.bg));
  tg.addEventListener('click', () => { state.bg = !state.bg; tg.setAttribute('aria-pressed', String(state.bg)); });
  sizes.appendChild(tg);
  wrap.appendChild(sizes);
  return { wrap, ta, state };
}
async function newText(el, p, pt) {
  const o = S.opts.text;
  const { wrap, ta, state } = textEditorContent({ text: '', color: o.color, size: o.size, bg: o.bg });
  const res = await modal({
    title: 'Text einfügen',
    content: wrap,
    buttons: [{ label: 'Abbrechen', value: null }, { label: 'Einfügen', value: 'ok', kind: 'primary' }],
    onOpen: () => ta.focus(),
  });
  if (res !== 'ok') return;
  const { text, replaced } = sanitizeText(ta.value);
  if (!text.trim()) return;
  Object.assign(o, state);
  saveOpts();
  renderToolOpts();
  checkpoint();
  p.annots.push({ id: uid(), type: 'text', color: state.color, size: state.size, bg: state.bg, x: pt[0], y: pt[1], text, rc: el._vp.rotation });
  changed({ uidOnly: p.uid });
  if (replaced) toast('Einige Sonderzeichen werden von der PDF-Schrift nicht unterstützt und wurden durch „?“ ersetzt.', 4500);
}
async function editText(p, a) {
  const { wrap, ta, state } = textEditorContent(a);
  const res = await modal({
    title: 'Text bearbeiten',
    content: wrap,
    buttons: [{ label: 'Löschen', value: 'del', kind: 'danger' }, { label: 'Abbrechen', value: null }, { label: 'Übernehmen', value: 'ok', kind: 'primary' }],
    onOpen: () => ta.focus(),
  });
  if (res === 'del') { deleteAnnot(p, a.id); return; }
  if (res !== 'ok') return;
  const { text, replaced } = sanitizeText(ta.value);
  if (!text.trim()) { deleteAnnot(p, a.id); return; }
  checkpoint();
  const i = p.annots.findIndex((x) => x.id === a.id);
  if (i >= 0) p.annots[i] = { ...a, text, color: state.color, size: state.size, bg: state.bg };
  changed({ uidOnly: p.uid });
  if (replaced) toast('Einige Sonderzeichen wurden durch „?“ ersetzt.', 4000);
}
function noteContent(init) {
  const wrap = document.createElement('div');
  wrap.style.display = 'flex';
  wrap.style.flexDirection = 'column';
  wrap.style.gap = '12px';
  const ta = document.createElement('textarea');
  ta.id = 'noteInput';
  ta.value = init.text || '';
  ta.placeholder = 'Anmerkung eingeben';
  wrap.appendChild(ta);
  const state = { color: init.color };
  wrap.appendChild(pickerRow(PALETTES.note, state.color, (c) => { state.color = c; }));
  return { wrap, ta, state };
}
async function newNote(el, p, pt) {
  const o = S.opts.note;
  const { wrap, ta, state } = noteContent({ text: '', color: o.color });
  const res = await modal({
    title: 'Notiz anlegen',
    content: wrap,
    buttons: [{ label: 'Abbrechen', value: null }, { label: 'Anlegen', value: 'ok', kind: 'primary' }],
    onOpen: () => ta.focus(),
  });
  if (res !== 'ok') return;
  const text = ta.value.replace(/\r\n?/g, '\n');
  if (!text.trim()) return;
  o.color = state.color;
  saveOpts();
  renderToolOpts();
  checkpoint();
  p.annots.push({ id: uid(), type: 'note', color: state.color, x: pt[0], y: pt[1], text });
  changed({ uidOnly: p.uid });
}
async function editNote(p, a) {
  const { wrap, ta, state } = noteContent(a);
  const res = await modal({
    title: 'Notiz',
    content: wrap,
    buttons: [{ label: 'Löschen', value: 'del', kind: 'danger' }, { label: 'Schließen', value: null }, { label: 'Speichern', value: 'ok', kind: 'primary' }],
  });
  if (res === 'del') { deleteAnnot(p, a.id); return; }
  if (res !== 'ok') return;
  const text = ta.value.replace(/\r\n?/g, '\n');
  if (!text.trim()) { deleteAnnot(p, a.id); return; }
  if (text === a.text && state.color === a.color) return;
  checkpoint();
  const i = p.annots.findIndex((x) => x.id === a.id);
  if (i >= 0) p.annots[i] = { ...a, text, color: state.color };
  changed({ uidOnly: p.uid });
}
function deleteAnnot(p, id) {
  const i = p.annots.findIndex((x) => x.id === id);
  if (i < 0) return;
  checkpoint();
  p.annots.splice(i, 1);
  if (S.sel && S.sel.id === id) S.sel = null;
  changed({ uidOnly: p.uid });
  updateSelBar();
}

// ---------------------------------------------------------------- selection bar
function setSel(sel) {
  const prev = S.sel;
  S.sel = sel;
  if (prev) { const el = pageEl(prev.uid); if (el) drawAnnots(el); }
  if (sel && (!prev || prev.uid !== sel.uid)) { const el = pageEl(sel.uid); if (el) drawAnnots(el); }
  updateSelBar();
}
function selected() {
  if (!S.sel) return null;
  const p = pageByUid(S.sel.uid);
  const a = p && p.annots.find((x) => x.id === S.sel.id);
  return a ? { p, a } : null;
}
function updateSelBar() {
  const cur = selected();
  $('#selBar').hidden = !cur || S.tool !== 'select';
  $('#zoomCtl').hidden = !S.pages.length || S.tool === 'pages' || !!(cur && S.tool === 'select');
  if (cur) $('#selEdit').hidden = !(cur.a.type === 'text' || cur.a.type === 'note');
}
async function editLook(p, a) {
  const pal = PALETTES[a.type];
  const state = { color: a.color, w: a.w };
  const wrap = document.createElement('div');
  wrap.style.display = 'flex';
  wrap.style.flexDirection = 'column';
  wrap.style.gap = '12px';
  wrap.appendChild(pickerRow(pal, a.color, (c) => { state.color = c; }));
  if (a.type === 'ink') {
    const sz = document.createElement('div');
    sz.className = 'sizes';
    const bs = [];
    for (const [name, w] of INK_WIDTHS) {
      const b = document.createElement('button');
      b.type = 'button';
      b.className = 'sz';
      b.textContent = name;
      b.setAttribute('aria-pressed', String(a.w === w));
      b.addEventListener('click', () => { state.w = w; bs.forEach((x) => x.setAttribute('aria-pressed', String(x === b))); });
      bs.push(b);
      sz.appendChild(b);
    }
    wrap.appendChild(sz);
  }
  const res = await modal({ title: 'Farbe ändern', content: wrap, buttons: [{ label: 'Abbrechen', value: null }, { label: 'Übernehmen', value: 'ok', kind: 'primary' }] });
  if (res !== 'ok') return;
  checkpoint();
  const i = p.annots.findIndex((x) => x.id === a.id);
  if (i >= 0) p.annots[i] = a.type === 'ink' ? { ...a, color: state.color, w: state.w } : { ...a, color: state.color };
  changed({ uidOnly: p.uid });
}
$('#selEdit').addEventListener('click', () => {
  const cur = selected();
  if (!cur) return;
  if (cur.a.type === 'text') editText(cur.p, cur.a);
  else if (cur.a.type === 'note') editNote(cur.p, cur.a);
});
$('#selColor').addEventListener('click', () => { const cur = selected(); if (cur) editLook(cur.p, cur.a); });
$('#selDelete').addEventListener('click', () => { const cur = selected(); if (cur) deleteAnnot(cur.p, cur.a.id); });
$('#selDone').addEventListener('click', () => setSel(null));

// ---------------------------------------------------------------- zoom & pinch
function anchorAt(clientX, clientY) {
  const r = viewer.getBoundingClientRect();
  const cx = viewer.scrollLeft + clientX - r.left;
  const cy = viewer.scrollTop + clientY - r.top;
  let best = null;
  let bestD = Infinity;
  for (const el of pagesEl.children) {
    const top = el.offsetTop;
    const bot = top + el.offsetHeight;
    const d = cy < top ? top - cy : cy > bot ? cy - bot : 0;
    if (d < bestD) { bestD = d; best = el; }
    if (d === 0) break;
  }
  if (!best) return null;
  return {
    el: best,
    fx: clamp((cx - best.offsetLeft) / best.offsetWidth, -0.5, 1.5),
    fy: clamp((cy - best.offsetTop) / best.offsetHeight, -0.5, 1.5),
    vx: clientX - r.left,
    vy: clientY - r.top,
  };
}
function restoreAnchor(an) {
  if (!an || !an.el.isConnected) return;
  viewer.scrollLeft = an.el.offsetLeft + an.fx * an.el.offsetWidth - an.vx;
  viewer.scrollTop = an.el.offsetTop + an.fy * an.el.offsetHeight - an.vy;
}
function setZoom(z, clientX, clientY) {
  z = clamp(z, MIN_ZOOM, MAX_ZOOM);
  if (Math.abs(z - S.zoom) < 1e-4) return;
  const r = viewer.getBoundingClientRect();
  const an = anchorAt(clientX ?? r.left + r.width / 2, clientY ?? r.top + r.height / 2);
  S.zoom = z;
  layout();
  restoreAnchor(an);
}
const ZOOM_STEPS = [0.25, 0.33, 0.5, 0.67, 0.75, 1, 1.25, 1.5, 2, 2.5, 3, 4, 5, 6];
$('#btnZoomIn').addEventListener('click', () => setZoom(ZOOM_STEPS.find((s) => s > S.zoom + 0.01) ?? MAX_ZOOM));
$('#btnZoomOut').addEventListener('click', () => setZoom([...ZOOM_STEPS].reverse().find((s) => s < S.zoom - 0.01) ?? MIN_ZOOM));
$('#zoomPct').addEventListener('click', () => setZoom(1));

const pinch = { active: false };
function touchDist(t) { return Math.hypot(t[0].clientX - t[1].clientX, t[0].clientY - t[1].clientY); }
function touchMid(t) { return [(t[0].clientX + t[1].clientX) / 2, (t[0].clientY + t[1].clientY) / 2]; }
viewer.addEventListener('touchstart', (e) => {
  if (e.touches.length !== 2 || modalOpen) return;
  e.preventDefault();
  cancelGesture();
  const [mx, my] = touchMid(e.touches);
  const r = viewer.getBoundingClientRect();
  pinch.active = true;
  pinch.d0 = touchDist(e.touches) || 1;
  pinch.z0 = S.zoom;
  pinch.m0 = [mx, my];
  pinch.r = r;
  pinch.sx = viewer.scrollLeft;
  pinch.sy = viewer.scrollTop;
  pinch.c = [viewer.scrollLeft + mx - r.left, viewer.scrollTop + my - r.top];
  pinch.anchor = anchorAt(mx, my);
  pinch.f = 1;
  pinch.m = [mx, my];
  pagesEl.style.willChange = 'transform';
}, { passive: false });
viewer.addEventListener('touchmove', (e) => {
  if (!pinch.active) return;
  e.preventDefault();
  if (e.touches.length < 2) return;
  const z = clamp(pinch.z0 * touchDist(e.touches) / pinch.d0, MIN_ZOOM, MAX_ZOOM);
  pinch.f = z / pinch.z0;
  pinch.m = touchMid(e.touches);
  // Inhaltspunkt c soll unter der Fingermitte bleiben
  const tx = pinch.m[0] - pinch.r.left + pinch.sx - pinch.f * pinch.c[0];
  const ty = pinch.m[1] - pinch.r.top + pinch.sy - pinch.f * pinch.c[1];
  pagesEl.style.transform = `translate(${tx}px, ${ty}px) scale(${pinch.f})`;
}, { passive: false });
function endPinch(e) {
  if (!pinch.active) return;
  if (e.touches && e.touches.length >= 2) return;
  pinch.active = false;
  pagesEl.style.transform = '';
  pagesEl.style.willChange = '';
  const an = pinch.anchor;
  if (an) { an.vx = pinch.m[0] - pinch.r.left; an.vy = pinch.m[1] - pinch.r.top; }
  const z = pinch.z0 * pinch.f;
  if (Math.abs(z - S.zoom) > 1e-4) { S.zoom = z; layout(); }
  restoreAnchor(an);
}
viewer.addEventListener('touchend', endPinch);
viewer.addEventListener('touchcancel', endPinch);
// Safari: eigene Seiten-Zoom-Geste unterdrücken; am Mac Trackpad-Zoom nutzen
const hasTouch = 'ontouchstart' in window || navigator.maxTouchPoints > 0;
let gestureZ0 = 1;
document.addEventListener('gesturestart', (e) => { e.preventDefault(); gestureZ0 = S.zoom; }, { passive: false });
document.addEventListener('gesturechange', (e) => {
  e.preventDefault();
  if (hasTouch || !S.pages.length || viewer.hidden) return;
  setZoom(gestureZ0 * e.scale, e.clientX, e.clientY);
}, { passive: false });
document.addEventListener('gestureend', (e) => e.preventDefault(), { passive: false });
viewer.addEventListener('wheel', (e) => {
  if (!e.ctrlKey) return;
  e.preventDefault();
  setZoom(S.zoom * Math.exp(-e.deltaY * 0.01), e.clientX, e.clientY);
}, { passive: false });

let lastW = 0;
new ResizeObserver(() => {
  const w = viewer.clientWidth;
  if (!S.pages.length || viewer.hidden || w === lastW) return;
  lastW = w;
  const r = viewer.getBoundingClientRect();
  const an = anchorAt(r.left + 1, r.top + 1);
  layout();
  restoreAnchor(an);
}).observe(viewer);

let indRaf = 0;
viewer.addEventListener('scroll', () => {
  if (indRaf) return;
  indRaf = requestAnimationFrame(() => { indRaf = 0; updateIndicator(); });
}, { passive: true });
function currentPageIndex() {
  const mid = viewer.scrollTop + viewer.clientHeight / 2;
  const kids = pagesEl.children;
  for (let i = 0; i < kids.length; i++) {
    if (kids[i].offsetTop + kids[i].offsetHeight + 7 >= mid) return i;
  }
  return Math.max(0, kids.length - 1);
}
function updateIndicator() {
  const ind = $('#pageIndicator');
  if (!S.pages.length) return;
  ind.textContent = `${currentPageIndex() + 1} / ${S.pages.length}`;
}
function scrollToPage(i) {
  const el = pagesEl.children[i];
  if (el) viewer.scrollTop = el.offsetTop - 10;
}
$('#pageIndicator').addEventListener('click', async () => {
  const input = document.createElement('input');
  input.type = 'number';
  input.id = 'gotoInput';
  input.min = '1';
  input.max = String(S.pages.length);
  input.inputMode = 'numeric';
  input.value = String(currentPageIndex() + 1);
  const res = await modal({
    title: 'Zu Seite springen',
    content: input,
    buttons: [{ label: 'Abbrechen', value: null }, { label: 'Springen', value: () => input.value, kind: 'primary' }],
    onOpen: () => { input.focus(); input.select(); },
  });
  const n = parseInt(res, 10);
  if (Number.isFinite(n)) scrollToPage(clamp(n, 1, S.pages.length) - 1);
});

// ---------------------------------------------------------------- page grid
const gridEl = $('#grid');
const thumbIO = new IntersectionObserver((entries) => {
  for (const en of entries) if (en.isIntersecting) renderThumb(en.target);
}, { root: $('#pageGrid'), rootMargin: '200px' });
function showGrid() {
  $('#pageGrid').hidden = false;
  viewer.hidden = true;
  $('#gridBar').hidden = false;
  $('#pageIndicator').hidden = true;
  renderGrid();
}
function hideGrid() {
  $('#pageGrid').hidden = true;
  $('#gridBar').hidden = true;
  if (S.pages.length) {
    viewer.hidden = false;
    $('#pageIndicator').hidden = false;
    if (needLayout) layout();
  }
}
function renderGrid() {
  for (const t of gridEl.children) thumbIO.unobserve(t);
  gridEl.replaceChildren();
  S.pages.forEach((p, i) => {
    const b = document.createElement('button');
    b.type = 'button';
    b.className = 'thumb';
    b.dataset.uid = p.uid;
    b.setAttribute('aria-pressed', String(S.gridSel.has(p.uid)));
    b.setAttribute('aria-label', `Seite ${i + 1}`);
    const frame = document.createElement('div');
    frame.className = 'tframe';
    const tp = document.createElement('div');
    tp.className = 'tpage';
    const vp1 = vpOf(p, 1);
    const s = Math.min(116 / vp1.width, 150 / vp1.height);
    tp.style.width = `${vp1.width * s}px`;
    tp.style.height = `${vp1.height * s}px`;
    const check = document.createElement('span');
    check.className = 'tcheck';
    check.textContent = '✓';
    tp.appendChild(check);
    frame.appendChild(tp);
    const num = document.createElement('span');
    num.className = 'tnum';
    num.textContent = String(i + 1);
    b.append(frame, num);
    b._scale = s;
    b.addEventListener('click', () => {
      if (S.gridSel.has(p.uid)) S.gridSel.delete(p.uid); else S.gridSel.add(p.uid);
      b.setAttribute('aria-pressed', String(S.gridSel.has(p.uid)));
      updateGridBar();
    });
    gridEl.appendChild(b);
    thumbIO.observe(b);
  });
  updateGridBar();
}
async function renderThumb(b) {
  if (b._done) return;
  b._done = true;
  const p = pageByUid(b.dataset.uid);
  if (!p) return;
  const vp = vpOf(p, b._scale);
  const dpr = Math.min(2, window.devicePixelRatio || 1);
  const c = document.createElement('canvas');
  c.width = Math.max(1, Math.floor(vp.width * dpr));
  c.height = Math.max(1, Math.floor(vp.height * dpr));
  const tp = b.querySelector('.tpage');
  try {
    await proxyOf(p).render({ canvas: c, viewport: vp, transform: dpr !== 1 ? [dpr, 0, 0, dpr, 0, 0] : undefined, annotationMode: pdfjsLib.AnnotationMode.ENABLE }).promise;
  } catch { return; }
  if (!b.isConnected) { c.width = 0; c.height = 0; return; }
  tp.insertBefore(c, tp.firstChild);
  if (p.annots.length) {
    const hl = svg('svg', {});
    const top = svg('svg', {});
    hl.style.cssText = 'position:absolute;left:0;top:0;mix-blend-mode:multiply;pointer-events:none';
    top.style.cssText = 'position:absolute;left:0;top:0;pointer-events:none';
    drawAnnotsInto(hl, top, p, vp, { interactive: false });
    tp.insertBefore(top, c.nextSibling);
    tp.insertBefore(hl, top);
  }
}
function selectedIndices() {
  return S.pages.map((p, i) => (S.gridSel.has(p.uid) ? i : -1)).filter((i) => i >= 0);
}
function updateGridBar() {
  const n = S.gridSel.size;
  const total = S.pages.length;
  $('#gCount').textContent = n ? `${n} von ${total} ausgewählt` : `${total} Seiten`;
  $('#gAll').lastChild.textContent = n === total && total ? 'Keine' : 'Alle';
  for (const id of ['gRotL', 'gRotR', 'gUp', 'gDown', 'gDel']) $('#' + id).disabled = !n;
  $('#gGoto').disabled = n !== 1;
  const idx = selectedIndices();
  if (n) {
    $('#gUp').disabled = idx.every((i, k) => i === k);
    $('#gDown').disabled = idx.every((i, k) => i === total - n + k);
  }
}
$('#gAll').addEventListener('click', () => {
  if (S.gridSel.size === S.pages.length) S.gridSel.clear();
  else S.gridSel = new Set(S.pages.map((p) => p.uid));
  for (const b of gridEl.children) b.setAttribute('aria-pressed', String(S.gridSel.has(b.dataset.uid)));
  updateGridBar();
});
function rotateSelected(d) {
  if (!S.gridSel.size) return;
  checkpoint();
  for (const p of S.pages) if (S.gridSel.has(p.uid)) p.rot = norm360(p.rot + d);
  changed({ structure: true });
}
$('#gRotL').addEventListener('click', () => rotateSelected(-90));
$('#gRotR').addEventListener('click', () => rotateSelected(90));
function moveSelected(dir) {
  if (!S.gridSel.size) return;
  let movedAny = false;
  const work = S.pages.slice();
  if (dir < 0) {
    for (let i = 1; i < work.length; i++) {
      if (S.gridSel.has(work[i].uid) && !S.gridSel.has(work[i - 1].uid)) { [work[i - 1], work[i]] = [work[i], work[i - 1]]; movedAny = true; }
    }
  } else {
    for (let i = work.length - 2; i >= 0; i--) {
      if (S.gridSel.has(work[i].uid) && !S.gridSel.has(work[i + 1].uid)) { [work[i + 1], work[i]] = [work[i], work[i + 1]]; movedAny = true; }
    }
  }
  if (!movedAny) return;
  checkpoint();
  S.pages = work;
  changed({ structure: true });
}
$('#gUp').addEventListener('click', () => moveSelected(-1));
$('#gDown').addEventListener('click', () => moveSelected(1));
$('#gDel').addEventListener('click', async () => {
  const n = S.gridSel.size;
  if (!n) return;
  if (n >= S.pages.length) { toast('Mindestens eine Seite muss im Dokument bleiben.'); return; }
  const ok = await modal({
    title: n === 1 ? 'Seite löschen?' : `${n} Seiten löschen?`,
    text: 'Das kannst du mit „Rückgängig“ wieder aufheben.',
    buttons: [{ label: 'Abbrechen', value: false }, { label: 'Löschen', value: true, kind: 'danger' }],
  });
  if (!ok) return;
  checkpoint();
  S.pages = S.pages.filter((p) => !S.gridSel.has(p.uid));
  S.gridSel.clear();
  changed({ structure: true });
});
function insertIndex() {
  const idx = selectedIndices();
  return idx.length ? idx[idx.length - 1] + 1 : S.pages.length;
}
$('#gBlank').addEventListener('click', async () => {
  const res = await modal({
    title: 'Leere Seite einfügen',
    text: S.gridSel.size ? 'Die Seite kommt nach der letzten ausgewählten Seite.' : 'Die Seite kommt ans Ende.',
    stack: true,
    buttons: [{ label: 'A4 Hochformat', value: 0, kind: 'primary' }, { label: 'A4 Querformat', value: 1 }, { label: 'Abbrechen', value: null }],
  });
  if (res !== 0 && res !== 1) return;
  try {
    const src = await blankSource();
    checkpoint();
    const page = { uid: uid(), src: src.id, idx: res, rot: 0, annots: [] };
    S.pages.splice(insertIndex(), 0, page);
    S.gridSel = new Set([page.uid]);
    changed({ structure: true });
  } catch (e) { errorDialog(e); }
});
$('#gPdf').addEventListener('click', () => $('#fileInsert').click());
$('#fileInsert').addEventListener('change', async (e) => {
  const files = [...e.target.files];
  e.target.value = '';
  if (!files.length) return;
  busy('PDF wird eingefügt …');
  try {
    let at = insertIndex();
    const added = [];
    const before = snapshot();
    for (const f of files) {
      const bytes = new Uint8Array(await f.arrayBuffer());
      if (!looksLikePdf(bytes)) throw new UserError(`„${f.name}“ ist keine PDF-Datei.`);
      const { src, extracted } = await loadSource(f.name, bytes);
      const pages = src.proxies.map((_, i) => ({ uid: uid(), src: src.id, idx: i, rot: 0, annots: extracted.get(i) || [] }));
      S.pages.splice(at, 0, ...pages);
      at += pages.length;
      added.push(...pages);
      warnIfLocked(src);
    }
    H.undo.push(before);
    H.redo.length = 0;
    S.gridSel = new Set(added.map((p) => p.uid));
    changed({ structure: true });
    toast(`${added.length} ${added.length === 1 ? 'Seite' : 'Seiten'} eingefügt.`);
  } catch (err) {
    if (!(err instanceof Cancelled)) await errorDialog(err);
  } finally { unbusy(); }
});
$('#gGoto').addEventListener('click', () => {
  const idx = selectedIndices();
  if (idx.length !== 1) return;
  setTool('read');
  requestAnimationFrame(() => scrollToPage(idx[0]));
});

// ---------------------------------------------------------------- saving
function suggestName() {
  let base = (S.fileName || 'Dokument').replace(/\.pdf$/i, '');
  base = base.replace(/[_\s-]?\d{4}[_.-]\d{2}[_.-]\d{2}$/, '').trim().replace(/\s+/g, '_');
  return `${base || 'Dokument'}_${todayStamp()}.pdf`;
}
function cleanFileName(n) {
  let s = (n || '').replace(/[\\/:*?"<>|\u0000-\u001f]/g, '').trim();
  if (!s) s = suggestName();
  if (!/\.pdf$/i.test(s)) s += '.pdf';
  return s;
}
function addAnnotToPage(out, page, a, fontRef) {
  const ctx = out.context;
  const [r, g, b] = hexRgb(a.color);
  const base = {
    Type: 'Annot',
    F: 4,
    C: [r, g, b],
    M: PDFString.of(pdfDate()),
    NM: PDFString.of(a.id),
    [ANNOT_KEY]: PDFHexString.fromText(JSON.stringify(a)),
  };
  let dict;
  if (a.type === 'hl') {
    const [x1, y1, x2, y2] = a.rect;
    const gs = ctx.obj({ Type: 'ExtGState', BM: 'Multiply', CA: 1, ca: 1 });
    const ap = ctx.register(ctx.stream(
      `/GS0 gs ${rgbOp(a.color)} rg ${pdfNum(x1)} ${pdfNum(y1)} ${pdfNum(x2 - x1)} ${pdfNum(y2 - y1)} re f`,
      { Type: 'XObject', Subtype: 'Form', BBox: [x1, y1, x2, y2], Resources: { ExtGState: { GS0: gs } } },
    ));
    dict = { ...base, Subtype: 'Highlight', Rect: [x1, y1, x2, y2], QuadPoints: [x1, y2, x2, y2, x1, y1, x2, y1], CA: 1, AP: { N: ap } };
  } else if (a.type === 'ink') {
    const bb = annotBounds(a);
    const pts = a.pts.length === 1 ? [a.pts[0], [a.pts[0][0] + 0.01, a.pts[0][1]]] : a.pts;
    let path = `${pdfNum(pts[0][0])} ${pdfNum(pts[0][1])} m`;
    for (let i = 1; i < pts.length; i++) path += ` ${pdfNum(pts[i][0])} ${pdfNum(pts[i][1])} l`;
    const ap = ctx.register(ctx.stream(
      `${rgbOp(a.color)} RG ${pdfNum(a.w)} w 1 J 1 j ${path} S`,
      { Type: 'XObject', Subtype: 'Form', BBox: bb },
    ));
    dict = { ...base, Subtype: 'Ink', Rect: bb, InkList: [pts.flat()], BS: { W: a.w, S: 'S' }, AP: { N: ap } };
  } else if (a.type === 'text') {
    const L = textLayout(a);
    const { right, down } = FRAMES[a.rc] || FRAMES[0];
    const matrix = [right[0], right[1], -down[0], -down[1], a.x + L.h * down[0], a.y + L.h * down[1]];
    const c = textCorners(a, L);
    const xs = c.map((q) => q[0]);
    const ys = c.map((q) => q[1]);
    const rect = [Math.min(...xs), Math.min(...ys), Math.max(...xs), Math.max(...ys)];
    let content = '';
    if (a.bg) content += `1 1 1 rg 0 0 ${pdfNum(L.w)} ${pdfNum(L.h)} re f `;
    content += `BT /F1 ${pdfNum(L.fs)} Tf ${rgbOp(a.color)} rg`;
    let prevY = null;
    L.lines.forEach((line, i) => {
      const y = L.h - (L.pad + L.asc + i * L.lh);
      if (prevY === null) content += ` ${pdfNum(L.pad)} ${pdfNum(y)} Td`;
      else content += ` 0 ${pdfNum(y - prevY)} Td`;
      prevY = y;
      content += ` ${fontRef.font.encodeText(line).toString()} Tj`;
    });
    content += ' ET';
    const ap = ctx.register(ctx.stream(content, {
      Type: 'XObject', Subtype: 'Form', BBox: [0, 0, L.w, L.h], Matrix: matrix, Resources: { Font: { F1: fontRef.font.ref } },
    }));
    // „Stamp“: wird von allen Programmen exakt so angezeigt, wie hier gezeichnet
    dict = { ...base, Subtype: 'Stamp', Name: 'Draft', Rect: rect, Contents: PDFHexString.fromText(a.text), AP: { N: ap } };
  } else if (a.type === 'note') {
    const h = NOTE_SIZE / 2;
    const rect = [a.x - h, a.y - h, a.x + h, a.y + h];
    const ap = ctx.register(ctx.stream(
      `${rgbOp(a.color)} rg 0.23 0.23 0.23 RG 1 w 1.5 17.5 m 18.5 17.5 l 18.5 6 l 9 6 l 4.5 2 l 4.5 6 l 1.5 6 l h B ` +
      `1.2 w 1 J 5 13.5 m 15 13.5 l S 5 10.5 m 12 10.5 l S`,
      { Type: 'XObject', Subtype: 'Form', BBox: [0, 0, 20, 20] },
    ));
    dict = { ...base, Subtype: 'Text', F: 28, Name: 'Comment', Open: false, Rect: rect, Contents: PDFHexString.fromText(a.text), AP: { N: ap } };
  } else return;
  const ref = ctx.register(ctx.obj(dict));
  let arr = page.node.lookupMaybe(PDFName.of('Annots'), PDFArray);
  if (!arr) { arr = ctx.obj([]); page.node.set(PDFName.of('Annots'), arr); }
  arr.push(ref);
}
async function buildPdf() {
  const ids = [...new Set(S.pages.map((p) => p.src))];
  for (const id of ids) {
    const s = sources.get(id);
    if (!s.lib) {
      throw new UserError(s.libError === 'encrypted'
        ? `„${s.name}“ ist vom Ersteller geschützt. Solche Dateien kann die App nur ansehen, nicht mit Änderungen speichern.`
        : `„${s.name}“ kann nicht gespeichert werden, weil die Datei fehlerhaft ist oder ein nicht unterstütztes Format hat.`);
    }
  }
  const occ = new Map();
  for (const p of S.pages) {
    const k = p.src + '#' + p.idx;
    occ.set(k, (occ.get(k) || 0) + 1);
  }
  const unique = [...occ.values()].every((n) => n === 1);
  let out;
  let outPages;
  if (ids.length === 1 && unique) {
    // Eine Quelle: Original weiterverwenden, damit Lesezeichen, Formulare und Metadaten erhalten bleiben
    const s = sources.get(ids[0]);
    out = await PDFDocument.load(s.bytes, { updateMetadata: false });
    const all = out.getPages();
    for (const pg of all) {
      for (const key of ['Resources', 'MediaBox', 'CropBox', 'Rotate']) {
        const n = PDFName.of(key);
        if (!pg.node.get(n)) {
          const v = pg.node.getInheritableAttribute(n);
          if (v) pg.node.set(n, v);
        }
      }
    }
    outPages = S.pages.map((p) => all[p.idx]);
    const tree = out.context.obj({ Type: 'Pages', Kids: outPages.map((pg) => pg.ref), Count: outPages.length });
    const treeRef = out.context.register(tree);
    for (const pg of outPages) pg.node.set(PDFName.of('Parent'), treeRef);
    out.catalog.set(PDFName.of('Pages'), treeRef);
  } else {
    out = await PDFDocument.create();
    const copied = new Map(); // "src#idx" -> [PDFPage, ...]
    for (const id of ids) {
      const s = sources.get(id);
      const list = S.pages.filter((p) => p.src === id).map((p) => p.idx);
      // Seiten, die mehrfach vorkommen, brauchen je eine eigene Kopie
      const rounds = [];
      const seen = new Map();
      for (const idx of list) {
        const n = seen.get(idx) || 0;
        seen.set(idx, n + 1);
        (rounds[n] ||= []).push(idx);
      }
      for (const round of rounds) {
        const pages = await out.copyPages(s.lib, round);
        round.forEach((idx, k) => {
          const key = id + '#' + idx;
          if (!copied.has(key)) copied.set(key, []);
          copied.get(key).push(pages[k]);
        });
      }
    }
    outPages = S.pages.map((p) => copied.get(p.src + '#' + p.idx).shift());
    for (const pg of outPages) out.addPage(pg);
    const first = sources.get(S.pages[0].src);
    try { const t = first.lib.getTitle(); if (t) out.setTitle(t); } catch { /* egal */ }
  }
  const needsFont = S.pages.some((p) => p.annots.some((a) => a.type === 'text'));
  const fontRef = needsFont ? { font: await out.embedFont(StandardFonts.Helvetica) } : null;
  S.pages.forEach((p, i) => {
    const pg = outPages[i];
    pg.setRotation(degrees(totalRot(p)));
    for (const a of p.annots) addAnnotToPage(out, pg, a, fontRef);
  });
  out.setModificationDate(new Date());
  out.setProducer('PDF Werkstatt');
  return out.save({ useObjectStreams: true, updateFieldAppearances: false });
}
async function saveFlow() {
  if (!S.pages.length) return;
  const input = document.createElement('input');
  input.type = 'text';
  input.id = 'nameInput';
  input.value = suggestName();
  input.autocapitalize = 'off';
  input.spellcheck = false;
  const lab = document.createElement('label');
  lab.className = 'fld';
  lab.append('Dateiname', input);
  const res = await modal({
    title: 'Als PDF speichern',
    text: 'Das Original bleibt unverändert. Es entsteht eine neue Datei.',
    content: lab,
    buttons: [{ label: 'Abbrechen', value: null }, { label: 'PDF erstellen', value: () => input.value, kind: 'primary' }],
    onOpen: () => { input.focus(); const dot = input.value.lastIndexOf('.'); input.setSelectionRange(0, dot > 0 ? dot : input.value.length); },
  });
  if (res == null) return;
  const name = cleanFileName(res);
  let bytes;
  busy('PDF wird erstellt …');
  try {
    bytes = await buildPdf();
  } catch (e) {
    unbusy();
    await errorDialog(e);
    return;
  }
  unbusy();
  const blob = new Blob([bytes], { type: 'application/pdf' });
  await deliver(name, blob);
}
async function deliver(name, blob) {
  const size = fmtSize(blob.size);
  if (TARGET === 'artifact' && window.claude && typeof window.claude.use === 'function') {
    const go = await modal({ title: 'PDF ist fertig', text: `${name} · ${size}`, buttons: [{ label: 'Abbrechen', value: false }, { label: 'Sichern', value: true, kind: 'primary' }] });
    if (!go) return;
    try {
      const dl = await window.claude.use('downloads');
      if (!dl) throw new UserError('Speichern ist in dieser Vorschau nicht möglich.');
      await dl.save({ filename: name, data: blob });
      markSaved(name);
    } catch (e) {
      if (e && e.code === 'declined') return;
      await errorDialog(e instanceof UserError ? e : new UserError('Speichern hat nicht geklappt: ' + (e?.message || e?.code || 'unbekannter Fehler')));
    }
    return;
  }
  const file = new File([blob], name, { type: 'application/pdf' });
  let canShare = false;
  try { canShare = !!(navigator.canShare && navigator.canShare({ files: [file] })); } catch { canShare = false; }
  const buttons = [];
  if (canShare) buttons.push({ label: 'Teilen oder in „Dateien“ sichern', value: 'share', kind: 'primary' });
  buttons.push({ label: 'Herunterladen', value: 'download', kind: canShare ? '' : 'primary' });
  buttons.push({ label: 'Abbrechen', value: null });
  const how = await modal({ title: 'PDF ist fertig', text: `${name} · ${size}`, stack: true, buttons });
  if (how === 'share') {
    try {
      await navigator.share({ files: [file] });
      markSaved(name);
    } catch (e) {
      if (e && e.name === 'AbortError') return;
      toast('Teilen hat nicht geklappt. Ich lade die Datei stattdessen herunter.', 3500);
      download(file, name);
    }
  } else if (how === 'download') {
    download(file, name);
  }
}
function download(blob, name) {
  const url = URL.createObjectURL(blob);
  const a = document.createElement('a');
  a.href = url;
  a.download = name;
  document.body.appendChild(a);
  a.click();
  a.remove();
  setTimeout(() => URL.revokeObjectURL(url), 60_000);
  markSaved(name);
}
function markSaved(name) {
  S.dirty = false;
  updateChrome();
  persistSoon();
  toast(`Gespeichert: ${name}`);
}

// ---------------------------------------------------------------- chrome & screens
function showStart() {
  $('#start').hidden = false;
  viewer.hidden = true;
  $('#pageGrid').hidden = true;
  $('#gridBar').hidden = true;
  $('#pageIndicator').hidden = true;
  $('#zoomCtl').hidden = true;
  $('#selBar').hidden = true;
  updateResumeBox();
  updateChrome();
}
function showDocument() {
  $('#start').hidden = true;
  if (S.tool === 'pages') { showGrid(); return; }
  viewer.hidden = false;
  $('#pageIndicator').hidden = false;
  $('#zoomCtl').hidden = false;
}
function updateChrome() {
  const has = S.pages.length > 0;
  $('#docTitle').textContent = has ? S.fileName : 'PDF Werkstatt';
  $('#docMeta').textContent = has
    ? `${S.pages.length} ${S.pages.length === 1 ? 'Seite' : 'Seiten'}${S.dirty ? ' · nicht gespeichert' : ''}`
    : 'Kein Dokument geöffnet';
  $('#btnUndo').disabled = !H.undo.length;
  $('#btnRedo').disabled = !H.redo.length;
  $('#btnSave').disabled = !has;
  for (const b of $$('#toolbar .tool')) b.disabled = !has;
  renderToolOpts();
  updateSelBar();
  if (S.tool === 'pages') updateGridBar();
  document.title = has ? `${S.fileName} – PDF Werkstatt` : 'PDF Werkstatt';
}
async function updateResumeBox() {
  const box = $('#resumeBox');
  box.hidden = true;
  const sess = await idb.get('state', 'session');
  if (!sess || !Array.isArray(sess.pages) || !sess.pages.length || S.pages.length) return;
  $('#resumeName').textContent = sess.fileName || 'Dokument';
  const d = new Date(sess.savedAt || Date.now());
  $('#resumeMeta').textContent = `${sess.pages.length} Seiten · ${pad2(d.getDate())}.${pad2(d.getMonth() + 1)}.${d.getFullYear()}, ${pad2(d.getHours())}:${pad2(d.getMinutes())}${sess.dirty ? ' · nicht gespeichert' : ''}`;
  box.hidden = false;
}

function openMenu() {
  const scrim = document.createElement('div');
  scrim.className = 'scrim menu-scrim';
  const m = document.createElement('div');
  m.className = 'menu';
  const item = (icon, label, fn, disabled = false) => {
    const b = document.createElement('button');
    b.type = 'button';
    b.disabled = disabled;
    b.innerHTML = `<svg><use href="#${icon}"/></svg>`;
    b.append(label);
    b.addEventListener('click', () => { scrim.remove(); fn(); });
    m.appendChild(b);
  };
  const has = S.pages.length > 0;
  item('i-open', 'PDF öffnen …', () => $('#fileOpen').click());
  item('i-doc', 'Beispiel ansehen', openSample);
  m.appendChild(document.createElement('hr'));
  item('i-save', 'Speichern …', saveFlow, !has);
  item('i-pages', 'Seiten verwalten', () => setTool('pages'), !has);
  item('i-close', 'Dokument schließen', closeDocument, !has);
  const foot = document.createElement('div');
  foot.className = 'mfoot';
  foot.textContent = `PDF Werkstatt · Stufe 1 · ${BUILD}`;
  m.appendChild(foot);
  scrim.appendChild(m);
  scrim.addEventListener('pointerdown', (e) => { if (e.target === scrim) scrim.remove(); });
  document.body.appendChild(scrim);
}

// ---------------------------------------------------------------- wiring
$('#btnMenu').addEventListener('click', openMenu);
$('#btnUndo').addEventListener('click', undo);
$('#btnRedo').addEventListener('click', redo);
$('#btnSave').addEventListener('click', saveFlow);
$('#btnOpenStart').addEventListener('click', () => $('#fileOpen').click());
$('#btnSample').addEventListener('click', openSample);
$('#btnResume').addEventListener('click', resumeSession);
$('#fileOpen').addEventListener('change', (e) => {
  const f = e.target.files && e.target.files[0];
  e.target.value = '';
  if (f) openFile(f);
});
for (const b of $$('#toolbar .tool')) b.addEventListener('click', () => setTool(b.dataset.tool));

document.addEventListener('keydown', (e) => {
  if (modalOpen) return;
  const typing = /^(INPUT|TEXTAREA)$/.test(document.activeElement?.tagName || '');
  const mod = e.metaKey || e.ctrlKey;
  if (mod && e.key.toLowerCase() === 'z') { e.preventDefault(); if (e.shiftKey) redo(); else undo(); return; }
  if (mod && e.key.toLowerCase() === 'y') { e.preventDefault(); redo(); return; }
  if (mod && e.key.toLowerCase() === 's') { e.preventDefault(); saveFlow(); return; }
  if (mod && e.key.toLowerCase() === 'o') { e.preventDefault(); $('#fileOpen').click(); return; }
  if (typing) return;
  if ((e.key === 'Delete' || e.key === 'Backspace') && S.sel) {
    e.preventDefault();
    const cur = selected();
    if (cur) deleteAnnot(cur.p, cur.a.id);
  }
  if (e.key === 'Escape' && S.sel) setSel(null);
});
// Datei auf das Fenster ziehen (Mac)
window.addEventListener('dragover', (e) => { if (e.dataTransfer && [...e.dataTransfer.types].includes('Files')) e.preventDefault(); });
window.addEventListener('drop', (e) => {
  const f = e.dataTransfer && [...e.dataTransfer.files].find((x) => /\.pdf$/i.test(x.name) || x.type === 'application/pdf');
  if (!f) return;
  e.preventDefault();
  openFile(f);
});
window.addEventListener('beforeunload', (e) => {
  if (S.dirty && S.pages.length) { persistNow(); e.preventDefault(); e.returnValue = ''; }
});
document.addEventListener('visibilitychange', () => { if (document.visibilityState === 'hidden') persistNow(); });

// ---------------------------------------------------------------- start
async function init() {
  $('#buildDate').textContent = BUILD;
  helvMeasure = await (await PDFDocument.create()).embedFont(StandardFonts.Helvetica);
  const standalone = window.matchMedia('(display-mode: standalone)').matches || navigator.standalone === true;
  const ios = /iPad|iPhone|iPod/.test(navigator.userAgent) || (navigator.platform === 'MacIntel' && navigator.maxTouchPoints > 1);
  if (TARGET === 'artifact') $('#artifactHint').hidden = false;
  else if (ios && !standalone) $('#installHint').hidden = false;
  if (TARGET !== 'artifact' && 'serviceWorker' in navigator) {
    navigator.serviceWorker.register('sw.js').catch(() => { /* ohne Offline-Speicher weiter */ });
  }
  try { if (navigator.storage && navigator.storage.persist) navigator.storage.persist(); } catch { /* egal */ }
  showStart();
}
init().catch(errorDialog);

// Für automatische Tests
window.__pdfw = { S, sources, buildPdf, layout, setTool, setZoom, undo, redo, openDocumentFromBytes };
