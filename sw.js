// Offline-Speicher der PDF Werkstatt: alle App-Dateien werden beim ersten Start gesichert.
const VERSION = 'pdfw-2cf4f2acb222';
const ASSETS = [
 "./",
 "./app.css",
 "./app.js",
 "./icons/icon-180.png",
 "./icons/icon-192.png",
 "./icons/icon-512.png",
 "./icons/icon-maskable-512.png",
 "./index.html",
 "./lib/LICENSE_pdf-lib.txt",
 "./lib/LICENSE_pdfjs.txt",
 "./lib/iccs/CGATS001Compat-v2-micro.icc",
 "./lib/iccs/LICENSE",
 "./lib/pdf-lib.js",
 "./lib/pdf.min.js",
 "./lib/pdf.worker.js",
 "./lib/standard_fonts/FoxitDingbats.pfb",
 "./lib/standard_fonts/FoxitFixed.pfb",
 "./lib/standard_fonts/FoxitFixedBold.pfb",
 "./lib/standard_fonts/FoxitFixedBoldItalic.pfb",
 "./lib/standard_fonts/FoxitFixedItalic.pfb",
 "./lib/standard_fonts/FoxitSerif.pfb",
 "./lib/standard_fonts/FoxitSerifBold.pfb",
 "./lib/standard_fonts/FoxitSerifBoldItalic.pfb",
 "./lib/standard_fonts/FoxitSerifItalic.pfb",
 "./lib/standard_fonts/FoxitSymbol.pfb",
 "./lib/standard_fonts/LICENSE_FOXIT",
 "./lib/standard_fonts/LICENSE_LIBERATION",
 "./lib/standard_fonts/LiberationSans-Bold.ttf",
 "./lib/standard_fonts/LiberationSans-BoldItalic.ttf",
 "./lib/standard_fonts/LiberationSans-Italic.ttf",
 "./lib/standard_fonts/LiberationSans-Regular.ttf",
 "./lib/wasm/LICENSE_JBIG2",
 "./lib/wasm/LICENSE_OPENJPEG",
 "./lib/wasm/LICENSE_PDFJS_JBIG2",
 "./lib/wasm/LICENSE_PDFJS_OPENJPEG",
 "./lib/wasm/LICENSE_PDFJS_QCMS",
 "./lib/wasm/LICENSE_QCMS",
 "./lib/wasm/jbig2.wasm",
 "./lib/wasm/jbig2_nowasm_fallback.js",
 "./lib/wasm/openjpeg.wasm",
 "./lib/wasm/openjpeg_nowasm_fallback.js",
 "./lib/wasm/qcms_bg.wasm",
 "./lib/wasm/quickjs-eval.js",
 "./lib/wasm/quickjs-eval.wasm",
 "./manifest.webmanifest",
 "./scan.js"
];

self.addEventListener('install', (event) => {
  event.waitUntil(
    caches.open(VERSION)
      .then((cache) => cache.addAll(ASSETS.map((u) => new Request(u, { cache: 'reload' }))))
      .then(() => self.skipWaiting()),
  );
});

self.addEventListener('activate', (event) => {
  event.waitUntil(
    caches.keys()
      .then((keys) => Promise.all(keys.filter((k) => k.startsWith('pdfw-') && k !== VERSION).map((k) => caches.delete(k))))
      .then(() => self.clients.claim()),
  );
});

self.addEventListener('fetch', (event) => {
  const req = event.request;
  if (req.method !== 'GET') return;
  const url = new URL(req.url);
  if (url.origin !== self.location.origin) return;
  event.respondWith((async () => {
    const cache = await caches.open(VERSION);
    const hit = await cache.match(req, { ignoreSearch: true });
    if (hit) return hit;
    try {
      const res = await fetch(req);
      if (res.ok && res.type === 'basic') cache.put(req, res.clone());
      return res;
    } catch (err) {
      if (req.mode === 'navigate') {
        const page = await cache.match('./index.html');
        if (page) return page;
      }
      throw err;
    }
  })());
});
