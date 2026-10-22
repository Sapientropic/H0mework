// Builds one static 1200×630 page per figure (plus a default brand page) into .og/.
// The pages are screenshotted by hand to produce the committed og images:
//   bun scripts/og.mjs
//   bunx serve .og            # or python3 -m http.server -d .og
//   # capture each page at exactly 1200×630 → public/og/<name>.png
import { mkdirSync, readFileSync, writeFileSync } from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";

const HERE = dirname(fileURLToPath(import.meta.url));
const OUT = join(HERE, "../.og");
const FIGURES = ["source-tape", "pairing-balance", "current-witness", "curvature-dome", "ghost-register", "whole-ledger-tower"];
const isoCss = readFileSync(join(HERE, "../figures/kit/iso.css"), "utf8");

const PAGE_CSS = `
  html, body { margin: 0; }
  body { width: 1200px; height: 630px; overflow: hidden; }
  .og { position: relative; width: 1200px; height: 630px; box-sizing: border-box; background: #fbfbfa; display: flex; align-items: center; justify-content: center; }
  .brand { position: absolute; top: 44px; left: 52px; font: 600 27px/1 ui-monospace, "SF Mono", Menlo, monospace; letter-spacing: .06em; color: #18181a; }
  .brand b { color: #c8372d; font-weight: 600; }
  .art { width: 880px; }
  .art .iso-figure { margin: 0; }
  .art .iso-plate { background: transparent; box-shadow: none; padding: 0; }
  .art .iso-plate-corners, .art .iso-legend { display: none; }
  .art .iso-svg { width: 100%; height: auto; max-height: 450px; margin: 0 auto; }
  .holes { position: absolute; right: 56px; bottom: 44px; display: flex; gap: 18px; }
  .holes i { width: 15px; height: 15px; border-radius: 50%; background: #18181a; }
  .holes i.red { background: #c8372d; }
`;

const page = (inner) => `<!doctype html>
<meta charset="utf-8">
<style>${isoCss}${PAGE_CSS}</style>
<body><div class="iso" data-theme="light"><div class="og">
  <div class="brand">H<b>0</b>mework</div>
  ${inner}
  <div class="holes"><i></i><i class="red"></i><i></i></div>
</div></div></body>`;

mkdirSync(OUT, { recursive: true });
for (const name of FIGURES) {
  const figure = JSON.parse(readFileSync(join(HERE, `../src/generated/${name}.json`), "utf8"));
  writeFileSync(join(OUT, `${name}.html`), page(`<div class="art"><style>${figure.css}</style>${figure.html.zh}</div>`));
  console.log(`wrote .og/${name}.html`);
}

// Default card: the punch-tape brand mark, for pages without a figure.
const tape = `<svg width="560" height="300" viewBox="0 0 560 300">
  <rect x="30" y="60" width="500" height="180" rx="10" fill="#fffef9" stroke="#18181a" stroke-width="5"/>
  ${[0, 1, 2, 3, 4].map((row) => `<line x1="46" y1="${108 + row * 27}" x2="514" y2="${108 + row * 27}" stroke="#e9e9e5" stroke-width="3"/>`).join("")}
  ${[110, 210, 280, 350, 450].map((x, i) => `<circle cx="${x}" cy="150" r="26" fill="${i === 2 ? "#c8372d" : "#18181a"}"/>`).join("")}
</svg>`;
writeFileSync(join(OUT, "default.html"), page(`<div class="art">${tape}</div>`));
console.log("wrote .og/default.html");
console.log("capture each at 1200×630 into public/og/<name>.png");
