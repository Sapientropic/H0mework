// Builds one static 1200×630 page per figure (plus the default brand card) into .og/
// and automatically renders any missing or outdated public/og/<name>.png via headless Chrome.
// Each PNG carries an `og-sha256` tEXt chunk of its source HTML, so unchanged cards are skipped in <10ms.
import { spawn } from "node:child_process";
import { createHash } from "node:crypto";
import { existsSync, mkdirSync, mkdtempSync, readdirSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { homedir, tmpdir } from "node:os";
import { dirname, join, resolve } from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";
import { crc32 } from "node:zlib";

const HERE = dirname(fileURLToPath(import.meta.url));
process.chdir(join(HERE, ".."));
const { PAPERS } = await import("../src/lib/registry.ts");
const OUT = join(HERE, "../.og");
const PUBLIC_OG = join(HERE, "../public/og");
const FIGURES = [...new Set(PAPERS.flatMap((paper) => (paper.figure ? [paper.figure.name] : [])))];
const isoCss = readFileSync(join(HERE, "../figures/kit/iso.css"), "utf8");
const force = process.argv.includes("--force");
const htmlOnly = process.argv.includes("--html-only");

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

const KEY = "og-sha256\0";

function readOgSha(pngPath) {
  if (!existsSync(pngPath)) return null;
  const buf = readFileSync(pngPath);
  if (buf.length < 33 || buf.readUInt32BE(16) !== 1200 || buf.readUInt32BE(20) !== 630) return null;
  for (let offset = 8; offset + 12 <= buf.length; ) {
    const length = buf.readUInt32BE(offset);
    const type = buf.subarray(offset + 4, offset + 8).toString("ascii");
    const data = buf.subarray(offset + 8, offset + 8 + length);
    if (type === "tEXt" && data.subarray(0, KEY.length).toString("ascii") === KEY)
      return data.subarray(KEY.length).toString("ascii");
    offset += 12 + length;
  }
  return null;
}

function stampOgSha(buf, sha) {
  const payload = Buffer.from(`${KEY}${sha}`, "ascii");
  const body = Buffer.concat([Buffer.from("tEXt", "ascii"), payload]);
  const chunk = Buffer.alloc(12 + payload.length);
  chunk.writeUInt32BE(payload.length, 0);
  body.copy(chunk, 4);
  chunk.writeUInt32BE(crc32(body) >>> 0, 4 + body.length);
  const iend = buf.length - 12;
  return Buffer.concat([buf.subarray(0, iend), chunk, buf.subarray(iend)]);
}

function chromePath() {
  const candidates = [
    process.env.CHROME_PATH,
    "/Applications/Google Chrome.app/Contents/MacOS/Google Chrome",
    "/Applications/Chromium.app/Contents/MacOS/Chromium",
    "/Applications/Google Chrome Canary.app/Contents/MacOS/Google Chrome Canary",
    "/usr/bin/google-chrome",
    "/usr/bin/google-chrome-stable",
    "/usr/bin/chromium",
    "/usr/bin/chromium-browser",
  ].filter(Boolean);
  for (const base of [join(homedir(), "Library/Caches/ms-playwright"), join(homedir(), ".cache/ms-playwright")]) {
    if (!existsSync(base)) continue;
    for (const dir of readdirSync(base).sort().reverse()) {
      for (const sub of [
        "chrome-mac-arm64/Google Chrome for Testing.app/Contents/MacOS/Google Chrome for Testing",
        "chrome-mac/Chromium.app/Contents/MacOS/Chromium",
        "chrome-linux64/chrome",
        "chrome-linux/chrome",
      ])
        candidates.push(join(base, dir, sub));
    }
  }
  return candidates.find((candidate) => existsSync(candidate));
}

async function renderCards(cards) {
  const binary = chromePath();
  if (!binary) throw new Error(`No Chrome/Chromium found to render OG cards: ${cards.map((c) => c.name).join(", ")}`);
  const profile = mkdtempSync(join(tmpdir(), "h0-og-"));
  const chrome = spawn(binary, [
    "--headless=new",
    ...(process.platform === "linux" ? ["--no-sandbox"] : []),
    "--remote-debugging-port=0",
    `--user-data-dir=${profile}`,
    "--no-first-run",
    "--no-default-browser-check",
    "--hide-scrollbars",
    "--allow-file-access-from-files",
    "--enable-unsafe-swiftshader",
    "--ignore-gpu-blocklist",
    "about:blank",
  ]);
  try {
    const port = await new Promise((done, fail) => {
      let stderr = "";
      const timer = setTimeout(() => fail(new Error("Chrome did not start within 20s")), 20000);
      chrome.stderr.on("data", (chunk) => {
        stderr += chunk;
        const match = stderr.match(/DevTools listening on ws:\/\/[^:]+:(\d+)\//);
        if (match) {
          clearTimeout(timer);
          done(Number(match[1]));
        }
      });
      chrome.on("error", (err) => {
        clearTimeout(timer);
        fail(err);
      });
    });
    const target = await (await fetch(`http://127.0.0.1:${port}/json/new?about:blank`, { method: "PUT" })).json();
    const socket = new WebSocket(target.webSocketDebuggerUrl);
    let callId = 0;
    const pending = new Map();
    let onLoad = () => {};
    socket.onmessage = (event) => {
      const msg = JSON.parse(event.data);
      if (msg.method === "Page.loadEventFired") onLoad();
      if (msg.id && pending.has(msg.id)) {
        pending.get(msg.id)(msg);
        pending.delete(msg.id);
      }
    };
    await new Promise((done) => (socket.onopen = done));
    const send = (method, params = {}) =>
      new Promise((done, fail) => {
        const id = ++callId;
        const timer = setTimeout(() => {
          pending.delete(id);
          fail(new Error(`CDP timeout on ${method}`));
        }, 30000);
        pending.set(id, (res) => {
          clearTimeout(timer);
          if (res.error) fail(new Error(`${method}: ${res.error.message}`));
          else done(res.result);
        });
        socket.send(JSON.stringify({ id, method, params }));
      });
    await send("Page.enable");
    await send("Emulation.setDeviceMetricsOverride", { width: 1200, height: 630, deviceScaleFactor: 1, mobile: false });
    for (const card of cards) {
      const loaded = new Promise((done) => {
        onLoad = done;
        setTimeout(done, 5000);
      });
      await send("Page.navigate", { url: pathToFileURL(resolve(card.htmlPath)).href });
      await loaded;
      await new Promise((done) => setTimeout(done, 150));
      const shot = await send("Page.captureScreenshot", {
        format: "png",
        captureBeyondViewport: true,
        clip: { x: 0, y: 0, width: 1200, height: 630, scale: 1 },
      });
      const stamped = stampOgSha(Buffer.from(shot.data, "base64"), card.sha);
      writeFileSync(card.pngPath, stamped);
      console.log(`rendered public/og/${card.name}.png (1200×630, ${card.sha.slice(0, 12)})`);
    }
    socket.close();
  } finally {
    chrome.kill("SIGKILL");
    try {
      rmSync(profile, { recursive: true, force: true });
    } catch {}
  }
}

mkdirSync(OUT, { recursive: true });
mkdirSync(PUBLIC_OG, { recursive: true });

// Default card: the punch-tape brand mark, for pages without a figure.
const tape = `<svg width="560" height="300" viewBox="0 0 560 300">
  <rect x="30" y="60" width="500" height="180" rx="10" fill="#fffef9" stroke="#18181a" stroke-width="5"/>
  ${[0, 1, 2, 3, 4].map((row) => `<line x1="46" y1="${108 + row * 27}" x2="514" y2="${108 + row * 27}" stroke="#e9e9e5" stroke-width="3"/>`).join("")}
  ${[110, 210, 280, 350, 450].map((x, i) => `<circle cx="${x}" cy="150" r="26" fill="${i === 2 ? "#c8372d" : "#18181a"}"/>`).join("")}
</svg>`;

const entries = [
  ...FIGURES.map((name) => {
    const figure = JSON.parse(readFileSync(join(HERE, `../src/generated/${name}.json`), "utf8"));
    return { name, html: page(`<div class="art"><style>${figure.css}</style>${figure.html.zh}</div>`) };
  }),
  { name: "default", html: page(`<div class="art">${tape}</div>`) },
];

const stale = [];
for (const { name, html } of entries) {
  const htmlPath = join(OUT, `${name}.html`);
  const pngPath = join(PUBLIC_OG, `${name}.png`);
  const sha = createHash("sha256").update(html).digest("hex");
  writeFileSync(htmlPath, html);
  if (force || readOgSha(pngPath) !== sha) stale.push({ name, htmlPath, pngPath, sha });
}

if (htmlOnly) {
  console.log(`wrote ${entries.length} .og/*.html pages`);
} else if (stale.length === 0) {
  console.log(`og: all ${entries.length} cards up to date`);
} else {
  await renderCards(stale);
}
