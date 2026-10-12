// Fig: an equal-arm balance for the classical–quantum pairing (Theorem 6.2, Example 6.6).
//   bun build.mjs [--light]   → out/pairing-balance[-light].html (standalone, for checks)
//   bun build.mjs --fragment  → ../../src/generated/pairing-balance.json (for the site)
import { mkdirSync, readFileSync, writeFileSync } from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";
import * as k from "../kit/iso-kit.mjs";
import * as G from "../kit/lathe.mjs";
import { balance, classicalCurrent } from "./model.mjs";

const HERE = dirname(fileURLToPath(import.meta.url));
const theme = process.argv.includes("--light") ? "light" : "dark";
const fragment = process.argv.includes("--fragment");

const WIDTH = 640;
const HEIGHT = 420;

const PLATE = { x: -104, y: -50, w: 208, d: 104, r: 8 };
const PLATE_H = 10;
const FOOT_H = 5;

const PLINTH = [{ plan: { x: -24, y: -18, w: 48, d: 36, r: 3 }, z: 0, h: 6 }, { plan: { x: -16, y: -12, w: 32, d: 24, r: 2 }, z: 6, h: 5 }];
const PILLAR = { r: 4.5, z0: 11, z1: 116 };
const PIVOT = [0, 0, 127];
const BEAM = { half: 76, arm: 72, y: 2.2, v: 3 };
const DROP = 54; // hook to pan
const PAN = { r: 19, h: 2.4 };
const TILT = (12 * Math.PI) / 180; // beam angle when the pans differ by 2J
const NEEDLE = { at: [0, 8, 125], length: 42 };
const SCALE = { y: 5.8, r0: 39.5, r1: 43.4 };
const CLOCK = { at: [-66, 30], r: 13, h: 5 };
const SWITCH = { x: 34, y: 26, w: 42, d: 10, r: 2, on: 47, off: 69 };
const LEVEL = [-36, 34];

const P = k.fitProjection(
  [...k.boxCorners(PLATE, -PLATE_H - FOOT_H, 0), [-BEAM.half - 4, 0, PIVOT[2] + 20], [BEAM.half + 4, 0, PIVOT[2] + 20], [0, 0, PIVOT[2] + 12]],
  WIDTH,
  HEIGHT,
  { pad: 26, azimuth: 90 },
);

const at = (point) => k.iso(point, P);
const S = (paths, style) => k.solidSvg(paths, style);
const L = (d, style) => k.lineSvg(d, style);
const D = (points, style) => k.dotsSvg(points, style);
const byDepth = (items, key = (item) => item) => [...items].sort((a, b) => k.depthOf([...key(a).slice(0, 2), 0], P) - k.depthOf([...key(b).slice(0, 2), 0], P));
const UP = (() => {
  let best = 0, high = Infinity;
  for (let step = 0; step < 720; step++) {
    const angle = (step / 720) * Math.PI * 2;
    const y = k.iso([Math.sin(angle), -Math.cos(angle), 0], P)[1];
    if (y < high) { high = y; best = angle; }
  }
  return best;
})();

// --- shared with the page: everything that moves is computed from the beam angle φ ----------

// φ > 0 raises the right (quantum) end. Beam axis a = (cos φ, 0, sin φ), up-normal v = (−sin φ, 0, cos φ).
const beamFrame = (G, phi) => G.frameOf(PIVOT, [Math.cos(phi), 0, Math.sin(phi)], [0, 1, 0], [-Math.sin(phi), 0, Math.cos(phi)]);
const hookOf = (phi, side) => {
  const s = side * BEAM.arm;
  return [PIVOT[0] + s * Math.cos(phi) + BEAM.v * Math.sin(phi), 0, PIVOT[2] + s * Math.sin(phi) - BEAM.v * Math.cos(phi) - 3];
};
const panTop = (phi, side) => { const h = hookOf(phi, side); return [h[0], 0, h[2] - DROP + PAN.h]; };
const STRING_ANGLES = [0, (2 * Math.PI) / 3, (4 * Math.PI) / 3];
const strings = (kit, P, phi, side, front) => {
  const h = hookOf(phi, side), top = panTop(phi, side);
  return STRING_ANGLES.map((angle) => [top[0] + Math.sin(angle) * (PAN.r - 1.5), -Math.cos(angle) * (PAN.r - 1.5), top[2]])
    .filter((rim) => (rim[1] > 0) === front)
    .map((rim) => kit.wireSvg(kit.iso(h, P), kit.iso(rim, P), { ends: "to", size: 0.7, tone: "mid" }))
    .join("");
};
const beamSvg = (kit, G, P, phi) => {
  const F = beamFrame(G, phi);
  const section = [[-BEAM.y, -BEAM.v], [BEAM.y, -BEAM.v], [BEAM.y, BEAM.v * 0.7], [BEAM.y * 0.6, BEAM.v], [-BEAM.y * 0.6, BEAM.v], [-BEAM.y, BEAM.v * 0.7]];
  const out = [kit.solidSvg(G.prismOf(F, section, -BEAM.half, BEAM.half, P), { tone: "hi", lit: true })];
  for (const side of [-1, 1]) {
    const tip = [PIVOT[0] + side * BEAM.arm * Math.cos(phi) + BEAM.v * Math.sin(phi), 0, PIVOT[2] + side * BEAM.arm * Math.sin(phi) - BEAM.v * Math.cos(phi)];
    const hook = hookOf(phi, side);
    out.push(kit.lineSvg(kit.pathOf([kit.iso(tip, P), kit.iso(hook, P)]), { tone: "mid" }));
    out.push(kit.dotsSvg([kit.iso(hook, P)], { size: 0.9, tone: "hi" }));
  }
  return out.join("");
};
const needleD = (kit, P, phi) => {
  const [x, y, z] = NEEDLE.at;
  return kit.pathOf([kit.iso([x, y, z], P), kit.iso([x + Math.sin(phi) * NEEDLE.length, y, z - Math.cos(phi) * NEEDLE.length], P)]);
};
const pointerOnTop = (kit, P, [x, y], angle, from, to, z) =>
  kit.lineOnTop([x + Math.sin(angle) * from, y - Math.cos(angle) * from], [x + Math.sin(angle) * to, y - Math.cos(angle) * to], z, P);

// --- static art ------------------------------------------------------------------------------

function plate() {
  const out = [`<path class="iso-halo" d="${k.haloOf(PLATE, -PLATE_H - FOOT_H, PLATE_H, P)}"/>`];
  for (const [x, y] of byDepth(k.corners(PLATE, 20))) {
    out.push(S(k.cylinder(x, y, 7.5, -PLATE_H - FOOT_H, 1.6, P, 28), { tone: "lo" }));
    out.push(S(k.cylinder(x, y, 5.6, -PLATE_H - FOOT_H + 1.6, FOOT_H - 1.6, P, 28), { tone: "mid" }));
    out.push(L(k.knurl(x, y, 5.6, -PLATE_H - FOOT_H + 1.6, -PLATE_H, 20, P), { tone: "lo" }));
  }
  out.push(S(k.slabOf(PLATE, -PLATE_H, PLATE_H, P, 8, 1.6), { tone: "mid", inner: L(k.sideSeam(PLATE, -4, P, 8), { tone: "faint" }) }));
  out.push(L(k.planOutline(k.insetPlan(PLATE, 5), 0, P), { tone: "lo" }));
  const screws = k.corners(PLATE, 10);
  out.push(L(screws.map(([x, y]) => k.ring(x, y, 2.2, 0, P, 16)).join(""), { tone: "lo" }));
  out.push(D(screws.map(([x, y]) => at([x, y, 0])), { size: 0.5 }));
  const strip = { x: -46, y: PLATE.y + PLATE.d - 11, w: 122, d: 5.5, r: 1 };
  out.push(S(k.slabOf(strip, 0, 0.6, P, 3), { tone: "lo", crease: "none" }));
  const ticks = k.topTicks(strip.x + 4, strip.x + strip.w - 4, 4, 5, strip.y + 0.8, 0.6, [1.6, 3], P);
  out.push(L(ticks.minor, { tone: "lo" }), L(ticks.major, { tone: "mid" }));
  out.push(D([at([strip.x + 2, strip.y + 2.75, 0.6]), at([strip.x + strip.w - 2, strip.y + 2.75, 0.6])], { size: 0.45 }));
  return out.join("");
}

function plinth() {
  const out = [`<path class="iso-halo" d="${k.haloOf(PLINTH[0].plan, 0, 11, P)}" style="filter:blur(5px)"/>`];
  for (const { plan, z, h } of PLINTH) {
    out.push(S(k.slabOf(plan, z, h, P, 4, 0.6), { tone: "mid" }));
    out.push(D(k.corners(plan, 2.6).map(([x, y]) => at([x, y, z + h])), { size: 0.45 }));
  }
  return out.join("");
}

function pillar() {
  const out = [];
  out.push(S(k.cylinder(0, 0, 7, PILLAR.z0, 3, P, 32, 0.4), { tone: "mid" }));
  out.push(S(k.cylinder(0, 0, PILLAR.r, PILLAR.z0 + 3, 57 - PILLAR.z0 - 3, P, 28), { tone: "mid", crease: "none" }));
  out.push(S(k.cylinder(0, 0, 5.8, 57, 3, P, 28, 0.3), { tone: "mid" }));
  out.push(S(k.cylinder(0, 0, PILLAR.r, 60, PILLAR.z1 - 60, P, 28), { tone: "mid", crease: "none" }));
  out.push(L([30, 45, 96].map((z) => k.sideArc(0, 0, PILLAR.r, z, P, 16)).join(""), { tone: "faint" }));
  out.push(S(k.cylinder(0, 0, 6.4, PILLAR.z1 - 4, 4, P, 28, 0.4), { tone: "mid" }));
  out.push(S(k.slabOf({ x: -6, y: -5, w: 12, d: 10, r: 1.5 }, PILLAR.z1, PIVOT[2] - BEAM.v - PILLAR.z1, P, 3, 0.5), { tone: "mid" }));
  // Beam arrest: a knurled knob on the plinth front.
  out.push(S(k.slabOf({ x: -3, y: 10, w: 6, d: 3, r: 0.8 }, 6, 3, P, 2), { tone: "mid", crease: "none" }));
  out.push(S(k.cylinder(0, 14.5, 3.2, 6, 4.5, P, 24), { tone: "mid" }));
  out.push(L(k.knurl(0, 14.5, 3.2, 6, 10.5, 22, P), { tone: "lo" }));
  return out.join("");
}

// The tilt scale: a plate on the pillar's front, its ticks hanging from a printed arc.
function scale() {
  const [nx, , nz] = NEEDLE.at;
  const plate = { x: -15, y: SCALE.y - 1.6, w: 30, d: 1.6, r: 0.4 };
  const z0 = nz - SCALE.r1 - 2.6, z1 = nz - SCALE.r0 + 5;
  const out = [S(k.slabOf(plate, z0, z1 - z0, P, 1, 0.2), { tone: "mid" })];
  const y = SCALE.y + 0.05;
  const onFace = (angle, r) => [nx + Math.sin(angle) * r, y, nz - Math.cos(angle) * r];
  const arc = [];
  for (let step = 0; step <= 40; step++) arc.push(at(onFace(-TILT + (2 * TILT * step) / 40, SCALE.r0)));
  out.push(L(k.pathOf(arc), { tone: "lo" }));
  const minor = [], major = [];
  for (let index = -4; index <= 4; index++) {
    const angle = (TILT * index) / 4;
    (index % 2 ? minor : major).push(k.pathOf([at(onFace(angle, SCALE.r0)), at(onFace(angle, index % 2 ? SCALE.r0 + 1.4 : SCALE.r0 + 2.4))]));
  }
  out.push(L(minor.join(""), { tone: "lo" }), L(major.join(""), { tone: "mid" }));
  out.push(L(k.pathOf([at(onFace(0, SCALE.r0)), at(onFace(0, SCALE.r0 + 3.2))]), { tone: "hi" }));
  out.push(D([at([plate.x + 2, y, z0 + 2]), at([plate.x + plate.w - 2, y, z0 + 2])], { size: 0.4 }));
  return out.join("");
}

function pan(side) {
  const x = side * BEAM.arm, top = panTop(0, side);
  const out = [];
  out.push(S(k.cylinder(x, 0, PAN.r, top[2] - PAN.h, PAN.h, P, 64, 0.6), { tone: "mid" }));
  out.push(L(k.ring(x, 0, PAN.r - 2.4, top[2], P, 56), { tone: "faint" }));
  return out.join("");
}

// The classical pan: brass weights standing for J.
function weights() {
  const x = -BEAM.arm, z = panTop(0, -1)[2];
  const set = [{ at: [x - 5, -3], r: 6.5, h: 9 }, { at: [x + 7, 5], r: 4.4, h: 6 }, { at: [x + 6, -9], r: 2.8, h: 4 }];
  return byDepth(set, (w) => w.at).map(({ at: [wx, wy], r, h }) => [
    S(k.cylinder(wx, wy, r, z, h, P, 32, 0.4), { tone: "hi" }),
    S(k.cylinder(wx, wy, r * 0.42, z + h, r * 0.25, P, 18), { tone: "mid" }),
    S(k.cylinder(wx, wy, r * 0.62, z + h + r * 0.25, r * 0.5, P, 22), { tone: "hi" }),
  ].join("")).join("");
}

// The quantum pan: the occupied state's two phases, the upper on the outer ring, the lower inside.
function statePuck() {
  const x = BEAM.arm, z = panTop(0, 1)[2];
  return [
    S(k.cylinder(x, 0, 11, z, 3, P, 48, 0.5), { tone: "mid" }),
    L(k.knurl(x, 0, 11, z, z + 3, 56, P), { tone: "lo" }),
    S(k.cylinder(x, 0, 10, z + 3, 1.2, P, 48), { tone: "hi" }),
    S(k.cylinder(x, 0, 5.4, z + 4.2, 1.6, P, 32, 0.3), { tone: "mid" }),
    `<path data-part="phase-upper" class="iso-line" data-tone="hi" data-free="start" d="" style="stroke-width:1"/>`,
    `<path data-part="phase-lower" class="iso-line" data-tone="hi" data-free="start" d="" style="stroke-width:1"/>`,
  ].join("");
}

function clock() {
  const [x, y] = CLOCK.at;
  const top = CLOCK.h + 1;
  const out = [S(k.cylinder(x, y, CLOCK.r, 0, CLOCK.h, P, 56, 0.6), { tone: "mid" })];
  out.push(L(k.knurl(x, y, CLOCK.r, CLOCK.h - 2, CLOCK.h, 56, P, 0.3), { tone: "lo" }));
  out.push(S(k.cylinder(x, y, CLOCK.r - 1.6, CLOCK.h, 1, P, 56), { tone: "hi", crease: "none" }));
  const ticks = [];
  for (let index = 0; index < 8; index++) ticks.push({ dark: index % 4 === 2, d: pointerOnTop(k, P, [x, y], UP + (index * Math.PI) / 4, CLOCK.r - (index % 4 === 2 ? 5.6 : 4.6), CLOCK.r - 2.8, top) });
  out.push(L(k.ring(x, y, CLOCK.r - 2.8, top, P, 48), { tone: "lo" }));
  out.push(L(ticks.filter((t) => !t.dark).map((t) => t.d).join(""), { tone: "mid" }), L(ticks.filter((t) => t.dark).map((t) => t.d).join(""), { tone: "hi" }));
  out.push(L(k.ring(x, y, 1.1, top, P, 12), { tone: "mid" }));
  out.push(`<path data-part="clock" class="iso-line" data-tone="hi" data-free="start" d="" style="stroke-width:1"/>`);
  return out.join("");
}

function level() {
  const [x, y] = LEVEL;
  return [S(k.cylinder(x, y, 4.6, 0, 1.6, P, 28, 0.3), { tone: "mid" }), L(k.ring(x, y, 2.2, 1.6, P, 20), { tone: "lo" }), D([at([x, y, 1.6])], { size: 0.9, tone: "hi" })].join("");
}

function switchPlate() {
  const plan = { x: SWITCH.x, y: SWITCH.y, w: SWITCH.w, d: SWITCH.d, r: SWITCH.r };
  const out = [S(k.slabOf(plan, 0, 3, P, 3, 0.5), { tone: "mid" })];
  const slot = { x: SWITCH.on - 2, y: SWITCH.y + SWITCH.d / 2 - 1.2, w: SWITCH.off - SWITCH.on + 4, d: 2.4, r: 1.2 };
  out.push(L(k.planOutline(slot, 3, P, 4), { tone: "lo" }));
  out.push(D([SWITCH.on, SWITCH.off].map((sx) => at([sx, SWITCH.y + 2.2, 3])), { size: 0.5, tone: "mid" }));
  out.push(k.faceTextSvg(k.topMatrix([SWITCH.x + 2.4, SWITCH.y + SWITCH.d - 2], 3, P), "S", { size: 4.4, tone: "hi" }));
  out.push(D([at([plan.x + plan.w - 2.2, plan.y + 2.2, 3]), at([plan.x + plan.w - 2.2, plan.y + plan.d - 2.2, 3])], { size: 0.4 }));
  return out.join("");
}

function switchKnob() {
  const y = SWITCH.y + SWITCH.d / 2;
  return [S(k.cylinder(0, y, 1.2, 3, 2, P, 14), { tone: "mid" }), S(k.cylinder(0, y, 3.2, 5, 4, P, 26), { tone: "hi" }), L(k.knurl(0, y, 3.2, 5, 9, 22, P), { tone: "lo" })].join("");
}

const kitLocal = { lineOnTop: k.lineOnTop, solidSvg: k.solidSvg, lineSvg: k.lineSvg, dotsSvg: k.dotsSvg, wireSvg: k.wireSvg, pathOf: k.pathOf, iso: k.iso };
const panGroup = (side, inner) => `<g data-part="pan-${side < 0 ? "left" : "right"}">${inner}</g>`;
const side = (sideSign) => [
  `<g data-part="strings-back-${sideSign < 0 ? "left" : "right"}">${strings(kitLocal, P, 0, sideSign, false)}</g>`,
  panGroup(sideSign, pan(sideSign) + (sideSign < 0 ? weights() : statePuck())),
  `<g data-part="strings-front-${sideSign < 0 ? "left" : "right"}">${strings(kitLocal, P, 0, sideSign, true)}</g>`,
].join("");

const svg = k.figureSvg({
  width: WIDTH,
  height: HEIGHT,
  className: "pb-svg",
  label:
    "An equal-arm balance. The left pan holds brass weights: the classical current J, computed by hand. The right pan holds the quantum state, two discs whose phases turn in opposite directions. A slide marked S on the base chooses whether the quantum side is read with the independent dual's exchange. With S in, the beam stays level at every time; with S out, it tips as time runs and falls fully to the classical side at the dark moment.",
  body: [
    plate(),
    plinth(),
    level(),
    pillar(),
    scale(),
    // Pan shadows stay on the floor while the pans ride up and down.
    ...[-1, 1].map((sign) => `<path class="iso-halo" d="${k.haloOf({ x: sign * BEAM.arm - PAN.r + 4, y: -PAN.r + 4, w: 2 * PAN.r - 8, d: 2 * PAN.r - 8, r: PAN.r - 4 }, 0, 0.2, P)}" style="filter:blur(8px);opacity:calc(var(--anatomy-halo-opacity) * .45)"/>`),
    ...byDepth([[-1, -BEAM.arm], [1, BEAM.arm]], (item) => [item[1], 0]).map(([sign]) => side(sign)),
    `<g data-part="beam">${beamSvg(kitLocal, G, P, 0)}</g>`,
    S(G.disc(-3, NEEDLE.at[1], 4.2, G.frameAlong(PIVOT, [0, 1, 0]), P), { tone: "mid" }),
    `<path data-part="needle" class="iso-line" data-tone="hi" data-free="end" d="${needleD(kitLocal, P, 0)}" style="stroke-width:1.1"/>`,
    D([at(NEEDLE.at)], { size: 1.1, tone: "hi" }),
    clock(),
    switchPlate(),
    `<g data-part="knob" transform="${k.translateAlong(P, [SWITCH.on, 0, 0])}">${switchKnob()}</g>`,
  ],
});

const CSS = `
.iso-stage{outline:none;cursor:pointer;touch-action:pan-y}
.iso-stage:focus-visible{box-shadow:0 0 0 1px var(--anatomy-mid)}
@media (max-width:560px){.iso-plate:has(.pb-svg){overflow:hidden}.pb-svg.iso-svg{width:116%;max-width:none;margin:0 -8%}}
`;

const strip = (file) => readFileSync(join(HERE, file), "utf8").replace(/^export /gm, "");
const kitSource = strip("../kit/iso-kit.mjs");
// lathe.mjs shares a few helper names with the core, so it lives in its own scope.
const latheSource = `const LATHE = (() => {\n${strip("../kit/lathe.mjs").replace(/^import .*$/gm, "")}\nreturn { prismOf, frameOf };\n})();`;
const modelSource = strip("model.mjs");
const live = `
const P = ${JSON.stringify(P)};
const PIVOT = ${JSON.stringify(PIVOT)}, BEAM = ${JSON.stringify(BEAM)}, DROP = ${DROP}, PAN = ${JSON.stringify(PAN)}, TILT = ${TILT};
const NEEDLE = ${JSON.stringify(NEEDLE)}, CLOCK = ${JSON.stringify(CLOCK)}, SWITCH = ${JSON.stringify(SWITCH)}, UP = ${UP};
const STRING_ANGLES = ${JSON.stringify(STRING_ANGLES)};
const kit = { lineOnTop, solidSvg, lineSvg, dotsSvg, wireSvg, pathOf, iso };
const G = LATHE;
const beamFrame = ${beamFrame.toString()};
const hookOf = ${hookOf.toString()};
const panTop = ${panTop.toString()};
const strings = ${strings.toString()};
const beamSvg = ${beamSvg.toString()};
const needleD = ${needleD.toString()};
const pointerOnTop = ${pointerOnTop.toString()};
const root = document.querySelector('[data-figure="pairing-balance"]');
const stage = root.querySelector(".iso-stage");
const part = (name) => stage.querySelector('[data-part="' + name + '"]');
const readout = root.querySelector("[data-readout]");
const still = matchMedia("(prefers-reduced-motion: reduce)");
const BEAM_AT = PIVOT, J = classicalCurrent;
let u = 1, withS = true, phi = 0, rate = 0, knobX = SWITCH.on, clock = 0;
let touring = !still.matches, visible = false, frame = 0, last = 0, idle = 0, target = null;
// Idle tour: time runs; every 9 s the slide flips, so the beam alternates level and swinging.
const tourS = (t) => Math.floor(t / 9) % 2 === 0;
const fmt = (x) => { const r = Math.round(x * 1000) / 1000 || 0; return (r < 0 ? "−" : "") + Math.abs(r).toFixed(3); };
function draw(dt) {
  const b = balance(u, withS);
  const want = (TILT * b.gap) / (2 * J);
  if (still.matches || !dt) { phi = want; rate = 0; }
  else for (let i = 0; i < 4; i++) { rate += ((want - phi) * 40 - rate * 7) * dt / 4; phi += rate * dt / 4; }
  part("beam").innerHTML = beamSvg(kit, G, P, phi);
  part("needle").setAttribute("d", needleD(kit, P, phi));
  for (const [sign, name] of [[-1, "left"], [1, "right"]]) {
    const top = panTop(phi, sign), rest = panTop(0, sign);
    part("pan-" + name).setAttribute("transform", translateAlong(P, [top[0] - rest[0], 0, top[2] - rest[2]]));
    part("strings-back-" + name).innerHTML = strings(kit, P, phi, sign, false);
    part("strings-front-" + name).innerHTML = strings(kit, P, phi, sign, true);
  }
  const z = panTop(0, 1)[2] + 4.2;
  part("phase-upper").setAttribute("d", pointerOnTop(kit, P, [BEAM.arm, 0], UP + b.theta, 6.4, 9.6, z - 1.2 + 0.05));
  part("phase-lower").setAttribute("d", pointerOnTop(kit, P, [BEAM.arm, 0], UP - b.theta, 0, 4.4, z + 1.6));
  part("clock").setAttribute("d", pointerOnTop(kit, P, CLOCK.at, UP + (u * Math.PI) / 2, -2, CLOCK.r - 2.8, CLOCK.h + 1.05));
  knobX = still.matches || !dt ? SWITCH[withS ? "on" : "off"] : knobX + (SWITCH[withS ? "on" : "off"] - knobX) * (1 - Math.exp(-dt / 0.15));
  part("knob").setAttribute("transform", translateAlong(P, [knobX, 0, 0]));
  const shown = (u % 4).toFixed(2);
  const text = "u " + shown + " · " + (withS ? root.dataset.with : root.dataset.without) + " · " + root.dataset.classical + " " + fmt(b.classical) + " · " + root.dataset.quantum + " " + fmt(b.quantum);
  if (readout.textContent !== text) readout.textContent = text;
  stage.setAttribute("aria-valuetext", text);
}
function tick(time) {
  const dt = last ? Math.min((time - last) / 1000, 1 / 30) : 1 / 60;
  last = time;
  if (touring) { clock += dt; u = (u + dt * 0.25) % 4; withS = tourS(clock); }
  else if (target !== null) { u += (target - u) * (1 - Math.exp(-dt / 0.25)); if (Math.abs(target - u) < 1e-4) { u = target; target = null; } }
  draw(dt);
  frame = visible ? requestAnimationFrame(tick) : 0;
}
const run = () => { if (!frame && visible && !still.matches) { last = 0; frame = requestAnimationFrame(tick); } };
const hold = () => { touring = false; clearTimeout(idle); idle = setTimeout(() => { touring = !still.matches; clock = withS ? 0 : 9; run(); }, 6000); };
const steer = (next) => { hold(); target = next; if (still.matches) { u = next; target = null; draw(0); } run(); };
const flip = () => { hold(); withS = !withS; if (still.matches) draw(0); run(); };
stage.addEventListener("keydown", (event) => {
  const base = target ?? u;
  if (event.key === "ArrowRight" || event.key === "ArrowUp") steer(Math.round(base * 2 + 1) / 2);
  else if (event.key === "ArrowLeft" || event.key === "ArrowDown") steer(Math.max(0, Math.round(base * 2 - 1) / 2));
  else if (event.key === "Home") steer(0);
  else if (event.key === "End") steer(1);
  else if (event.key === "s" || event.key === "S" || event.key === " ") flip();
  else return;
  event.preventDefault();
});
stage.addEventListener("click", flip);
new IntersectionObserver((entries) => { visible = entries[entries.length - 1].isIntersecting; if (visible) run(); }, { rootMargin: "120px 0px" }).observe(stage);
if (still.matches) { withS = false; touring = false; }
draw(0);
`;

const COPY = {
  en: {
    title: "Classical–quantum pairing",
    hint: "Click: slide S in or out · ← →: time",
    keys: ["Beam: level means the two sides read the same current", "Left pan J by hand; right pan the state's two phases", "S: read with the independent dual's exchange"],
    caption: `Theorem 6.2 and Example 6.6. The left pan holds the classical current J = 4Nk·½ = ${classicalCurrent.toFixed(4)}, computed from the source constants alone. The right pan holds the occupied state, whose upper and lower phases turn in opposite directions; it weighs 4Nk·⟨v, R(A) v⟩. With the independent dual's exchange S the beam is level at every time, with no counterweight to tune: the factor 4Nk is computed, not fitted. Slide S out and the reading becomes J·cos 2θ: level only at u = 0 and 2, and at the dark moment u = 1 the quantum side reads −J and the beam falls fully to the classical side.`,
    aria: "Balance: arrow keys step the time u in halves, S slides the exchange in or out",
    with: "with S",
    without: "without S",
    classical: "classical",
    quantum: "quantum",
  },
  zh: {
    title: "经典—量子配对",
    hint: "点击：推入或拉出 S · ← →：时间",
    keys: ["横梁：水平即两侧读出同一个电流", "左盘为手算的 J；右盘为占据态的两个相位", "S：按独立对偶的交换读数"],
    caption: `定理 6.2 与例 6.6。左盘是经典电流 J = 4Nk·½ = ${classicalCurrent.toFixed(4)}，只用源常数手算得出。右盘是占据态，上下两个相位反向转动，其重量为 4Nk·⟨v, R(A) v⟩。带上独立对偶的交换 S，横梁在每个时刻都保持水平，无需任何配重微调：系数 4Nk 是算出的，不是拟合的。拉出 S，读数变成 J·cos 2θ：只在 u = 0 与 2 时水平；到暗时刻 u = 1，量子侧读出 −J，横梁整个倒向经典侧。`,
    aria: "天平：方向键按半步拨动时间 u，S 键推入或拉出交换",
    with: "有 S",
    without: "无 S",
    classical: "经典",
    quantum: "量子",
  },
};
const bodyOf = (lang) => {
  const copy = COPY[lang];
  const rest = balance(1, false);
  return `<div data-figure="pairing-balance" data-with="${copy.with}" data-without="${copy.without}" data-classical="${copy.classical}" data-quantum="${copy.quantum}">${k.plateHtml({
    fig: "Fig 6.6",
    title: copy.title,
    hint: copy.hint,
    readout: `u 1.00 · ${copy.without} · ${copy.classical} ${rest.classical.toFixed(3)} · ${copy.quantum} −${Math.abs(rest.quantum).toFixed(3)}`,
    keys: [
      { mark: "lit", label: copy.keys[0] },
      { mark: "raised", label: copy.keys[1] },
      { mark: "dim", label: copy.keys[2] },
    ],
    caption: copy.caption,
    body: `<div class="iso-stage" tabindex="0" role="slider" aria-label="${copy.aria}" aria-valuemin="0" aria-valuemax="4" aria-valuenow="1">${svg}</div>`,
  })}</div>`;
};

const script = `{\n${kitSource}\n${latheSource}\n${modelSource}\n${live}\n}`.replace(/<\/(script)/gi, "<\\/$1");
if (fragment) {
  const outDir = join(HERE, "../../src/generated");
  mkdirSync(outDir, { recursive: true });
  writeFileSync(join(outDir, "pairing-balance.json"), JSON.stringify({ html: { zh: bodyOf("zh"), en: bodyOf("en") }, css: CSS, script }));
  console.log("wrote src/generated/pairing-balance.json");
} else {
  mkdirSync(join(HERE, "out"), { recursive: true });
  const name = theme === "light" ? "pairing-balance-light.html" : "pairing-balance.html";
  writeFileSync(join(HERE, "out", name), k.pageHtml({ title: "Classical–quantum pairing", theme, body: `<style>${CSS}</style>${bodyOf("en")}`, script: `{\n${kitSource}\n${latheSource}\n${modelSource}\n${live}\n}`, width: 700 }));
  console.log("wrote out/" + name);
}
