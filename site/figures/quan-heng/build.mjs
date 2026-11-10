// Fig: a steelyard (quan-heng) for responsibility reattachment (Proposition 4, eqs. 5–8, PE2).
// The hook carries the initiator's advantage m = 4, the poise (quan) weighs the shifted liability
// T = 6, and the beam (heng) reads the moment Δ(λ) = m − λT as the poise slides to λ.
//   bun build.mjs [--light]   → out/quan-heng[-light].html (standalone, for checks)
//   bun build.mjs --fragment  → ../../src/generated/quan-heng.json (for the site)
import { mkdirSync, readFileSync, writeFileSync } from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";
import * as k from "../kit/iso-kit.mjs";
import * as G from "../kit/lathe.mjs";
import { ADVANTAGE, FULL, PAYERS, PEACE, STAR, STEPS, capOf, deltaOf, fraction, halves, stateOf } from "./model.mjs";
import { shipped, SWING_CSS, swingSource } from "../swing.mjs";

const HERE = dirname(fileURLToPath(import.meta.url));
const theme = process.argv.includes("--light") ? "light" : "dark";
const fragment = process.argv.includes("--fragment");

const WIDTH = 680;
const HEIGHT = 470;

const PLATE = { x: -122, y: -54, w: 244, d: 108, r: 8 };
const PLATE_H = 10;
const FOOT_H = 5;

const PIVOT = [0, 0, 104];
// arm: pivot to hook, and pivot to the star at λ = 1. y, v: half depth and half height of the section.
const BEAM = { arm: 84, back: 91, front: 95, y: 2, v: 2.8 };
const TILT = (10 * Math.PI) / 180; // beam angle at Δ = m
const DROP = 30; // hook to pan
const PAN = { r: 17, h: 2.2 };
const COLUMN = { y: -28, r: 4.5 };
const ARM = { z: 132, h: 5 };
const STRAP = { y: 3.2, d: 1.2, half: 2.4 };
const NEEDLE = { y: 5.7, length: 25 };
const SCALE = { y: 4.45, r0: 21.5, z0: 117 };
const CORD = 8;
const POISE = { r: 7.2, unit: 2.3 };
const RIDER = 2.2; // half length along the beam
const STOP = 1.5;
const RACK = { xs: [-74, 0, 74], y: 30, base: 2, unit: 2.2, r: 6.2, post: [8.6, -8.6] };
const SLOT = { y: 45, d: 3.2 };
const TRAY = { x: -47, y: 29, w: 20, d: 15, r: 2 };
const LEVEL = [38, 38];
const RULER = { x: -4.5, y: -3, w: BEAM.arm + 9, d: 6, r: 1 };
const PURSE = { x: -110, y: -47, w: 52, d: 13, r: 2, h: 3, pitch: 7.4 };
// The still figure: the poise on the tie star, under the payer who can reach it.
const REST = { step: STAR, cap: capOf(PAYERS[0]) };

const FIT = [...k.boxCorners(PLATE, -PLATE_H - FOOT_H, 0), [-BEAM.back - 6, 0, PIVOT[2] + 22], [BEAM.front + 6, 0, PIVOT[2] + 22], [0, COLUMN.y, ARM.z + ARM.h + 8]];
const P = k.fitProjection(FIT, WIDTH, HEIGHT, { pad: 24, azimuth: 64 });
// The page swings the view (../swing.mjs), framed by the same fit, and redraws `composition` there.
const FRAME = { points: FIT, width: WIDTH, height: HEIGHT, pad: 24 };

const at = (point) => k.iso(point, P);
const S = (paths, style) => k.solidSvg(paths, style);
const L = (d, style) => k.lineSvg(d, style);
const D = (points, style) => k.dotsSvg(points, style);
// A material (kit iso.css, data-mat) remaps the tone ramp of everything inside it.
const M = (material, ...svg) => `<g data-mat="${material}">${svg.join("")}</g>`;
const byDepth = (items, key = (item) => item) => [...items].sort((a, b) => k.depthOf([...key(a).slice(0, 2), 0], P) - k.depthOf([...key(b).slice(0, 2), 0], P));
const box = (halfY, v0, v1) => [[-halfY, v0], [halfY, v0], [halfY, v1], [-halfY, v1]];

// --- shared with the page: everything that moves follows the beam angle φ and the rate λ ------

// φ > 0 raises the poise end. A beam point: s along the beam, y in depth, n along its up-normal.
const beamPoint = (phi, s, y, n) => [PIVOT[0] + s * Math.cos(phi) - n * Math.sin(phi), y, PIVOT[2] + s * Math.sin(phi) + n * Math.cos(phi)];
const beamFrame = (phi) => G.frameOf(PIVOT, [Math.cos(phi), 0, Math.sin(phi)], [0, 1, 0], [-Math.sin(phi), 0, Math.cos(phi)]);
const hookOf = (phi) => { const p = beamPoint(phi, -BEAM.arm, 0, -BEAM.v); return [p[0], 0, p[2] - 3]; };
const panTop = (phi) => { const h = hookOf(phi); return [h[0], 0, h[2] - DROP + PAN.h]; };
const hangOf = (phi, lambda) => beamPoint(phi, lambda * BEAM.arm, 0, -BEAM.v);
const STRING_ANGLES = [0, (2 * Math.PI) / 3, (4 * Math.PI) / 3];
const strings = (phi, front) => {
  const h = hookOf(phi), top = panTop(phi);
  const [vx, vy] = G.viewOf(P);
  return STRING_ANGLES.map((angle) => [top[0] + Math.sin(angle) * (PAN.r - 1.5), -Math.cos(angle) * (PAN.r - 1.5), top[2]])
    .filter((rim) => ((rim[0] - top[0]) * vx + rim[1] * vy > 0) === front)
    .map((rim) => k.wireSvg(at(h), at(rim), { ends: "to", size: 0.7, tone: "mid" }))
    .join("");
};
// The beam and what rides it. `cap` and `star` are in twelfths; Λpeace = [star, cap] is the lit inlay.
function beamSvg(phi, lambda, cap, star) {
  const F = beamFrame(phi), unit = BEAM.arm / STEPS;
  const section = [[-BEAM.y, -BEAM.v], [BEAM.y, -BEAM.v], [BEAM.y, BEAM.v * 0.7], [BEAM.y * 0.6, BEAM.v], [-BEAM.y * 0.6, BEAM.v], [-BEAM.y, BEAM.v * 0.7]];
  const stars = Array.from({ length: STEPS + 1 }, (_, i) => ({ i, p: at(beamPoint(phi, i * unit, BEAM.y + 0.05, 0.9)) }));
  const out = [M("ink",
    S(G.prismOf(F, section, -BEAM.back, BEAM.front, P), { tone: "hi" }),
    D(stars.filter(({ i }) => i % 4).map(({ p }) => p), { size: 0.55, tone: "hi" }),
    D([...stars.filter(({ i }) => i % 4 === 0).map(({ p }) => p), at(beamPoint(phi, -BEAM.arm, BEAM.y + 0.05, 0.9))], { size: 0.95, tone: "hi" }))];
  for (const [s0, s1] of [[-BEAM.back - 2.4, -BEAM.back + 1.6], [BEAM.front - 1.6, BEAM.front + 2.4]])
    out.push(M("jade", S(G.prismOf(F, box(BEAM.y + 0.5, -BEAM.v - 0.5, BEAM.v + 0.5), s0, s1, P), { tone: "mid" })));
  if (cap - star > 0.04) out.push(S(G.prismOf(F, [[BEAM.y, -2.2], [BEAM.y + 0.5, -2.2], [BEAM.y + 0.5, -0.5], [BEAM.y, -0.5]], star * unit, cap * unit, P), { tone: "hi", lit: true, crease: "none" }));
  // The tie notch at λ*: a tooth on the beam's back that the rider settles over.
  out.push(M("jade", S(G.prismOf(F, box(BEAM.y * 0.6, BEAM.v, BEAM.v + 1.3), star * unit - 0.7, star * unit + 0.7, P), { tone: "mid" })));
  // The capacity stop: a collar clamped where the payer's spendable stock runs out.
  const stop = cap * unit + RIDER + STOP;
  const screw = G.frameAlong(beamPoint(phi, stop, 0, BEAM.v + 1.1), [-Math.sin(phi), 0, Math.cos(phi)]);
  out.push(M("jade", S(G.prismOf(F, box(BEAM.y + 1.1, -BEAM.v - 1.1, BEAM.v + 1.1), stop - STOP, stop + STOP, P), { tone: "mid" }),
    S(G.disc(0, 1.3, 0.8, screw, P), { tone: "lo" }), S(G.disc(1.3, 3.6, 2.1, screw, P), { tone: "hi" })));
  const rider = lambda * BEAM.arm;
  out.push(M("jade", S(G.prismOf(F, box(BEAM.y + 0.9, -0.6, BEAM.v + 1.7), rider - RIDER, rider + RIDER, P), { tone: "hi" }),
    L(k.pathOf([at(beamPoint(phi, rider, BEAM.y + 0.95, -0.6)), at(beamPoint(phi, rider, BEAM.y + 0.95, BEAM.v + 1.7))]), { tone: "hi" })));
  const hang = hangOf(phi, lambda);
  out.push(L(k.pathOf([at(hang), at([hang[0], 0, hang[2] - CORD + 2.5])]), { tone: "mid" }));
  const hook = hookOf(phi);
  out.push(L(k.pathOf([at(beamPoint(phi, -BEAM.arm, 0, -BEAM.v)), at([hook[0], 0, hook[2] + 2.4])]), { tone: "mid" }), L(k.sideRing([hook[0], 0, hook[2] + 1.2], 1.2, "y", P, 14), { tone: "hi" }), D([at(hook)], { size: 0.8, tone: "hi" }));
  return out.join("");
}
const needleD = (phi) => k.pathOf([0, NEEDLE.length].map((r) => at([PIVOT[0] - Math.sin(phi) * r, NEEDLE.y, PIVOT[2] + Math.cos(phi) * r])));
// One party's stock, a stack of half-unit discs with a seam at every whole unit.
function stackSvg(index, count) {
  const x = RACK.xs[index], height = (count * RACK.unit) / 2;
  const seams = [];
  for (let z = RACK.unit; z < height - 0.25; z += RACK.unit) seams.push(k.sideArc(x, RACK.y, RACK.r, RACK.base + z, P, 20));
  return M("marble", S(k.cylinder(x, RACK.y, RACK.r, RACK.base, height, P, 44, 0.3), { tone: "hi", crease: "none" }), L(seams.join(""), { tone: "lo" }),
    L(k.ring(x, RACK.y, RACK.r - 1.9, RACK.base + height, P, 28), { tone: "faint" }));
}

// The payer's purse: six sockets for a full reattachment, a peg in each unit the payer can spend.
const pegAt = (index) => [PURSE.x + PURSE.w / 2 + (index - 2.5) * PURSE.pitch, PURSE.y + PURSE.d / 2];
function purseSvg(spend) {
  const pegs = [];
  for (let i = 0; i < 6; i++) {
    const [x, y] = pegAt(i), up = 4.4 * Math.max(0, Math.min(1, spend - i));
    if (up > 0.35) pegs.push(S(k.cylinder(x, y, 2.3, PURSE.h, up, P, 20, 0.3), { tone: "hi" }) + L(k.ring(x, y, 1.1, PURSE.h + up, P, 12), { tone: "lo" }));
  }
  return M("marble", ...pegs);
}

// --- static art ------------------------------------------------------------------------------

function plate() {
  const out = [`<path class="iso-halo" d="${k.haloOf(PLATE, -PLATE_H - FOOT_H, PLATE_H, P)}"/>`];
  for (const [x, y] of byDepth(k.corners(PLATE, 20))) {
    out.push(M("ink", S(k.cylinder(x, y, 7.5, -PLATE_H - FOOT_H, 1.6, P, 28), { tone: "lo" })));
    out.push(M("ink", S(k.cylinder(x, y, 5.6, -PLATE_H - FOOT_H + 1.6, FOOT_H - 1.6, P, 28), { tone: "mid" }), L(k.knurl(x, y, 5.6, -PLATE_H - FOOT_H + 1.6, -PLATE_H, 20, P), { tone: "lo" })));
  }
  const screws = k.corners(PLATE, 10);
  out.push(M("marble", S(k.slabOf(PLATE, -PLATE_H, PLATE_H, P, 8, 1.6), { tone: "mid", inner: L(k.sideSeam(PLATE, -4, P, 8), { tone: "faint" }) }),
    L(k.planOutline(k.insetPlan(PLATE, 5), 0, P), { tone: "lo" }), L(screws.map(([x, y]) => k.ring(x, y, 2.2, 0, P, 16)).join(""), { tone: "lo" }), D(screws.map(([x, y]) => at([x, y, 0])), { size: 0.5 })));
  const label = { x: 72, y: -46, w: 42, d: 11, r: 1.4 };
  out.push(M("jade", S(k.slabOf(label, 0, 0.7, P, 3), { tone: "lo", crease: "none" }),
    D([at([label.x + 2, label.y + 5.5, 0.7]), at([label.x + label.w - 2, label.y + 5.5, 0.7])], { size: 0.45 })),
    k.faceTextSvg(k.topMatrix([label.x + 6.5, label.y + label.d - 3.4], 0.7, P), "Δ = m − λT", { size: 4.6, tone: "hi" }));
  // The rate ruler under the poise arm: a tick per twelfth, a long one at each third.
  const ticks = k.topTicks(0, BEAM.arm, BEAM.arm / STEPS, 4, RULER.y + 0.8, 0.6, [1.6, 3], P);
  out.push(M("jade", S(k.slabOf(RULER, 0, 0.6, P, 3), { tone: "lo", crease: "none" }), L(ticks.minor, { tone: "lo" }), L(ticks.major, { tone: "mid" }),
    D([at([RULER.x + 1.8, RULER.y + 3.6, 0.6]), at([RULER.x + RULER.w - 1.8, RULER.y + 3.6, 0.6])], { size: 0.45 })));
  return out.join("");
}

// The original slot: the one registered channel from the initiator's stand to the victim's.
function slot() {
  const [a, , c] = RACK.xs, mid = SLOT.y + SLOT.d / 2;
  const groove = { x: a - 3, y: SLOT.y, w: c - a + 6, d: SLOT.d, r: SLOT.d / 2 };
  return [L(k.planOutline(groove, 0, P, 6), { tone: "lo" }), L(k.lineOnTop([a, mid], [c, mid], 0, P), { tone: "faint" }),
    L([a, c].map((x) => k.lineOnTop([x, RACK.y + 11], [x, SLOT.y], 0, P)).join(""), { tone: "lo" }), D([at([a, mid, 0]), at([c, mid, 0])], { size: 0.7, tone: "mid" })].join("");
}
const bead = () => M("jade", S(k.cylinder(RACK.xs[0], SLOT.y + SLOT.d / 2, 1.5, 0, 1.3, P, 16), { tone: "hi" }));

function column() {
  const y = COLUMN.y, shaft = (z0, z1) => S(k.cylinder(0, y, COLUMN.r, z0, z1 - z0, P, 28), { tone: "mid", crease: "none" });
  return [
    M("ink", S(k.slabOf({ x: -12, y: y - 11, w: 24, d: 22, r: 3 }, 0, 3, P, 4, 0.5), { tone: "mid" }), D(k.corners({ x: -12, y: y - 11, w: 24, d: 22 }, 2.6).map(([px, py]) => at([px, py, 3])), { size: 0.45 })),
    M("jade", S(k.cylinder(0, y, 7, 3, 3, P, 32, 0.4), { tone: "mid" })),
    M("marble", shaft(6, 66)),
    M("jade", S(k.cylinder(0, y, 5.8, 66, 3, P, 28, 0.3), { tone: "mid" })),
    M("marble", shaft(69, ARM.z), L([28, 46, 92, 112].map((z) => k.sideArc(0, y, COLUMN.r, z, P, 16)).join(""), { tone: "faint" })),
    // The arm reaches forward over the pivot; the shears hang from it.
    M("ink", S(k.slabOf({ x: -4.2, y: y - 6, w: 8.4, d: 6 - y + STRAP.y + STRAP.d + 1.4, r: 1.2 }, ARM.z, ARM.h, P, 3, 0.4), { tone: "mid" }), D([at([0, 0, ARM.z + ARM.h])], { size: 0.5 })),
    M("jade", S(k.cylinder(0, y, 5.6, ARM.z + ARM.h, 2, P, 28, 0.4), { tone: "mid" }), S(k.cylinder(0, y, 2.4, ARM.z + ARM.h + 2, 2.4, P, 20, 0.5), { tone: "hi" })),
  ].join("");
}

const strap = (y) => M("ink", S(k.slabOf({ x: -STRAP.half, y, w: 2 * STRAP.half, d: STRAP.d, r: 0.3 }, PIVOT[2] - 3.4, ARM.z - PIVOT[2] + 3.4, P, 1, 0.2), { tone: "mid" }));

// The tilt scale on the front shear: one tick per unit of Δ, leaning to the hook side for Δ > 0.
function scale() {
  const plate = { x: -9.5, y: STRAP.y, w: 19, d: STRAP.d, r: 0.4 };
  const out = [S(k.slabOf(plate, SCALE.z0, ARM.z - SCALE.z0, P, 1, 0.2), { tone: "mid" })];
  const onFace = (angle, r) => at([PIVOT[0] - Math.sin(angle) * r, SCALE.y, PIVOT[2] + Math.cos(angle) * r]);
  out.push(L(k.pathOf(Array.from({ length: 33 }, (_, i) => onFace(-TILT + (2 * TILT * i) / 32, SCALE.r0))), { tone: "lo" }));
  const tick = (index, length) => k.pathOf([onFace((TILT * index) / ADVANTAGE, SCALE.r0), onFace((TILT * index) / ADVANTAGE, SCALE.r0 + length)]);
  out.push(L([-3, -1, 1, 3].map((i) => tick(i, 1.3)).join(""), { tone: "lo" }), L([-4, -2, 2, 4].map((i) => tick(i, 2.2)).join(""), { tone: "mid" }), L(tick(0, 3), { tone: "hi" }));
  out.push(D([at([plate.x + 1.8, SCALE.y, ARM.z - 1.8]), at([plate.x + plate.w - 1.8, SCALE.y, ARM.z - 1.8])], { size: 0.4 }));
  return M("marble", ...out);
}
const pin = () => M("jade", S(G.disc(STRAP.y + STRAP.d, NEEDLE.y - 0.1, 1.5, G.frameAlong(PIVOT, [0, 1, 0]), P), { tone: "mid" }));

function pan() {
  const top = panTop(0);
  return M("marble", S(k.cylinder(top[0], 0, PAN.r, top[2] - PAN.h, PAN.h, P, 64, 0.6), { tone: "mid" }), L(k.ring(top[0], 0, PAN.r - 2.4, top[2], P, 56), { tone: "faint" }));
}
// The load: m = 4, four unit weights.
function weights() {
  const [x, , z] = panTop(0);
  return byDepth([[-5.4, -5.4], [5.4, -5.4], [-5.4, 5.4], [5.4, 5.4]].map(([dx, dy]) => [x + dx, dy])).map(([wx, wy]) => M("ink",
    S(k.cylinder(wx, wy, 4.3, z, 6, P, 28, 0.4), { tone: "hi" }),
    S(k.cylinder(wx, wy, 1.7, z + 6, 1, P, 14), { tone: "mid" }),
    S(k.cylinder(wx, wy, 2.6, z + 7, 1.9, P, 18, 0.3), { tone: "hi" }),
  )).join("");
}
// The poise: T = 6, six unit slugs on one hanger, drawn under the pivot and carried along the beam.
function poise() {
  const top = hangOf(0, 0)[2] - CORD, body = 6 * POISE.unit, z = top - 3.4 - body;
  const seams = [1, 2, 3, 4, 5].map((i) => k.sideArc(0, 0, POISE.r, z + i * POISE.unit, P, 24)).join("");
  return [
    M("ink", S(k.cylinder(0, 0, 2.3, z - 1.4, 1.4, P, 18), { tone: "mid" })),
    M("jade", S(k.cylinder(0, 0, POISE.r, z, body, P, 52, 0.5), { tone: "hi", crease: "none" }), L(seams, { tone: "lo" })),
    M("ink", S(k.cylinder(0, 0, 3.3, z + body, 1.6, P, 22, 0.3), { tone: "mid" }), S(k.cylinder(0, 0, 1.3, z + body + 1.6, 1.8, P, 12), { tone: "hi" })),
    L(k.sideRing([0, 0, top + 1.2], 1.3, "y", P, 14), { tone: "hi" }),
  ].join("");
}

// A stand: a plinth, a graduated post, and a feeler set at the party's peace stock.
function rack(index) {
  const x = RACK.xs[index], y = RACK.y, px = x + RACK.post[0], py = y + RACK.post[1];
  const plan = { x: x - 11, y: y - 11, w: 22, d: 22, r: 3 };
  const mark = RACK.base + PEACE[index] * RACK.unit, height = 10 * RACK.unit + 3;
  const rings = Array.from({ length: 10 }, (_, i) => k.sideArc(px, py, 0.8, RACK.base + (i + 1) * RACK.unit, P, 8)).join("");
  const reach = RACK.r / Math.hypot(...RACK.post);
  return [
    M("ink", S(k.slabOf(plan, 0, RACK.base, P, 4, 0.4), { tone: "mid" }), D(k.corners(plan, 2.4).map(([cx, cy]) => at([cx, cy, RACK.base])), { size: 0.4 })),
    M("jade", S(k.cylinder(px, py, 0.8, RACK.base, height, P, 12), { tone: "mid", crease: "none" }), L(rings, { tone: "lo" }), S(k.cylinder(px, py, 1.3, RACK.base + height, 0.9, P, 12), { tone: "hi" })),
    M("ink", S(k.cylinder(px, py, 1.9, mark - 0.5, 1, P, 16), { tone: "hi" })),
    k.wireSvg(at([px, py, mark]), at([x + RACK.post[0] * reach, y + RACK.post[1] * reach, mark]), { ends: "to", size: 0.8, tone: "hi" }),
  ].join("");
}

// What the war destroyed: two units, four broken halves that belong to no stack.
function tray() {
  const out = [M("ink", S(k.slabOf(TRAY, 0, 1.6, P, 4, 0.3), { tone: "mid" }), L(k.planOutline(k.insetPlan(TRAY, 1.5), 1.6, P, 4), { tone: "lo" }))];
  const shards = [[-43, 33.5, 0.4], [-36, 32.5, 1.9], [-40.5, 39.5, 2.7], [-33.5, 39, 1.1]];
  for (const [x, y, turn] of byDepth(shards)) {
    const crack = [[-1, 0], [-0.2, 0.25], [0.3, -0.2], [1, 0.1]].map(([u, v]) => [x + 3 * (u * Math.cos(turn) - v * Math.sin(turn)), y + 3 * (u * Math.sin(turn) + v * Math.cos(turn))]);
    out.push(M("marble", S(k.cylinder(x, y, 3.1, 1.6, 0.6, P, 20), { tone: "lo", crease: "none" }), L(k.onTop(crack, 2.2, P), { tone: "mid" })));
  }
  return out.join("");
}

function purse() {
  const sockets = Array.from({ length: 6 }, (_, i) => pegAt(i));
  return M("ink", S(k.slabOf(PURSE, 0, PURSE.h, P, 4, 0.4), { tone: "mid" }), L(sockets.map(([x, y]) => k.ring(x, y, 2.9, PURSE.h, P, 18)).join(""), { tone: "lo" }),
    D(sockets.map(([x, y]) => at([x, y, PURSE.h])), { size: 0.5, tone: "mid" }));
}

function level() {
  const [x, y] = LEVEL;
  return M("jade", S(k.cylinder(x, y, 4.6, 0, 1.6, P, 28, 0.3), { tone: "mid" }), L(k.ring(x, y, 2.2, 1.6, P, 20), { tone: "lo" }), D([at([x, y, 1.6])], { size: 0.9, tone: "hi" }));
}

const shift = (by) => k.translateAlong(P, by);
const hangShift = (phi, lambda) => { const h = hangOf(phi, lambda), rest = hangOf(0, 0); return shift([h[0] - rest[0], 0, h[2] - rest[2]]); };

// Drawn at the still pose; the page repaints the moving parts from there.
function composition() {
  const rest = stateOf(REST.step, PAYERS[0]), lambda = REST.step / STEPS, top = panTop(0);
  return [
    plate(),
    slot(),
    `<g data-part="bead" transform="${shift([(RACK.xs[2] - RACK.xs[0]) * lambda, 0, 0])}">${bead()}</g>`,
    purse(),
    `<g data-part="purse">${purseSvg(PAYERS[0])}</g>`,
    column(),
    strap(-STRAP.y - STRAP.d),
    `<path class="iso-halo" d="${k.haloOf({ x: top[0] - PAN.r + 4, y: -PAN.r + 4, w: 2 * PAN.r - 8, d: 2 * PAN.r - 8, r: PAN.r - 4 }, 0, 0.2, P)}" style="filter:blur(8px);opacity:calc(var(--anatomy-halo-opacity) * .45)"/>`,
    `<g data-part="shade" transform="${shift([hangOf(0, lambda)[0], 0, 0])}"><path class="iso-halo" d="${k.haloOf({ x: -5, y: -5, w: 10, d: 10, r: 5 }, 0.6, 0.2, P)}" style="filter:blur(5px);opacity:calc(var(--anatomy-halo-opacity) * .5)"/></g>`,
    `<g data-part="strings-back">${strings(0, false)}</g>`,
    `<g data-part="pan">${pan()}${weights()}</g>`,
    `<g data-part="strings-front">${strings(0, true)}</g>`,
    `<g data-part="poise" transform="${hangShift(0, lambda)}">${poise()}</g>`,
    `<g data-part="beam">${beamSvg(0, lambda, REST.cap, STAR)}</g>`,
    strap(STRAP.y),
    scale(),
    pin(),
    `<path data-part="needle" class="iso-line" data-tone="hi" data-free="end" d="${needleD(0)}" style="stroke-width:1.1"/>`,
    D([at([PIVOT[0], NEEDLE.y, PIVOT[2]])], { size: 1.1, tone: "hi" }),
    ...byDepth([0, 1, 2], (i) => [RACK.xs[i], RACK.y]).map((i) => rack(i) + `<g data-part="stack-${i}">${stackSvg(i, rest.stock2[i])}</g>`),
    tray(),
    level(),
  ].join("");
}

const svg = k.figureSvg({
  width: WIDTH,
  height: HEIGHT,
  className: "qh-svg",
  label:
    "A steelyard hanging from a column. Its hook carries a pan with four unit weights, the initiator's advantage m = 4. A poise of six unit slugs, the shifted liability T = 6, slides along a beam marked in twelfths; the beam's tilt reads Δ = m − λT and is level at the star λ = 2/3. A collar clamped on the beam is the payer's capacity; the lit strip between the tie star and the collar is the interval of rates that end the war, and it vanishes when the collar sits before the star. On the base three stacks show the parties' stock beside feelers set at their peace stock, and a tray holds the two destroyed units.",
  body: composition(),
});

const CSS = `
.iso-stage{outline:none;cursor:pointer;touch-action:pan-y}
.iso-stage:focus-visible{box-shadow:0 0 0 1px var(--anatomy-mid)}
${SWING_CSS}
@media (max-width:560px){.iso-plate:has(.qh-svg){overflow:hidden}.qh-svg.iso-svg{width:116%;max-width:none;margin:0 -8%}}
`;

const strip = (file) => readFileSync(join(HERE, file), "utf8").replace(/^export /gm, "");
const kitSource = strip("../kit/iso-kit.mjs");
// lathe.mjs shares a few helper names with the core, so it lives in its own scope.
const latheSource = `const LATHE = (() => {\n${strip("../kit/lathe.mjs").replace(/^import .*$/gm, "")}\nreturn { ${Object.keys(G).join(", ")} };\n})();`;
const MODEL = ["ADVANTAGE", "FULL", "PAYERS", "PEACE", "STAR", "STEPS", "capOf", "deltaOf", "fraction", "halves", "stateOf"];
const modelSource = `const { ${MODEL.join(", ")} } = (() => {\n${strip("model.mjs")}\nreturn { ${MODEL.join(", ")} };\n})();`;
const live = `
const P0 = ${JSON.stringify(P)};
let P = P0;
${shipped({ PLATE, PLATE_H, FOOT_H, PIVOT, BEAM, TILT, DROP, PAN, COLUMN, ARM, STRAP, NEEDLE, SCALE, CORD, POISE, RIDER, STOP, RACK, SLOT, TRAY, LEVEL, PURSE, RULER, REST, STRING_ANGLES, FRAME })}
const k = { ${Object.keys(k).join(", ")} };
const G = LATHE;
const at = (point) => k.iso(point, P);
const S = (paths, style) => k.solidSvg(paths, style);
const L = (d, style) => k.lineSvg(d, style);
const D = (points, style) => k.dotsSvg(points, style);
const M = ${M.toString()};
const byDepth = ${byDepth.toString()};
${shipped({ box, beamPoint, beamFrame, hookOf, panTop, hangOf, strings, beamSvg, needleD, stackSvg, pegAt, purseSvg, purse, plate, slot, bead, column, strap, scale, pin, pan, weights, poise, rack, tray, level, shift, hangShift, composition })}
${swingSource}
const root = document.querySelector('[data-figure="quan-heng"]');
const stage = root.querySelector(".iso-stage");
const part = (name) => stage.querySelector('[data-part="' + name + '"]');
const readout = root.querySelector("[data-readout]");
const still = matchMedia("(prefers-reduced-motion: reduce)");
// goal: the step the poise is sent to; lambda follows it and the stop pushes it back; phi is the sprung beam.
let payer = 0, goal = REST.step, lambda = REST.step / STEPS, cap = REST.cap, phi = 0, rate = 0, stacks = "";
let touring = !still.matches, tourClock = 0, tourStage = 3, visible = false, frame = 0, last = 0, idle = 0;
const capNow = () => capOf(PAYERS[payer]);
const signed = (h) => (h > 0 ? "+" : "") + halves(h);
function draw(dt) {
  const settle = still.matches || !dt;
  cap = settle ? capNow() : cap + (capNow() - cap) * (1 - Math.exp(-dt / 0.18));
  lambda = Math.min(cap / STEPS, settle ? goal / STEPS : lambda + (goal / STEPS - lambda) * (1 - Math.exp(-dt / 0.22)));
  const want = (TILT * deltaOf(lambda)) / ADVANTAGE;
  if (settle) { phi = want; rate = 0; }
  else for (let i = 0; i < 4; i++) { rate += ((want - phi) * 40 - rate * 8) * dt / 4; phi += rate * dt / 4; }
  paint();
}
function paint() {
  part("beam").innerHTML = beamSvg(phi, lambda, cap, STAR);
  part("needle").setAttribute("d", needleD(phi));
  const top = panTop(phi), rest = panTop(0);
  part("pan").setAttribute("transform", shift([top[0] - rest[0], 0, top[2] - rest[2]]));
  part("strings-back").innerHTML = strings(phi, false);
  part("strings-front").innerHTML = strings(phi, true);
  part("poise").setAttribute("transform", hangShift(phi, lambda));
  part("bead").setAttribute("transform", shift([(RACK.xs[2] - RACK.xs[0]) * lambda, 0, 0]));
  part("shade").setAttribute("transform", shift([hangOf(phi, lambda)[0], 0, 0]));
  const state = stateOf(Math.round(lambda * STEPS), PAYERS[payer]);
  // The stacks and the purse move with the poise and the stop; the readout names the nearest twelfth.
  const flow = lambda * STEPS, key = flow.toFixed(3) + "/" + cap.toFixed(3);
  if (key !== stacks) {
    stacks = key;
    [state.stock2[0] + state.step - flow, state.stock2[1], state.stock2[2] - state.step + flow].forEach((count, index) => { part("stack-" + index).innerHTML = stackSvg(index, count); });
    part("purse").innerHTML = purseSvg((cap * FULL) / STEPS);
  }
  const text = "λ " + fraction(state.step) + " · Δ " + signed(state.delta2) + " · (" + state.stock2.map(halves).join(", ") + ") · Λ " + (state.interval ? "[" + state.interval.map((s) => fraction(s)).join(", ") + "]" : "∅");
  if (readout.textContent !== text) readout.textContent = text;
  stage.setAttribute("aria-valuenow", (state.step / STEPS).toFixed(3));
  stage.setAttribute("aria-valuetext", text);
}
// Idle tour: the poise walks out to the stop and back; each round the other payer's stop is clamped on.
const TOUR = [{ to: () => capNow(), wait: 0.9 }, { hold: 2.6 }, { to: () => 0, wait: 0.9 }, { swap: true, hold: 1.4 }];
function tour(dt) {
  const stageNow = TOUR[tourStage];
  tourClock += dt;
  if (stageNow.to) {
    const end = stageNow.to();
    if (goal === end) { if (tourClock > stageNow.wait) next(); }
    else if (tourClock > 0.34) { goal += Math.sign(end - goal); tourClock = 0; }
  } else if (tourClock > stageNow.hold) next();
}
function next() {
  tourStage = (tourStage + 1) % TOUR.length;
  tourClock = 0;
  if (TOUR[tourStage].swap) payer = 1 - payer;
}
function tick(time) {
  const dt = last ? Math.min((time - last) / 1000, 1 / 30) : 1 / 60;
  last = time;
  if (touring) tour(dt);
  draw(dt);
  frame = visible ? requestAnimationFrame(tick) : 0;
}
const run = () => { if (!frame && visible && !still.matches) { last = 0; frame = requestAnimationFrame(tick); } };
const hold = () => { touring = false; clearTimeout(idle); idle = setTimeout(() => { touring = !still.matches; tourStage = goal > 0 ? 2 : 0; tourClock = 0; run(); }, 7000); };
const steer = (step) => { hold(); goal = Math.max(0, Math.min(capNow(), step)); if (still.matches) draw(0); run(); };
const swap = () => { hold(); payer = 1 - payer; goal = Math.min(goal, capNow()); if (still.matches) draw(0); run(); };
stage.addEventListener("keydown", (event) => {
  if (event.key === "ArrowRight" || event.key === "ArrowUp") steer(goal + 1);
  else if (event.key === "ArrowLeft" || event.key === "ArrowDown") steer(goal - 1);
  else if (event.key === "Home") steer(0);
  else if (event.key === "End") steer(STEPS);
  else if (event.key === " " || event.key === "Enter") swap();
  else return;
  event.preventDefault();
});
stage.addEventListener("click", swap);
new IntersectionObserver((entries) => { visible = entries[entries.length - 1].isIntersecting; if (visible) run(); }, { rootMargin: "120px 0px" }).observe(stage);
if (still.matches) touring = false;
draw(0);
// A sideways drag swings the view (../swing.mjs): everything is redrawn from there, then the moving parts.
const svg = stage.querySelector("svg");
mountSwing(stage, { onHold: hold, onSwing: (angle) => { P = swingOf(k.iso, P0, FRAME, angle); svg.innerHTML = composition(); stacks = ""; paint(); } });
// For checks: drive.mjs sets a pose directly.
window.__quanHeng = (step, who) => { touring = false; clearTimeout(idle); payer = who; goal = step; draw(0); };
`;

const COPY = {
  en: {
    title: "Reattachment steelyard",
    hint: "Drag: look round · ← → poise · click: payer",
    keys: ["Lit strip: Λ = [λ*, λcap], the rates that end the war", "Hook m = 4; poise T = 6 at λ; tilt reads Δ = m − λT", "Collar: where the payer's spendable stock runs out"],
    refs: ["Proposition 4", "Eqs. (5)–(8)"],
    caption: [
      "A steelyard that weighs a war: the hook carries what the initiator gains, the poise carries the liability it pushed onto someone else.",
      "Peace leaves the three parties (4, 7, 10). War destroys 2 and shifts 6, leaving (8, 7, 4): the initiator is up m = 4, the four weights on the pan. The poise is the shifted liability T = 6. Slid to the rate λ, it returns 6λ along the one registered slot on the base, and the beam reads the moment Δ(λ) = 4 − 6λ.",
      "The beam is level at the star λ* = 2/3, where the initiator's stack meets its peace feeler; at λ = 1 the stacks read (2, 7, 10), the destroyed 2 have landed on the initiator alone, and the total has stayed 19 throughout.",
      "The collar is the payer's capacity λcap. A payer who can spend 5 of the 6 clamps it at 5/6, and the lit strip [2/3, 5/6] is every rate that both can be paid and ends the incentive. A payer who can spend only 3 clamps it at 1/2, before the star: the strip is gone, the beam cannot come level, and no liability rate after the fact deters the war.",
    ],
    aria: "Steelyard: arrow keys slide the poise by twelfths of the rate λ, space changes the payer's capacity",
  },
  zh: {
    title: "权衡：责任回接",
    hint: "拖动侧看 · ← → 移权 · 点击换付款人",
    keys: ["亮条：Λ = [λ*, λcap]，全部可付的止战比例", "钩 m = 4；权 T = 6 置于 λ；倾角读出 Δ = m − λT", "卡箍：付款人可支用额度的尽头"],
    refs: ["命题 4", "式 (5)–(8)"],
    caption: [
      "一杆称战争的秤：钩上挂着发动者的所得，权（秤砣）是他转嫁到别人账上的责任。",
      "和平时三方库存为 (4, 7, 10)。战争毁掉 2、转嫁 6，变为 (8, 7, 4)：发动者多出 m = 4，即盘中四枚砝码。权是被转嫁的责任 T = 6；移到比例 λ 处，就沿底座上那条登记在册的原槽接回 6λ，衡（秤杆）读出力矩 Δ(λ) = 4 − 6λ。",
      "秤杆在星位 λ* = 2/3 处持平，此时发动者的库存正好齐平他的和平标尺；到 λ = 1，三方为 (2, 7, 10)，被毁的 2 全部落回发动者自己，总量始终是 19。",
      "卡箍是付款人的容量 λcap。能支用 6 中之 5 的付款人把它夹在 5/6，亮条 [2/3, 5/6] 就是既付得出又消除开战诱因的全部比例；只能支用 3 的付款人把它夹在 1/2，落在星位之前：亮条消失，秤杆无法持平，任何事后赔偿比例都止不住这场战争。",
    ],
    aria: "杆秤：方向键按十二分之一移动权的位置 λ，空格更换付款人的容量",
  },
};
const restText = (() => {
  const s = stateOf(REST.step, PAYERS[0]);
  return `λ ${fraction(s.step)} · Δ ${halves(s.delta2)} · (${s.stock2.map(halves).join(", ")}) · Λ [${s.interval.map((x) => fraction(x)).join(", ")}]`;
})();
const bodyOf = (lang) => {
  const copy = COPY[lang];
  return `<div data-figure="quan-heng">${k.plateHtml({
    fig: "Fig 2.2",
    title: copy.title,
    hint: copy.hint,
    readout: restText,
    keys: [
      { mark: "lit", label: copy.keys[0] },
      { mark: "raised", label: copy.keys[1] },
      { mark: "dim", label: copy.keys[2] },
    ],
    caption: copy.caption,
    refs: copy.refs,
    body: `<div class="iso-stage" tabindex="0" role="slider" aria-label="${copy.aria}" aria-valuemin="0" aria-valuemax="1" aria-valuenow="${(REST.step / STEPS).toFixed(3)}">${svg}</div>`,
  })}</div>`;
};

const script = `{\n${kitSource}\n${latheSource}\n${modelSource}\n${live}\n}`;
if (fragment) {
  const outDir = join(HERE, "../../src/generated");
  mkdirSync(outDir, { recursive: true });
  writeFileSync(join(outDir, "quan-heng.json"), JSON.stringify({ html: { zh: bodyOf("zh"), en: bodyOf("en") }, css: CSS, script: script.replace(/<\/(script)/gi, "<\\/$1") }));
  console.log("wrote src/generated/quan-heng.json");
} else {
  mkdirSync(join(HERE, "out"), { recursive: true });
  const lang = process.argv.includes("--zh") ? "zh" : "en";
  const name = theme === "light" ? "quan-heng-light.html" : "quan-heng.html";
  writeFileSync(join(HERE, "out", name), k.pageHtml({ title: COPY[lang].title, theme, body: `<style>${CSS}</style>${bodyOf(lang)}`, script, width: 740 }));
  console.log("wrote out/" + name);
}
