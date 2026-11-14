// Fig: a Hankel order bench for unknown-sparsity signed recovery (Theorem 6.2, R49).
// Three stations on an address rail hold signed weights; six cups hold the moments M_j = Σ a τ^j as
// coin stacks (marble +, ink −); a 3 × 4 board copies M_{p+q} into cell (p, q), so every anti-diagonal
// reads one moment. Three nested folds rise from the board where det H_w ≠ 0, and the largest raised
// fold is the order r. Behind the rail the template P(t), solved from H_r, meets its datum exactly at
// the live addresses.
//   bun build.mjs [--light]   → out/hankel-bench[-light].html (standalone, for checks)
//   bun build.mjs --fragment  → ../../src/generated/hankel-bench.json (for the site)
import { mkdirSync, readFileSync, writeFileSync } from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";
import * as k from "../kit/iso-kit.mjs";
import * as G from "../kit/lathe.mjs";
import { ADDRESSES, EXAMPLE, LOADINGS, evalPoly, polyText, signed, stateOf } from "./model.mjs";
import { paperFigureCss, paperFigureSource, paperPlate } from "../paper-figure.mjs";
import { shipped, swingSource } from "../swing.mjs";

const HERE = dirname(fileURLToPath(import.meta.url));
const theme = process.argv.includes("--light") ? "light" : "dark";
const fragment = process.argv.includes("--fragment");

const WIDTH = 640;
const HEIGHT = 470;

// World: x along the address rail, y toward the viewer, z up; the deck's top is z = 0. The board's cell
// (p, q) sits at (X(q), Y(p)), so the anti-diagonal p + q = j runs across the screen at this camera.
const C = {
  CELL: 18,
  QX: -52,
  PY: -8,
  PLATE: { x: -86, y: -70, w: 162, d: 132, r: 8 },
  PLATE_H: 10,
  FOOT_H: 5,
  BOARD: { q0: -0.75, q1: 3.75, p0: -0.75, p1: 2.75, h: 4 },
  SOCKET: { r: 6.4 },
  COIN: { r: 5.1, t: 1.15 },
  CUP: { p: -1.25, r: 7.2, h: 2.6 },
  BAR: { half: 1.3, lift: 4.6, edge: 1.6 },
  RAIL: { x0: -72, x1: 72, y: -49, d: 6, h: 3 },
  CARRIAGE: { half: 8, y0: -52, y1: -40, z: 3, h: 4.6, tab: [-55.6, -52] },
  TAU: { zero: -15.7, unit: 31.4 },
  ROD: { y: -55.3, r: 0.5, bead: 1.15, wire: 0.32 },
  BACK: { y: -61, d: 3.2, h: 40 },
  TEMPLATE: { y: -57.8, d: 1.6, base: 5, datum: 22, amp: 13, soft: 2 },
  WEIGHT: { r: 4.2, h: 6.6 },
  DIAL: { x: 57, y: 27, r: 12.5 },
  TRAY: { x: -82, y: -38, w: 12, d: 40, r: 2.4 },
  RACK: { y: 47.5, d: 11, h: 2.6 },
};
const X = (q) => C.QX + C.CELL * q;
const Y = (p) => C.PY + C.CELL * p;
const XT = (tau) => C.TAU.zero + C.TAU.unit * tau;
// Sample the exact candidate addresses even when they fall between the uniform samples.
const TAUS = [...new Set([...ADDRESSES, ...Array.from({ length: 121 }, (_, i) => (7 * i - 320) / 200)])].sort((a, b) => a - b);
// The template's height over the datum: monotone in P, zero exactly where P is.
const lift = (value) => (C.TEMPLATE.amp * value) / Math.sqrt(value * value + C.TEMPLATE.soft * C.TEMPLATE.soft);

const BOARD_PLAN = { x: X(C.BOARD.q0), y: Y(C.BOARD.p0), w: C.CELL * (C.BOARD.q1 - C.BOARD.q0), d: C.CELL * (C.BOARD.p1 - C.BOARD.p0), r: 3 };
const CELLS = [0, 1, 2].flatMap((p) => [0, 1, 2, 3].map((q) => [p, q]));

const FIT = [
  ...k.boxCorners(C.PLATE, -C.PLATE_H - C.FOOT_H, 0),
  [C.PLATE.x + 8, C.BACK.y, C.BACK.h + 4],
  [C.PLATE.x + C.PLATE.w - 8, C.BACK.y, C.BACK.h + 4],
];
const VIEW = { pad: 22, azimuth: 50, elevation: 31 };
const P0 = k.fitProjection(FIT, WIDTH, HEIGHT, VIEW);
const FRAME = { points: FIT, width: WIDTH, height: HEIGHT, pad: VIEW.pad };
let P = P0;

// --- shared with the page --------------------------------------------------------------------

const at = (point) => k.iso(point, P);
const S = (paths, style) => k.solidSvg(paths, style);
const L = (d, style) => k.lineSvg(d, style);
const D = (points, style) => k.dotsSvg(points, style);
const M = (material, ...svg) => `<g data-mat="${material}">${svg.join("")}</g>`;
const depthAt = (x, y, z = 0) => k.depthOf([x, y, z], P);
const byDepth = (items, key = (item) => item) => [...items].sort((a, b) => depthAt(...key(a)) - depthAt(...key(b)));

// A stack of |n| coins standing at (x, y) from z0: marble for a positive moment, ink for a negative one.
// A seam at every coin, a darker one at every fifth, so the stack can be counted.
function coinStack(count, camera) {
  const { r, t } = C.COIN, top = count * t;
  const fine = [], fifth = [];
  for (let i = 1; i < count; i++) (i % 5 ? fine : fifth).push(k.sideArc(0, 0, r, i * t, camera, 18));
  return S(k.cylinder(0, 0, r, 0, top, camera, 32, 0.3), { tone: "hi", crease: "none", inner: L(fine.join(""), { tone: "lo" }) + L(fifth.join(""), { tone: "mid" }) })
    + L(k.ring(0, 0, r - 1.3, top, camera, 22), { tone: "lo" }) + L(k.ring(0, 0, r - 2.6, top, camera, 18), { tone: "faint" });
}
function coinsSvg(x, y, z0, n) {
  if (!n) return "";
  const count = Math.abs(n), scale = P.scale / P0.scale, [dx, dy] = at([x, y, z0]);
  coinsSvg.stacks ??= new Map();
  if (!coinsSvg.stacks.has(count)) coinsSvg.stacks.set(count, coinStack(count, { ...P0, origin: [0, 0] }));
  return M(n > 0 ? "marble" : "ink", `<g transform="translate(${dx.toFixed(2)} ${dy.toFixed(2)}) scale(${scale})">${coinsSvg.stacks.get(count)}</g>`);
}
const cellTop = () => C.BOARD.h;
const cupTop = () => C.CUP.h;
const cupAt = (j) => [X(j - C.CUP.p), Y(C.CUP.p)];

// The fold of the leading block H_w: an L-bar on the lines p = w − ½ and q = w − ½, from the board's
// back and left margins to the corner it turns at. It rises by `up` out of its slot.
function foldRing(w, grow = 0) {
  const h = C.BAR.half + grow, xc = X(w - 0.5), yc = Y(w - 0.5);
  const x0 = BOARD_PLAN.x + C.BAR.edge - grow, y0 = BOARD_PLAN.y + C.BAR.edge - grow;
  return [[x0, yc - h], [xc - h, yc - h], [xc - h, y0], [xc + h, y0], [xc + h, yc + h], [x0, yc + h]];
}
// Flush, a fold is an inlay level with the board; the largest raised frame is polished green jade.
function foldSvg(w, up, lit) {
  const ring = foldRing(w), x0 = BOARD_PLAN.x + C.BAR.edge, yc = Y(w - 0.5), z = C.BOARD.h + up;
  // w pips near the fold's left end: the order of the block it frames.
  const pips = Array.from({ length: w }, (_, i) => at([x0 + 2.6 + i * 2.3, yc, z]));
  if (up < 0.05) return M("jade", S(k.extrude(ring, C.BOARD.h, 0.001, P, { convex: false }), { tone: "mid", crease: "none" }), D(pips, { size: 0.45, tone: "lo" }));
  const edge = lit ? L(k.onTop([ring[0], ring[1], ring[2]], z, P), { className: "polished-edge" }) : "";
  return M(lit ? "jade" : "marble", S(k.extrude(ring, C.BOARD.h, up, P, { convex: false }), { tone: "hi", lit, crease: "lo" }), edge,
    D(pips, { size: 0.62, tone: lit ? "hi" : "mid" }));
}

// The template P(t) on its plate: a profile plate whose top edge stands lift(P(t)) over the datum. Built as
// one solid: the front face, the visible strips of the cut edge and the right end.
function templatePaths(heights) {
  const { y, d, base } = C.TEMPLATE, yf = y + d, yb = y;
  const xs = TAUS.map(XT);
  const zs = heights.map((h) => C.TEMPLATE.datum + h);
  const V = G.viewOf(P);
  const front = [[xs[0], yf, base], ...xs.map((x, i) => [x, yf, zs[i]]), [xs[xs.length - 1], yf, base]].map(at);
  const strips = [], crease = [], back = [];
  for (let i = 0; i + 1 < xs.length; i++) {
    const dx = xs[i + 1] - xs[i], dz = zs[i + 1] - zs[i];
    if (-dz * V[0] + dx * V[2] <= 0) continue;
    const quad = [[xs[i], yf, zs[i]], [xs[i + 1], yf, zs[i + 1]], [xs[i + 1], yb, zs[i + 1]], [xs[i], yb, zs[i]]].map(at);
    strips.push(k.pathOf(quad, true));
    crease.push([at([xs[i], yf, zs[i]]), at([xs[i + 1], yf, zs[i + 1]])]);
    back.push([at([xs[i], yb, zs[i]]), at([xs[i + 1], yb, zs[i + 1]])]);
  }
  const x1 = xs[xs.length - 1], z1 = zs[zs.length - 1];
  const end = [[x1, yf, base], [x1, yb, base], [x1, yb, z1], [x1, yf, z1]].map(at);
  const joined = (segments) => {
    const runs = [];
    for (const [a, b] of segments) {
      const last = runs[runs.length - 1];
      if (last && Math.hypot(last[last.length - 1][0] - a[0], last[last.length - 1][1] - a[1]) < 0.01) last.push(b);
      else runs.push([a, b]);
    }
    return runs.map((run) => k.pathOf(run)).join("");
  };
  const frontPath = k.pathOf(front, true), endPath = k.pathOf(end, true);
  const shades = ["", "", "", ""];
  shades[1] = endPath;
  shades[3] = frontPath;
  return {
    fill: frontPath + endPath + strips.join(""),
    top: strips.join(""),
    shades,
    crease: joined(crease),
    outline: frontPath + k.pathOf([end[1], end[2], end[3]]) + joined(back),
  };
}
const templateHeights = (poly) => TAUS.map((tau) => lift(evalPoly(poly, tau)));
function templateSvg(heights) {
  return M("marble", S(templatePaths(heights), { tone: "hi", crease: "lo" }));
}

// A station on the rail at address τ_i, loaded with weight a ∈ {−1, 0, 1}. Its feeler rod rises behind
// it to the datum, and its ball sits on the template's edge exactly when P(τ_i) = 0.
function stationSvg(i, weight, root) {
  const x = XT(ADDRESSES[i]), { half, y0, y1, z, h, tab } = C.CARRIAGE, top = z + h;
  const out = [];
  // Rod and bead first: they stand behind the carriage. The bead rides the datum wire.
  out.push(M("ink", S(k.cylinder(x, C.ROD.y, C.ROD.r, top, C.TEMPLATE.datum - top - C.ROD.bead * 0.8, P, 12), { tone: "mid", crease: "none" }), S(k.cylinder(x, C.ROD.y, 1.1, top, 1.2, P, 14), { tone: "hi" })));
  out.push(M(root ? "jade" : "ink", S(G.sphereOf([x, C.ROD.y, C.TEMPLATE.datum], C.ROD.bead, P), { tone: "hi" })));
  out.push(M("marble", S(k.slabOf({ x: x - 2.2, y: tab[0], w: 4.4, d: tab[1] - tab[0] + 0.5, r: 0.6 }, z + 1.4, h - 1.4, P, 2, 0.3), { tone: "mid" })));
  // The carriage: two cheeks down the rail's sides, a saddle across its top.
  out.push(M("marble", S(k.slabOf({ x: x - half, y: y1 - 3, w: 2 * half, d: 3, r: 0.8 }, 0.6, z - 0.6, P, 3, 0.3), { tone: "mid" })));
  out.push(M("marble", S(k.slabOf({ x: x - half, y: y0, w: 2 * half, d: y1 - y0, r: 1.4 }, z, h, P, 4, 0.6), { tone: "hi", inner: L(k.sideSeam({ x: x - half, y: y0, w: 2 * half, d: y1 - y0, r: 1.4 }, z + 1.6, P, 4), { tone: "faint" }) }),
    L(k.ring(x, (y0 + y1) / 2, C.WEIGHT.r + 1.2, top, P, 28), { tone: "lo" }),
    k.faceTextSvg(k.sideMatrix([x - 0.6, y1], z + 1.4, P, "left"), signed(ADDRESSES[i]), { size: 2.8, tone: "hi", anchor: "middle" }),
    D(k.corners({ x: x - half, y: y0, w: 2 * half, d: y1 - y0 }, 1.8).map(([cx, cy]) => at([cx, cy, top])), { size: 0.42 })));
  // The lock screw on the front cheek: a neck and a knurled head along +y.
  const F = G.frameAlong([x + half - 3.6, y1, z - 1.4], [0, 1, 0]);
  out.push(M("ink", S(G.disc(0, 1.2, 0.9, F, P), { tone: "mid" }), S(G.disc(1.2, 3.2, 1.9, F, P), { tone: "hi" })));
  // The weight: a calibration mass (marble +1, ink −1) on the saddle's socket; an empty socket holds a pin.
  const cy = (y0 + y1) / 2, w = C.WEIGHT;
  if (weight) out.push(M(weight > 0 ? "marble" : "ink",
    S(k.cylinder(x, cy, w.r, top, w.h, P, 32, 0.5), { tone: "hi", inner: L(k.sideArc(x, cy, w.r, top + 1.2, P, 20), { tone: "faint" }) }),
    S(k.cylinder(x, cy, 1.6, top + w.h, 1.2, P, 14), { tone: "mid" }),
    S(k.cylinder(x, cy, 2.5, top + w.h + 1.2, 1.8, P, 18, 0.3), { tone: "hi" })));
  else out.push(M("ink", S(k.cylinder(x, cy, 1, top, 2.2, P, 12), { tone: "mid" })));
  return out.join("");
}

// Round components keep the same silhouette under azimuth changes; place one projection at each anchor.
function turned(key, point, draw) {
  turned.parts ??= new Map();
  if (!turned.parts.has(key)) turned.parts.set(key, draw({ ...P0, origin: [0, 0] }));
  const [dx, dy] = at(point);
  return `<g transform="translate(${dx.toFixed(2)} ${dy.toFixed(2)}) scale(${P.scale / P0.scale})">${turned.parts.get(key)}</g>`;
}

// --- static art ------------------------------------------------------------------------------

function plate() {
  const out = [`<path class="iso-halo" d="${k.haloOf(C.PLATE, -C.PLATE_H - C.FOOT_H, C.PLATE_H, P)}"/>`];
  for (const [x, y] of byDepth(k.corners(C.PLATE, 18), ([x, y]) => [x, y])) {
    out.push(M("ink", S(k.cylinder(x, y, 7.5, -C.PLATE_H - C.FOOT_H, 1.6, P, 28), { tone: "lo" })));
    out.push(M("ink", S(k.cylinder(x, y, 5.6, -C.PLATE_H - C.FOOT_H + 1.6, C.FOOT_H - 1.6, P, 28), { tone: "mid" }), L(k.knurl(x, y, 5.6, -C.PLATE_H - C.FOOT_H + 1.6, -C.PLATE_H, 20, P), { tone: "lo" })));
  }
  const screws = k.corners(C.PLATE, 9);
  out.push(M("marble", S(k.slabOf(C.PLATE, -C.PLATE_H, C.PLATE_H, P, 8, 1.6), { tone: "mid", inner: L(k.sideSeam(C.PLATE, -4, P, 8), { tone: "faint" }) }),
    L(k.planOutline(k.insetPlan(C.PLATE, 5), 0, P), { tone: "lo" }), L(screws.map(([x, y]) => k.ring(x, y, 2.2, 0, P, 16)).join(""), { tone: "lo" }), D(screws.map(([x, y]) => at([x, y, 0])), { size: 0.5 })));
  return out.join("");
}

// The backboard behind the rail: a jade panel between two posts with a cap rail, a grid at the integer
// addresses, and the ledge and clamps that hold the template.
function backboard() {
  const { y, d, h } = C.BACK, x0 = XT(TAUS[0]) - 4, x1 = XT(TAUS.at(-1)) + 4, face = y + d;
  const panel = { x: x0 - 3.2, y, w: x1 - x0 + 6.4, d, r: 0.6 };
  const grid = [-1, 0, 1, 2].map((tau) => k.segment([XT(tau), face, C.TEMPLATE.base], [XT(tau), face, h], P)).join("");
  const posts = [x0 - 3.2, x1 + 3.2];
  const cap = { x: x0 - 3.2, y: y - 0.8, w: x1 - x0 + 6.4, d: d + 1.6, r: 0.6 };
  const ledge = { x: x0 + 1, y: face, w: x1 - x0 - 2, d: C.TEMPLATE.y + C.TEMPLATE.d + 0.6 - face, r: 0.4 };
  const clamps = [XT(-1.42), XT(2.42)].map((cx) => {
    const plan = { x: cx - 3.4, y: C.TEMPLATE.y + C.TEMPLATE.d, w: 6.8, d: 1.8, r: 0.4 }, F = G.frameAlong([cx, plan.y + plan.d, C.TEMPLATE.base + 3.4], [0, 1, 0]);
    return M("ink", S(k.slabOf(plan, C.TEMPLATE.base, 6.8, P, 2, 0.3), { tone: "mid" }), S(G.disc(0, 1.6, 1.7, F, P), { tone: "hi" }), L(G.circleOf(F, 1.6, 0.8, P), { tone: "lo" }));
  });
  return {
    back: [
      M("marble", S(k.slabOf(panel, 0, h, P, 2, 0.4), { tone: "mid", inner: L(k.sideSeam(panel, 3, P, 2), { tone: "faint" }) }),
        L(grid, { tone: "faint" }),
        D([[x0 + 2.4, face, h - 2.2], [x1 - 2.4, face, h - 2.2]].map(at), { size: 0.45 })),
      M("ink", S(k.slabOf(cap, h, 1.8, P, 2, 0.4), { tone: "mid" }), D([x0 + 6, (x0 + x1) / 2, x1 - 6].map((cx) => at([cx, y + d / 2, h + 1.8])), { size: 0.45 })),
      M("ink", S(k.slabOf(ledge, 0, C.TEMPLATE.base, P, 2, 0.3), { tone: "mid" })),
      post(posts[0]),
    ].join(""),
    front: clamps.join("") + datumWire() + post(posts[1]),
  };
}
// The datum: a taut wire across the template's face, post to post, at P = 0.
function datumWire() {
  const x0 = XT(TAUS[0]) - 4.6, x1 = XT(TAUS.at(-1)) + 4.6;
  const F = G.frameAlong([x0, C.ROD.y, C.TEMPLATE.datum], [1, 0, 0]);
  return M("ink", S(G.disc(0, x1 - x0, C.ROD.wire, F, P), { tone: "hi", crease: "none" }));
}
function post(px) {
  const y = C.ROD.y - 1.2;
  return M("ink", S(k.slabOf({ x: px - 3.2, y: y - 4, w: 6.4, d: 8, r: 1 }, 0, 2, P, 3, 0.3), { tone: "mid" }),
    S(k.cylinder(px, y, 2.6, 2, C.BACK.h + 1.8, P, 22), { tone: "mid", crease: "none", inner: L([12, 32].map((z) => k.sideArc(px, y, 2.6, z, P, 14)).join(""), { tone: "faint" }) }),
    S(k.cylinder(px, y, 3.4, C.TEMPLATE.datum - 1.4, 2.8, P, 24, 0.3), { tone: "hi" }),
    S(k.cylinder(px, y, 3.4, C.BACK.h + 3.8, 1.6, P, 24, 0.4), { tone: "hi" }));
}

function rail() {
  const { x0, x1, y, d, h } = C.RAIL;
  const plan = { x: x0, y, w: x1 - x0, d, r: 1 };
  const stops = [x0 + 2, x1 - 2].map((x) => M("ink", S(k.slabOf({ x: x - 2, y: y - 2.5, w: 4, d: d + 5, r: 0.8 }, 0, h + 2.6, P, 3, 0.4), { tone: "mid" }), D([at([x, y + d / 2, h + 2.6])], { size: 0.45 })));
  // The address scale on the rail's top: a tick every quarter, longer at the integers, the zero brightest.
  const ticks = { minor: [], major: [], zero: [] };
  for (let i = -7; i <= 10; i++) {
    const tau = i / 4, x = XT(tau), list = i === 0 ? ticks.zero : i % 4 ? ticks.minor : ticks.major;
    if (x >= x0 + 1 && x <= x1 - 1) list.push(k.lineOnTop([x, y], [x, y + (i % 4 ? 1.8 : 3.2)], h, P));
  }
  return stops[0] + M("ink", S(k.slabOf(plan, 0, h, P, 3, 0.5), { tone: "mid" }), L(ticks.minor.join(""), { tone: "lo" }), L(ticks.major.join(""), { tone: "mid" }), L(ticks.zero.join(""), { tone: "hi" })) + stops[1];
}

// Inside the board's rounded plan.
function onBoard([x, y]) {
  const { x: bx, y: by, w, d, r } = BOARD_PLAN;
  const dx = Math.max(bx + r - x, 0, x - (bx + w - r)), dy = Math.max(by + r - y, 0, y - (by + d - r));
  return x >= bx && x <= bx + w && y >= by && y <= by + d && dx * dx + dy * dy <= r * r;
}
function grooves(onTopOfBoard) {
  const out = [];
  for (let j = 0; j < 6; j++) {
    // From the cup down the anti-diagonal p + q = j: on the deck under the board's edge, then over the board
    // from the point where the line enters its rounded plan to the last cell of that anti-diagonal.
    const [cx, cy] = cupAt(j), u = [-1 / Math.SQRT2, 1 / Math.SQRT2];
    let t = 0;
    while (!onBoard([cx + u[0] * t, cy + u[1] * t]) && t < 200) t += 0.05;
    const entry = [cx + u[0] * t, cy + u[1] * t];
    const pEnd = Math.min(j, 2), qEnd = j - pEnd;
    if (!onTopOfBoard) out.push(k.lineOnTop([cx, cy], [entry[0] + u[0] * 3, entry[1] + u[1] * 3], 0, P));
    else if (qEnd <= 3) out.push(k.lineOnTop(entry, [X(qEnd) - u[0] * 1.4, Y(pEnd) - u[1] * 1.4], C.BOARD.h, P));
  }
  return L(out.join(""), { tone: "lo" });
}

// A cup: a turned jade pedestal with its moment index engraved on the front flange.
function cup(j) {
  const [x, y] = cupAt(j), stamp = [x + C.CUP.r + 2, y + 1];
  const tag = { x: x + C.CUP.r - 1.25, y: y - 2.8, w: 5.7, d: 5.6, r: 0.7 };
  return M("jade", S(k.slabOf(tag, 0, 0.85, P, 2, 0.25), { tone: "mid" }),
    turned("cup", [x, y, 0], (camera) => S(k.cylinder(0, 0, C.CUP.r + 0.8, 0, 0.9, camera, 32, 0.3), { tone: "lo" })
      + S(k.cylinder(0, 0, C.CUP.r, 0.9, C.CUP.h - 0.9, camera, 32, 0.5), { tone: "mid" })
      + L(k.ring(0, 0, C.SOCKET.r - 0.4, C.CUP.h, camera, 27), { tone: "lo" })
      + L(k.ring(0, 0, 1.6, C.CUP.h, camera, 14), { tone: "faint" })),
    k.faceTextSvg(k.topMatrix(stamp, 0.85, P), "M" + "₀₁₂₃₄₅"[j], { size: 2.7, tone: "hi", anchor: "middle" }));
}

function board() {
  return M("marble", S(k.slabOf(BOARD_PLAN, 0, C.BOARD.h, P, 4, 0.6), { tone: "mid" }),
    D(k.corners(BOARD_PLAN, 2.4).map(([x, y]) => at([x, y, C.BOARD.h])), { size: 0.45 }),
    k.faceTextSvg(k.sideMatrix([BOARD_PLAN.x + BOARD_PLAN.w, BOARD_PLAN.y + BOARD_PLAN.d - 10], 0.9, P, "right"), "H = V·diag(a)·Vᵀ", { size: 2.6, tone: "hi" }));
}
// The board top under the folds and stacks: the fold slots and the right-hand column's rule.
function boardTop() {
  const slots = [1, 2, 3].map((w) => k.onTop(foldRing(w, 0.45), C.BOARD.h, P, true)).join("");
  return grooves(true) + L(slots, { tone: "faint" });
}
// A cell's socket: an engraved ring and a centre mark; the right-hand column's rings are doubled.
function pad(p, q) {
  const x = X(q), y = Y(p), z = C.BOARD.h;
  return L(k.ring(x, y, C.SOCKET.r, z, P, 32) + (q === 3 ? k.ring(x, y, C.SOCKET.r + 1, z, P, 32) : ""), { tone: q === 3 ? "mid" : "lo" }) + L(k.ring(x, y, 1.4, z, P, 14), { tone: "faint" });
}

function dial() {
  const { x, y, r } = C.DIAL, base = { x: x - r - 3, y: y - r - 3, w: 2 * r + 6, d: 2 * r + 6, r: 3 };
  const top = 9.4;
  const ticks = k.radialTicks(x, y, r - 1.2, 12, 4, top, [1.1, 2.1], P, -Math.PI * 0.75, Math.PI * 1.5);
  // r pips inside the major tick for order r.
  const numerals = [0, 1, 2, 3].map((order) => {
    const a = orderAngle(order), rr = r - 4.8;
    return k.faceTextSvg(k.topMatrix([x + Math.sin(a) * rr, y - Math.cos(a) * rr + 1], top, P), String(order), { size: 2.9, tone: "hi", anchor: "middle" });
  }).join("");
  return M("ink", S(k.slabOf(base, 0, 2, P, 4, 0.5), { tone: "mid" }), D(k.corners(base, 2.2).map(([cx, cy]) => at([cx, cy, 2])), { size: 0.45 })) +
    M("jade", S(k.cylinder(x, y, r + 0.8, 2, 3, P, 64, 0.5), { tone: "mid" }), L(k.knurl(x, y, r + 0.8, 2.3, 4.8, 72, P, 0.3), { tone: "lo" })) +
    M("marble", S(k.cylinder(x, y, r, 5, top - 5, P, 64, 0.8), { tone: "hi", crease: "lo" }), L(k.ring(x, y, r - 1.2, top, P, 64), { tone: "lo" }),
      L(ticks.minor, { tone: "lo" }), L(ticks.major, { tone: "mid" }), L(k.ring(x, y, 1.4, top, P, 16), { tone: "lo" }), numerals);
}
// Needle angle for an order r ∈ [0, 3] (eased): the four major ticks sit at −135°, −45°, 45°, 135°.
const orderAngle = (order) => -Math.PI * 0.75 + (order * Math.PI) / 2;
const needleD = (order) => {
  const { x, y, r } = C.DIAL, a = orderAngle(order), top = 9.6;
  const tip = [x + Math.sin(a) * (r - 6.2), y - Math.cos(a) * (r - 6.2), top], tail = [x - Math.sin(a) * 3, y + Math.cos(a) * 3, top];
  return k.pathOf([at(tail), at(tip)]);
};

// Spare weights: two marble, two ink, in a tray beside the board.
function tray() {
  const t = C.TRAY, wells = [0, 1, 2, 3].map((i) => [t.x + t.w / 2, t.y + 6 + i * 9.4]);
  const out = [M("ink", S(k.slabOf(t, 0, 2.4, P, 4, 0.4), { tone: "mid" }), L(wells.map(([x, y]) => k.ring(x, y, C.WEIGHT.r + 0.5, 2.4, P, 24)).join(""), { tone: "lo" }))];
  const w = C.WEIGHT;
  for (const [index, [x, y]] of wells.entries()) out.push(M(index < 2 ? "marble" : "ink",
    S(k.cylinder(x, y, w.r, 2.4, w.h, P, 32, 0.5), { tone: "hi", inner: L(k.sideArc(x, y, w.r, 3.6, P, 20), { tone: "faint" }) }),
    S(k.cylinder(x, y, 1.6, 2.4 + w.h, 1.2, P, 14), { tone: "mid" }), S(k.cylinder(x, y, 2.5, 3.6 + w.h, 1.8, P, 18, 0.3), { tone: "hi" })));
  return out.join("");
}

// The readback rack along the front: a socket under each address, where the Vandermonde solve on the
// recovered support sets its weight. A τ scale runs along its front face.
function rack() {
  const { y, d, h } = C.RACK, x0 = XT(-1.4), x1 = XT(2.4), plan = { x: x0, y, w: x1 - x0, d, r: 2 };
  const ticks = { minor: [], major: [], zero: [] };
  for (let i = -5; i <= 9; i++) {
    const x = XT(i / 4), list = i === 0 ? ticks.zero : i % 4 ? ticks.minor : ticks.major;
    list.push(k.segment([x, y + d, h], [x, y + d, h - (i % 4 ? 1 : 1.8)], P));
  }
  return M("jade", S(k.slabOf(plan, 0, h, P, 4, 0.5), { tone: "mid" }), L(ticks.minor.join(""), { tone: "lo" }), L(ticks.major.join(""), { tone: "mid" }), L(ticks.zero.join(""), { tone: "hi" }),
    L(ADDRESSES.map((tau) => k.ring(XT(tau), y + d / 2, C.WEIGHT.r + 0.6, h, P, 24)).join(""), { tone: "lo" }),
    D([at([x0 + 2.2, y + d / 2, h]), at([x1 - 2.2, y + d / 2, h])], { size: 0.45 }));
}
function readbackSvg(weights) {
  const { y, d, h } = C.RACK, w = C.WEIGHT;
  return weights.map((a, i) => {
    if (!a) return "";
    const x = XT(ADDRESSES[i]), cy = y + d / 2;
    return M(a > 0 ? "marble" : "ink", S(k.cylinder(x, cy, w.r, h, w.h, P, 32, 0.5), { tone: "hi", inner: L(k.sideArc(x, cy, w.r, h + 1.2, P, 20), { tone: "faint" }) }),
      S(k.cylinder(x, cy, 1.6, h + w.h, 1.2, P, 14), { tone: "mid" }), S(k.cylinder(x, cy, 2.5, h + w.h + 1.2, 1.8, P, 18, 0.3), { tone: "hi" }));
  }).join("");
}

// Each cup and the cells on its anti-diagonal are one readout of the same moment.
function composition(view) {
  const blockOf = ([p, q]) => (q === 3 ? 4 : Math.max(p, q) + 1);
  const cells = (block) => byDepth(CELLS.filter((cell) => blockOf(cell) === block), ([p, q]) => [X(q), Y(p)]);
  const stack = ([p, q]) => `<g data-part="cell-${p}-${q}">${coinsSvg(X(q), Y(p), cellTop(), view.shown[p + q])}</g>`;
  const fold = (w) => `<g data-part="fold-${w}">${foldSvg(w, view.lifts[w - 1], view.lit === w)}</g>`;
  const block = (b) => cells(b).map((cell) => pad(...cell) + stack(cell)).join("");
  const panel = backboard();
  return [
    plate(),
    tray(),
    panel.back,
    `<g data-part="template">${templateSvg(view.heights)}</g>`,
    panel.front,
    rail(),
    ...[0, 1, 2].map((i) => `<g data-part="station-${i}" data-station="${i}">${stationSvg(i, view.weights[i], view.roots[i])}</g>`),
    grooves(false),
    ...byDepth(view.shown.map((_, j) => j), cupAt).map((j) => cup(j) + `<g data-part="cup-${j}">${coinsSvg(...cupAt(j), cupTop(), view.shown[j])}</g>`),
    board(),
    boardTop(),
    block(1), fold(1), block(2), fold(2), block(3), fold(3), block(4),
    rack(),
    `<g data-part="readback">${readbackSvg(view.back)}</g>`,
    dial(),
    `<path data-part="needle" class="iso-line" data-tone="lit" data-free="" d="${needleD(view.order)}" style="stroke-width:1.2"/>`,
    D([at([C.DIAL.x, C.DIAL.y, 9.6])], { size: 1.1, tone: "hi" }),
  ].join("");
}

// The resting view of a loading.
function viewOf(s) {
  return {
    weights: [...s.weights],
    shown: [...s.moments],
    lifts: s.dets.map((d) => (d ? C.BAR.lift : 0)),
    lit: s.r,
    order: s.r,
    heights: templateHeights(s.poly),
    roots: ADDRESSES.map((_, i) => s.support.includes(i)),
    back: [...s.recovered],
  };
}
const INITIAL = stateOf(EXAMPLE), REST = viewOf(INITIAL);
const readingsOf = (s) => ["M = (" + s.moments.map(signed).join(", ") + ")", "det H₁–₃ = (" + s.dets.map(signed).join(", ") + ")", "r = " + s.r, "P = " + polyText(s.poly)];
const weightLabel = (i, weight) => "τ " + signed(ADDRESSES[i]) + " · " + (weight > 0 ? "+" : "") + signed(weight);

const art = composition(REST);

const CSS = `${paperFigureCss}
.hb-svg [data-station]{cursor:pointer}
`;

const strip = (file) => readFileSync(join(HERE, file), "utf8").replace(/^export /gm, "");
const kitSource = strip("../kit/iso-kit.mjs");
const latheSource = `const LATHE = (() => {\n${strip("../kit/lathe.mjs").replace(/^import .*$/gm, "")}\nreturn { ${Object.keys(G).join(", ")} };\n})();`;
const MODEL = ["ADDRESSES", "EXAMPLE", "LOADINGS", "evalPoly", "polyText", "signed", "stateOf"];
const modelSource = `const { ${MODEL.join(", ")} } = (() => {\n${strip("model.mjs")}\nreturn { ${MODEL.join(", ")} };\n})();`;
const live = `
const P0 = ${JSON.stringify(P0)};
let P = P0;
${shipped({ C, BOARD_PLAN, CELLS, FRAME, TAUS })}
const k = { ${Object.keys(k).join(", ")} };
const G = LATHE;
${shipped({ X, Y, XT, lift, at, S, L, D, M, depthAt, byDepth, coinStack, coinsSvg, cellTop, cupTop, cupAt, onBoard, foldRing, foldSvg, templatePaths, templateHeights, templateSvg, stationSvg, turned, plate, backboard, datumWire, post, rail, grooves, cup, board, boardTop, pad, dial, orderAngle, needleD, tray, rack, readbackSvg, composition, viewOf, readingsOf, weightLabel })}
${swingSource}
${paperFigureSource}
const root = document.querySelector('[data-figure="hankel-bench"]');
const stage = root.querySelector(".iso-stage");
const svgEl = stage.querySelector("svg");
const paintPart = partPainter(stage);
const readout = root.querySelector("[data-readout]");
const still = matchMedia("(prefers-reduced-motion: reduce)");
const controls = root.querySelector(".paper-figure-controls");
const stations = [...controls.querySelectorAll("[data-weight]")];
let weights = [...EXAMPLE], state = stateOf(weights), target = viewOf(state);
const view = viewOf(state);
let fromHeights = target.heights, morph = 1, coinClock = 0, phase = "rest";
let touring = !still.matches, tourAt = 0, tourClock = 0;
const TOUR = [[-1, 1, 0], [0, 0, 1], [1, 1, 0], [-1, 1, 1], [1, 0, -1]];

function say() {
  const readings = readingsOf(state);
  if (readout.firstElementChild && readout.textContent === readings.join(" · ")) return;
  const parts = readings.flatMap((text, i) => {
    const item = document.createElement("span");
    item.textContent = text;
    return i ? [" · ", item] : [item];
  });
  readout.replaceChildren(...parts);
}
function load(next) {
  weights = [...next];
  state = stateOf(weights);
  target = viewOf(state);
  view.weights = target.weights;
  view.roots = [false, false, false];
  view.back = [0, 0, 0];
  view.lit = 0;
  fromHeights = view.heights;
  morph = 0;
  coinClock = 0;
  phase = "moments";
  for (let i = 0; i < weights.length; i++) stations[i].textContent = weightLabel(i, weights[i]);
  if (still.matches) settle();
  else { readout.textContent = root.dataset.working; paint(); }
}
function settle() {
  Object.assign(view, target, { shown: [...target.shown], lifts: [...target.lifts] });
  phase = "rest";
  paint();
  say();
}
function step(dt) {
  if (phase === "moments") {
    coinClock += dt;
    if (coinClock >= 0.032) {
      coinClock -= 0.032;
      for (let j = 0; j < view.shown.length; j++) view.shown[j] += Math.sign(target.shown[j] - view.shown[j]);
    }
    view.lifts = view.lifts.map((have) => easeTo(have, 0, dt, 0.1, 0.08));
    if (view.shown.every((m, j) => m === target.shown[j])) phase = "recovery";
  }
  if (phase === "recovery") {
    view.lifts = view.lifts.map((have, i) => easeTo(have, target.lifts[i], dt, 0.14, 0.025));
    view.order = easeTo(view.order, target.order, dt, 0.18, 0.008);
    morph = Math.min(1, morph + dt / 0.85);
    const t = morph * morph * (3 - 2 * morph);
    view.heights = fromHeights.map((h, i) => h + (target.heights[i] - h) * t);
    if (morph === 1 && view.order === target.order && view.lifts.every((h, i) => h === target.lifts[i])) settle();
  }
  if (phase !== "rest") paint();
  else if (touring) {
    tourClock += dt;
    if (tourClock > 4.2) nextExample();
  }
  return touring || phase !== "rest";
}
function paint() {
  for (const [j, n] of view.shown.entries()) paintPart("cup-" + j, n, () => coinsSvg(...cupAt(j), cupTop(), n));
  for (const [p, q] of CELLS) {
    const n = view.shown[p + q];
    paintPart("cell-" + p + "-" + q, n, () => coinsSvg(X(q), Y(p), cellTop(), n));
  }
  for (const [i, up] of view.lifts.entries()) {
    const w = i + 1, lit = view.lit === w;
    paintPart("fold-" + w, up + ":" + lit, () => foldSvg(w, up, lit));
  }
  paintPart("template", view.heights, () => templateSvg(view.heights));
  paintPart("readback", view.back.join(), () => readbackSvg(view.back));
  for (const [i, weight] of view.weights.entries()) {
    paintPart("station-" + i, weight + ":" + view.roots[i], () => stationSvg(i, weight, view.roots[i]));
  }
  const needle = svgEl.querySelector('[data-part="needle"]'), d = needleD(view.order);
  if (needle.getAttribute("d") !== d) needle.setAttribute("d", d);
}
const run = playOnScreen(stage, still, step, () => { touring = false; settle(); });
const hold = () => { touring = false; readout.setAttribute("aria-live", "polite"); };
function nextExample() {
  tourClock = 0;
  tourAt = (tourAt + 1) % TOUR.length;
  load(TOUR[tourAt]);
  run();
}
root.addEventListener("focusin", hold);
const turn = (i) => { hold(); const next = [...weights]; next[i] = next[i] === 1 ? -1 : next[i] + 1; load(next); run(); };
const browse = (by) => { hold(); const at = LOADINGS.findIndex((w) => w.join() === weights.join()); load(LOADINGS[(at + by + LOADINGS.length) % LOADINGS.length]); run(); };
stations.forEach((button, i) => button.addEventListener("click", () => turn(i)));
controls.querySelector("[data-example]").addEventListener("click", () => { hold(); nextExample(); });
stage.addEventListener("click", (event) => {
  const station = event.target.closest("[data-station]");
  if (station) turn(Number(station.dataset.station));
});
stage.addEventListener("keydown", (event) => {
  if (event.key === "1" || event.key === "2" || event.key === "3") turn(Number(event.key) - 1);
  else if (event.key === "ArrowRight" || event.key === "ArrowUp") browse(1);
  else if (event.key === "ArrowLeft" || event.key === "ArrowDown") browse(-1);
  else if (event.key === " " || event.key === "Enter") { hold(); nextExample(); }
  else return;
  event.preventDefault();
});
mountSwing(stage, { touch: false, limit: 26, home: 2500, onHold: hold, onDragStart: run.pause, onDragEnd: run.resume, onSwing: (angle) => { P = swingOf(k.iso, P0, FRAME, angle); svgEl.innerHTML = composition(view); paintPart.reset(); } });
say();
// For checks: drive.mjs loads the bench directly.
window.__hankelBench = (next) => { hold(); load(next); settle(); };
`;

const COPY = {
  en: {
    title: "Hankel order bench",
    hint: "Drag to rotate · ← → browse all loadings",
    working: "Measuring moments and recovering the weights…",
    example: "Next example",
    controls: "Change the signed weights",
    keys: ["Green raised frame · largest nonsingular leading block", "Raised frame · det H_w ≠ 0, flush · det H_w = 0", "White is positive, graphite is negative"],
    refs: ["Theorem 6.2", "Example 1.1(d)"],
    caption: [
      "Six power moments recover the weights at three known candidate addresses, even when signed weights cancel. Each cup represents one moment M_j = Σ a τ^j. Cells (p, q) share the moment M_{p+q} along each anti-diagonal. The fourth column supplies M₃, M₄, M₅ for the recurrence.",
      "In Example 1.1(d), the weights −1 and +1 cancel in H₁ = [0]. The determinants of H₁, H₂, H₃ are 0, −4, 0. The raised H₂ frame gives the support size r = 2. In general, det H_r is nonzero and all larger blocks are singular. An empty source has r = 0, with det H₀ = 1.",
      "Solving the recurrence using H₂ gives the profile P(t) = t² − 1. Its edge meets the reference line at the active addresses −1 and 1. A Vandermonde solve at those addresses recovers the weights −1 and +1 in the front rack.",
    ],
    aria: "Hankel bench. Keys 1 to 3 change the three weights. Arrow keys browse all loadings. Space shows the next example.",
    alt: "Three signed weights feed six moment cups and a Hankel matrix. The largest nonsingular leading block raises a green frame and sets the dial. The polynomial profile meets the reference line at the recovered addresses.",
  },
  zh: {
    title: "Hankel 定阶台",
    hint: "拖动旋转 · ← → 浏览全部装载",
    working: "正在计算矩并恢复权重…",
    example: "下个例子",
    controls: "更改有号权重",
    keys: ["玉绿升框 · 最大非奇异首块", "升起 · det H_w ≠ 0，平齐 · det H_w = 0", "白色表示正值，石墨色表示负值"],
    refs: ["定理 6.2", "例 1.1(d)"],
    caption: [
      "即使有号权重相互抵消，六个幂矩仍能恢复三个已知候选地址上的权重。每只杯子盛放一个矩 M_j = Σ a τ^j，盘面格 (p, q) 在同一条反对角线上共享 M_{p+q}。第四列给出递推所需的 M₃、M₄、M₅。",
      "例 1.1(d) 的权重 −1 与 +1 在 H₁ = [0] 中相消。H₁、H₂、H₃ 的行列式依次为 0、−4、0。最大升框 H₂ 给出支撑大小 r = 2。一般地，det H_r 非零，更大的首块均奇异。空源对应 r = 0，约定 det H₀ = 1。",
      "由 H₂ 解递推方程得到曲线 P(t) = t² − 1。曲线在两个有权重的地址 −1 与 1 处碰到基准线。在这两个地址上解 Vandermonde 方程组，前方托架给出恢复的权重 −1 与 +1。",
    ],
    aria: "Hankel 定阶台。数字键 1 至 3 更改权重，方向键浏览全部装载，空格切换示例。",
    alt: "三处有号权重生成六杯矩并排成 Hankel 矩阵。最大的非奇异首块升起玉绿边框，表盘读出它的阶。多项式曲线在恢复的地址处接触基准线。",
  },
};
const bodyOf = (lang) => {
  const copy = COPY[lang];
  const svg = k.figureSvg({ width: WIDTH, height: HEIGHT, className: "hb-svg paper-figure-art", label: copy.alt, body: art });
  const buttons = ADDRESSES.map((_, i) => `<button type="button" data-weight="${i}">${weightLabel(i, EXAMPLE[i])}</button>`).join("");
  return `<div data-figure="hankel-bench" lang="${lang}" data-working="${copy.working}">${paperPlate({
    title: copy.title,
    hint: copy.hint,
    readout: readingsOf(INITIAL).join(" · "),
    keys: [
      { mark: "green", label: copy.keys[0] },
      { mark: "raised", label: copy.keys[1] },
      { mark: "dim", label: copy.keys[2] },
    ],
    caption: copy.caption,
    refs: copy.refs,
    body: `<div class="iso-stage paper-figure-stage" tabindex="0" role="group" aria-label="${copy.aria}">${svg}</div><div class="paper-figure-controls" role="group" aria-label="${copy.controls}">${buttons}<button type="button" data-example>${copy.example}</button></div>`,
  })}</div>`;
};

const script = `{\n${kitSource}\n${latheSource}\n${modelSource}\n${live}\n}`;
if (fragment) {
  const outDir = join(HERE, "../../src/generated");
  mkdirSync(outDir, { recursive: true });
  writeFileSync(join(outDir, "hankel-bench.json"), JSON.stringify({ html: { zh: bodyOf("zh"), en: bodyOf("en") }, css: CSS, script: script.replace(/<\/(script)/gi, "<\\/$1") }));
  console.log("wrote src/generated/hankel-bench.json");
} else {
  mkdirSync(join(HERE, "out"), { recursive: true });
  const lang = process.argv.includes("--zh") ? "zh" : "en";
  const name = theme === "light" ? "hankel-bench-light.html" : "hankel-bench.html";
  writeFileSync(join(HERE, "out", name), k.pageHtml({ title: COPY[lang].title, theme, body: `<style>${CSS}</style>${bodyOf(lang)}`, script, width: 740 }));
  console.log("wrote out/" + name);
}
