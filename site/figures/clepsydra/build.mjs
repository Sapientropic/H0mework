// Fig: a stone water clock for the four claims. A spring jar on a stepped stand pours three ways: to a
// basin anyone may draw from, into the clock's own vessel whose float arrow measures the keeper's term,
// and down a paid gate onto a waterwheel. In front stands a sealed jar a contribution filled once, its
// arrow showing what is left of Q, its spigot turning to whoever holds the tally (Results 4, 5 and 7 and
// Principles 2–4 and 6 of "The Economic Constitution of Possibility").
//   bun build.mjs [--light]   → out/clepsydra[-light].html (standalone, for checks)
//   bun build.mjs --fragment  → ../../src/generated/clepsydra.json (for the site)
import { mkdirSync, readFileSync, writeFileSync } from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";
import * as k from "../kit/iso-kit.mjs";
import * as G from "../kit/lathe.mjs";
import * as MD from "./model.mjs";
import { shipped, SWING_CSS, swingSource } from "../swing.mjs";

const HERE = dirname(fileURLToPath(import.meta.url));
const theme = process.argv.includes("--light") ? "light" : "dark";
const fragment = process.argv.includes("--fragment");

const WIDTH = 640;
const HEIGHT = 460;

// World: x across the stand, y toward the viewer, z up; the deck's top is z = 0. The stand rises in three
// steps at the back; the spring jar stands on the top step.
const C = {
  BASE: { x: -100, y: -44, w: 200, d: 88, r: 5 },
  BASE_Z: [-18, 0],
  FOOT: { r: 6, h: 4, inset: 16 },
  FACE: 44,
  STEPS: [{ x: -46, y: -42, w: 92, d: 30, r: 1.2, z: 0, h: 16 }, { x: -30, y: -42, w: 60, d: 19, r: 1.2, z: 16, h: 16 }, { x: -14, y: -42, w: 28, d: 12, r: 1.2, z: 32, h: 14 }],
  SOURCE: [0, -36, 46],
  // Each trough: a run from the spring jar's side spout, then down to its end.
  LEFT: [[-11, -36, 52], [-52, -36, 33], [-60, 0, 17]],
  RIGHT: [[11, -36, 52], [54, -36, 34]],
  VESSEL: [0, -20, 16, 7.2, 16], // the clock's receiving vessel: x, y, z, r, h
  RULER: [10.5, -20],
  STEP_UP: 3.4, // arrow rise per unit of time
  SEAL: [20, -15],
  TABLET: [-19, -17],
  BASIN: [-66, 14, 14, 8],
  BOWLS: [[-84, 32], [-52, 34]],
  GATE_X: 36,
  COINBOX: [36, -25],
  WHEEL: [62, -36, 20, 11, 6], // overshot: centre x, y, z, radius, width (axis along y)
  PIVOT: [69, -10, 17], // the hammer's pivot, level with the wheel's shaft
  LAMPS: [84, -22],
  JAR: [0, 22, 10, 20], // the contribution's jar: x, y, r, h
  QRULER: [-14, 22],
  Q_UP: 2.4,
  CUPS: [[22, 16], [22, 30]],
  RACK: [34, 23],
  PLATE: [52, 92],
};

const FIT = [
  ...k.boxCorners(C.BASE, C.BASE_Z[0] - C.FOOT.h, 0),
  [0, C.SOURCE[1], C.SOURCE[2] + 22],
  [C.RULER[0], C.RULER[1], C.VESSEL[2] + C.VESSEL[4] + 8 * C.STEP_UP + 4],
];
const VIEW = { pad: 22, azimuth: 72, elevation: 26 };
const P0 = k.fitProjection(FIT, WIDTH, HEIGHT, VIEW);
const FRAME = { points: FIT, width: WIDTH, height: HEIGHT, pad: VIEW.pad };
let P = P0;

// --- shared with the page --------------------------------------------------------------------

const X3 = [1, 0, 0], Y3 = [0, 1, 0], Z3 = [0, 0, 1];
const at = (point) => k.iso(point, P);
const S = (paths, style) => k.solidSvg(paths, style);
const L = (d, style) => k.lineSvg(d, style);
const D = (points, style) => k.dotsSvg(points, style);
const M = (material, ...svg) => `<g data-mat="${material}">${svg.join("")}</g>`;
const n2 = (v) => (Math.round(v * 100) / 100).toString();
const faceY = (y) => k.sideMatrix([0, y], 0, P, "left");
const rectD = (u0, v0, u1, v1, r = 0) => k.pathOf(k.roundedPlan({ x: u0, y: v0, w: u1 - u0, d: v1 - v0, r }, 4), true);
const box = (plan, z, h, style, steps = 3, bevel = 0) => S(k.slabOf(plan, z, h, P, steps, bevel), style);
const cyl = (x, y, r, z, h, style, steps = 20, bevel = 0) => S(k.cylinder(x, y, r, z, h, P, steps, bevel), style);
const FV = (x, y, z) => G.frameOf([x, y, z], Z3, X3, Y3);
const unit = (v) => { const n = Math.hypot(...v) || 1; return v.map((c) => c / n); };
const rod = (a, b, r, style, steps) => {
  const d = [b[0] - a[0], b[1] - a[1], b[2] - a[2]];
  const length = Math.hypot(...d);
  return length < 0.05 ? "" : S(G.disc(0, length, r, G.frameAlong(a, d), P, steps ? { steps } : {}), style);
};
// A falling stream is a tapered sheet with a narrow highlight, both driven by the same flow envelope.
const fall = (a, b, w = 1.2, opacity = 1) => {
  const sheet = k.pathOf([at([a[0] - w / 2, a[1], a[2]]), at([a[0] + w / 2, a[1], a[2]]), at([b[0] + w * 0.35, b[1], b[2]]), at([b[0] - w * 0.35, b[1], b[2]])], true);
  const shine = k.pathOf([at([a[0] - w * 0.12, a[1] + 0.02, a[2]]), at([b[0] - w * 0.08, b[1] + 0.02, b[2]])]);
  return `<path class="cl-fall" style="opacity:${n2(opacity)}" d="${sheet}"/><path class="cl-stream-shine" style="opacity:${n2(opacity * 0.75)}" d="${shine}"/>`;
};
const WATER_DEFS = `<defs>
  <linearGradient id="cl-water-fill" x1="0" y1="0" x2="1" y2="1"><stop offset="0" stop-color="var(--cl-water-light)"/><stop offset=".55" stop-color="var(--cl-water)"/><stop offset="1" stop-color="var(--cl-water-edge)"/></linearGradient>
  <linearGradient id="cl-stream-fill" x1="0" y1="0" x2="1" y2="0"><stop offset="0" stop-color="var(--cl-water-edge)"/><stop offset=".42" stop-color="var(--cl-water-light)"/><stop offset="1" stop-color="var(--cl-water)"/></linearGradient>
</defs>`;
const shadow = (x, y, r, o = 0.35) => `<path class="iso-halo" d="${k.haloOf({ x: x - r, y: y - r, w: 2 * r, d: 2 * r, r }, 0, 0.1, P)}" style="filter:blur(2.5px);opacity:calc(var(--anatomy-halo-opacity) * ${o})"/>`;

// --- the base and the stand ---------------------------------------------------------------------

function base() {
  const { BASE, BASE_Z, FOOT } = C;
  const out = [`<path class="iso-halo" d="${k.haloOf(BASE, BASE_Z[0] - FOOT.h, BASE_Z[1] - BASE_Z[0], P)}"/>`];
  const feet = k.corners(BASE, FOOT.inset).sort((a, b) => k.depthOf([...a, 0], P) - k.depthOf([...b, 0], P));
  for (const [x, y] of feet) out.push(cyl(x, y, FOOT.r, BASE_Z[0] - FOOT.h, FOOT.h, { tone: "mid" }, 28, 0.4));
  out.push(box(BASE, BASE_Z[0], -BASE_Z[0] - 3, { tone: "hi", inner: L(k.sideSeam(BASE, BASE_Z[0] + 3, P, 6), { tone: "faint" }) }, 6, 1));
  const deck = k.insetPlan(BASE, 1.5);
  const [p0, p1] = C.PLATE;
  const plate = `<g transform="${faceY(C.FACE + 0.02)}">${L(rectD(p0, 5, p1, 14, 1.2), { tone: "faint" })}${L(`M${p0 + 6} 8H${p1 - 10}M${p0 + 6} 10H${p1 - 16}M${p0 + 6} 12H${p1 - 22}`, { tone: "faint", free: true })}</g>`;
  return M("ink", ...out, plate, counterFace(), D([[p0 + 2.4, -7], [p1 - 2.4, -7], [p0 + 2.4, -12], [p1 - 2.4, -12]].map(([u, z]) => at([u, C.FACE, z])), { size: 0.45 }))
    + M("marble", box(deck, -3, 3, { tone: "mid" }, 6, 0.8), L(k.planOutline(k.insetPlan(deck, 3.5), 0, P), { tone: "faint" }), D(k.corners(deck, 6).map(([x, y]) => at([x, y, 0])), { size: 0.5 }),
      L(k.corners(deck, 6).map(([x, y]) => k.ring(x, y, 1.6, 0, P, 14)).join(""), { tone: "faint" }));
}
// The register on the base's face: what the cups have received, plus what is left, equals Q.
const COUNTER = { cells: [-26, -10, 8], v: [5, 13.4] };
function counterFace() {
  const { cells, v } = COUNTER;
  const [a, b] = v;
  const plus = `M${cells[0] + 6.2} 9.2H${cells[1] - 6.2}M${(cells[0] + cells[1]) / 2} 7.4V11`;
  const equals = `M${cells[1] + 6.6} 8.3H${cells[2] - 6.6}M${cells[1] + 6.6} 10.1H${cells[2] - 6.6}`;
  const screws = [[cells[0] - 6.6, -(a - 0.2)], [cells[2] + 6.6, -(a - 0.2)], [cells[0] - 6.6, -(b + 0.2)], [cells[2] + 6.6, -(b + 0.2)]];
  return `<g transform="${faceY(C.FACE + 0.02)}">${cells.map((u) => `<path class="cl-window" d="${rectD(u - 4, a, u + 4, b, 1)}"/>`).join("")}${L(cells.map((u) => rectD(u - 4, a, u + 4, b, 1)).join("") + rectD(cells[0] - 8, a - 1.6, cells[2] + 8, b + 1.6, 1.6), { tone: "faint" })}${L(plus + equals, { tone: "mid", free: true })}</g>`
    + D(screws.map(([u, z]) => at([u, C.FACE, z])), { size: 0.45 });
}
function counter(state) {
  const { cells, v } = COUNTER;
  const got = MD.receivedFor(state.account, state.origin), left = MD.remainingFor(state.account, state.origin);
  const digit = (u, n, lit) => `<text class="cl-digit${lit ? " cl-q" : ""}" transform="${faceY(C.FACE + 0.05)} translate(${u} ${v[1] - 1.4})" font-size="7.4" text-anchor="middle">${n}</text>`;
  return digit(cells[0], got) + digit(cells[1], left) + digit(cells[2], MD.Q, true);
}
// The stepped stand: three marble steps, each with a jade nosing and its joints.
function stand() {
  const out = [];
  for (const [i, s] of C.STEPS.entries()) {
    // Each riser is laid in blocks: vertical joints across its front, a sunk panel in each block.
    const front = s.y + s.d, z1 = s.z + s.h - 1.4;
    const blocks = Math.max(2, Math.round(s.w / 23));
    const joints = [], panels = [];
    for (let j = 0; j < blocks; j++) {
      const u0 = s.x + (s.w * j) / blocks, u1 = s.x + (s.w * (j + 1)) / blocks;
      if (j > 0) joints.push(`M${n2(u0)} ${-s.z}V${-z1}`);
      panels.push(rectD(u0 + 2.2, -(z1 - 2.2), u1 - 2.2, -(s.z + 2.2), 0.8));
    }
    out.push(M("marble", box(s, s.z, s.h - 1.4, { tone: "mid", inner: `<g transform="${faceY(front)}">${L(joints.join(""), { tone: "faint" })}${L(panels.join(""), { tone: "faint" })}</g>` }, 2, 0.5)));
    out.push(M("jade", box(k.insetPlan(s, -0.8), s.z + s.h - 1.4, 1.4, { tone: "mid" }, 2, 0.4)));
    if (i === 0) out.push(D([[s.x + 4, s.y + s.d, 4], [s.x + s.w - 4, s.y + s.d, 4]].map(at), { size: 0.45 }));
  }
  return out.join("");
}

// --- the spring jar and its troughs ---------------------------------------------------------------

function source() {
  const [x, y, z] = C.SOURCE;
  const F = FV(x, y, z);
  const profile = [[0, 6.2], [0.8, 7, 1], [4, 8.6, 1], [9, 8.4, 1], [13, 6.6, 1], [15, 5.2, 1], [16, 5.6]];
  const out = [shadow(x, y, 8, 0.3), M("ink", cyl(x, y, 7, z, 0.8, { tone: "mid" }, 40, 0.2)), M("marble", S(G.solidOf(profile, F, P, { smooth: true }), { tone: "mid" }))];
  out.push(M("marble", L(G.arcOf(F, 8.4, 8.5, P) + G.arcOf(F, 9.4, 8.45, P), { tone: "lo" })));
  out.push(M("jade", S(G.disc(16, 17.2, 6, F, P, { bevel: 0.4 }), { tone: "mid" }), S(G.sphereOf([x, y, z + 19], 1.8, P), { tone: "mid" })));
  // Three spouts: left and right to the troughs, front into the clock's vessel.
  out.push(M("jade", rod([x - 7.4, y, z + 6], [x - 11.4, y, z + 5.6], 1.1, { tone: "mid" }, 14), rod([x + 7.4, y, z + 6], [x + 11.4, y, z + 5.6], 1.1, { tone: "mid" }, 14), rod([x, y + 7.6, z + 9], [x, y + 11, z + 8.6], 0.9, { tone: "mid" }, 14)));
  return out.join("");
}
// A trough from a to b: a floor and two walls on one frame, its water, and trestles under it.
function trough(a, b, { trestles = [] } = {}) {
  const d = [b[0] - a[0], b[1] - a[1], b[2] - a[2]];
  const len = Math.hypot(...d);
  const dir = unit(d);
  const across = unit([-dir[1], dir[0], 0]);
  const up = unit([dir[1] * across[2] - dir[2] * across[1], dir[2] * across[0] - dir[0] * across[2], dir[0] * across[1] - dir[1] * across[0]]);
  const F = G.frameOf(a, dir, across, up[2] > 0 ? up : up.map((c) => -c));
  const out = [];
  for (const trestle of trestles) {
    const p = a.map((v, i) => v + d[i] * trestle.t);
    out.push(M("ink", box({ x: p[0] - 0.8, y: p[1] - 0.8, w: 1.6, d: 1.6, r: 0.2 }, trestle.z0, p[2] - 1 - trestle.z0, { tone: "mid" }, 1), box({ x: p[0] - 2.2, y: p[1] - 2.6 * Math.abs(across[1]) - 0.6, w: 4.4, d: 1.2 + 5.2 * Math.abs(across[1]), r: 0.3 }, p[2] - 1.6, 0.8, { tone: "mid" }, 1)));
  }
  out.push(M("marble", S(G.prismOf(F, [[-2.2, -0.6], [2.2, -0.6], [2.2, 0], [-2.2, 0]], 0, len, P), { tone: "mid" }), S(G.prismOf(F, [[-2.2, 0], [-1.6, 0], [-1.6, 1.6], [-2.2, 1.6]], 0, len, P), { tone: "mid" })));
  const w = (u) => k.pathOf([0, len].map((s) => at(G.pointOf(F, s, 0, 0).map((v, i) => v + across[i] * u + F.v[i] * 0.9))));
  out.push(`<path class="tw-water" d="${k.pathOf([...[0, len].map((s) => at(G.pointOf(F, s, 0, 0).map((v, i) => v + across[i] * -1.6 + F.v[i] * 0.9))), ...[len, 0].map((s) => at(G.pointOf(F, s, 0, 0).map((v, i) => v + across[i] * 1.6 + F.v[i] * 0.9)))], true)}"/>`);
  out.push(L(w(0), { tone: "lo", flow: true, className: "cl-flow", free: true }));
  out.push(M("marble", S(G.prismOf(F, [[1.6, 0], [2.2, 0], [2.2, 1.6], [1.6, 1.6]], 0, len, P), { tone: "mid" })));
  // The wall nearer the viewer is laid in lengths: a joint every nine units down its outer face.
  const view = G.viewOf(P);
  const near = Math.sign(F.u[0] * view[0] + F.u[1] * view[1] + F.u[2] * view[2]) || 1;
  const n = Math.max(1, Math.round(len / 9));
  const joints = [];
  for (let j = 1; j < n; j++) {
    const o = G.pointOf(F, (len * j) / n, 0, 0);
    const p = (v) => at(o.map((c, i) => c + F.u[i] * 2.2 * near + F.v[i] * v));
    joints.push(k.pathOf([p(-0.6), p(1.6)]));
  }
  out.push(L(joints.join(""), { tone: "faint" }));
  return out.join("");
}
function troughs() {
  const [a, b, c] = C.LEFT;
  const [r0, r1] = C.RIGHT;
  return [
    trough(a, b, { trestles: [{ t: 0.62, z0: 16 }, { t: 0.98, z0: 0 }] }),
    trough(b, c, { trestles: [{ t: 0.5, z0: 0 }, { t: 0.95, z0: 0 }] }),
    fall(c, [C.BASIN[0] + 3, C.BASIN[1] - 6, C.BASIN[3] - 1], 1.4),
    fall([C.SOURCE[0] - 11.4, C.SOURCE[1], C.SOURCE[2] + 5.4], [a[0], a[1], a[2] + 0.6], 1),
  ].join("");
}
function rightTrough(open) {
  const [r0, r1] = C.RIGHT;
  const x = C.GATE_X;
  const t = (x - r0[0]) / (r1[0] - r0[0]);
  const z = r0[2] + (r1[2] - r0[2]) * t;
  return [
    trough(r0, r1, { trestles: [{ t: 0.5, z0: 16 }, { t: 0.96, z0: 0 }] }),
    fall([C.SOURCE[0] + 11.4, C.SOURCE[1], C.SOURCE[2] + 5.4], [r0[0], r0[1], r0[2] + 0.6], 1),
    // The paid gate: a plate in its frame across the trough, lifted when the use is paid.
    M("ink", box({ x: x - 0.9, y: r0[1] - 3.4, w: 1.8, d: 1.2, r: 0.2 }, z - 1, 7, { tone: "mid" }, 1), box({ x: x - 0.9, y: r0[1] + 2.2, w: 1.8, d: 1.2, r: 0.2 }, z - 1, 7, { tone: "mid" }, 1), box({ x: x - 1.2, y: r0[1] - 3.6, w: 2.4, d: 7.2, r: 0.3 }, z + 6, 1.2, { tone: "mid" }, 1)),
    M("marble", box({ x: x - 0.5, y: r0[1] - 2, w: 1, d: 4, r: 0.1 }, z + 0.2 + open * 3.6, 3.4, { tone: "mid" }, 1)),
    open > 0.3 ? fall([r1[0] + 0.6, r1[1], r1[2] + 0.4], [r1[0] + 4, r1[1], C.WHEEL[2] + C.WHEEL[3] - 0.6], 1.6, Math.min(1, (open - 0.3) * 3)) : "",
  ].join("");
}

// --- the clock: its vessel, float arrow, ruler, the seal of the seat and the tablet of its duties ----

function vessel(elapsed) {
  const [x, y, z, r, h] = C.VESSEL;
  const F = FV(x, y, z);
  const wall = G.ringBand(0.8, h - 0.25, r - 0.55, r, F, P);
  const out = [shadow(x, y, r + 1, 0.3), M("jade", S(G.ringBand(0, 0.65, r - 0.65, r + 0.25, F, P), { tone: "mid" }))];
  out.push(`<path class="cl-glass-wall" fill-rule="evenodd" d="${wall.fill}"/>`, L(wall.outline, { tone: "mid" }));
  out.push(`<path class="iso-shade" data-shade="0" d="${k.ring(x, y, r - 0.8, z + h, P, 40)}"/><path class="tw-water" d="${k.ring(x, y, r - 0.8, z + h - 2.2, P, 40)}"/>`);
  out.push(M("jade", S(G.ringBand(h - 0.35, h, r - 0.55, r + 0.35, F, P), { tone: "mid" })));
  for (const [dx, dy, start] of [[-0.48, 0.8, 2.1], [-0.18, 0.96, 4.2]]) {
    out.push(k.fadeLineSvg([at([x + r * dx, y + r * dy, z + start]), at([x + r * dx, y + r * dy, z + h - 1.2])], { fade: [1.4, 1.4], tone: "hi", className: "cl-glass-shine" }));
  }
  // The float arrow: its tip rises one step per unit of the seat's time.
  const tip = z + h + 4 + elapsed * C.STEP_UP;
  out.push(M("jade", cyl(x, y, 2.6, z + h - 2, 1.2, { tone: "mid" }, 20), cyl(x, y, 0.55, z + h - 0.8, tip - z - h + 0.8, { tone: "hi", crease: "none", lit: true }, 10), S(G.solidOf([[tip, 0.9], [tip + 2.6, 0.15]], FV(x, y, 0), P), { tone: "hi", lit: true })));
  out.push(fall([x, C.SOURCE[1] + 11, C.SOURCE[2] + 8.4], [x, y - r + 1.6, z + h - 2], 0.8, 0.9));
  return out.join("");
}
// The arrow's ruler: a tick a unit, the term's mark in jade where the seat's deadline lies.
function ruler() {
  const [x, y] = C.RULER;
  const z0 = C.VESSEL[2] + C.VESSEL[4] + 4;
  const top = z0 + 8 * C.STEP_UP;
  const out = [M("ink", box({ x: x - 1.6, y: y - 1.6, w: 3.2, d: 3.2, r: 0.4 }, C.VESSEL[2], 1.4, { tone: "mid" }, 2)), M("marble", box({ x: x - 0.9, y: y - 0.6, w: 1.8, d: 1.2, r: 0.2 }, C.VESSEL[2] + 1.4, top - C.VESSEL[2] - 1.4, { tone: "mid" }, 1))];
  const face = y + 0.62;
  const minor = [], major = [];
  for (let i = 0; i <= 8; i++) (i % 5 ? minor : major).push(k.pathOf([at([x - 0.9, face, z0 + i * C.STEP_UP]), at([x - (i % 5 ? 0.2 : -0.4), face, z0 + i * C.STEP_UP])]));
  out.push(L(minor.join(""), { tone: "lo" }), L(major.join(""), { tone: "mid" }));
  out.push(M("jade", box({ x: x - 1.4, y: y - 1, w: 2.8, d: 2, r: 0.3 }, z0 + MD.TERM * C.STEP_UP - 0.6, 1.2, { tone: "mid" }, 1)));
  return out.join("");
}
// The seal of the seat on its pedestal: ink for 乙's first seat, marble for the next; the lamp shows a
// seat in force (jade) or a term run out (red).
function seal(state) {
  const [x, y] = C.SEAL;
  const z = C.STEPS[0].h;
  const out = [shadow(x, y, 4.4, 0.3), M("ink", box({ x: x - 4, y: y - 3.4, w: 8, d: 6.8, r: 0.8 }, z, 4, { tone: "mid" }, 2, 0.4))];
  out.push(M("jade", box({ x: x - 3.2, y: y - 2.6, w: 6.4, d: 5.2, r: 1.4 }, z + 4, 0.9, { tone: "mid" }, 3, 0.3)));
  out.push(M(state.seatAt[0] === 0 ? "ink" : "marble", box({ x: x - 2, y: y - 2, w: 4, d: 4, r: 0.4 }, z + 4.9, 3.2, { tone: "hi" }, 2, 0.3), S(G.sphereOf([x, y, z + 9.2], 1.2, P), { tone: "hi" })));
  const F = G.frameOf([x, y + 3.42, z + 2], Y3, X3, Z3);
  out.push(`<path class="${state.force ? "cl-lens cl-force" : "cl-lens cl-lapsed"}" d="${G.circleOf(F, 0.02, 1.2, P, 18)}"/>`);
  return out.join("");
}
// The tablet of the gate's duties: a line for every duty and every seat, none ever erased.
function tablet(lines) {
  const [x, y] = C.TABLET;
  const z = C.STEPS[0].h;
  const face = y + 1.02;
  const border = `<g transform="${faceY(face)}">${L(rectD(x - 3.3, -(z + 12.4), x + 3.3, -(z + 2.7), 0.5), { tone: "faint" })}</g>`;
  const out = [M("ink", box({ x: x - 5, y: y - 2.4, w: 10, d: 4.8, r: 0.6 }, z, 2, { tone: "mid" }, 2, 0.3), D([at([x - 4, y + 2.4, z + 1]), at([x + 4, y + 2.4, z + 1])], { size: 0.38 })),
    M("marble", box({ x: x - 4, y: y - 1, w: 8, d: 2, r: 0.4 }, z + 2, 11, { tone: "mid", inner: border }, 2, 0.3)),
    // Its cap: an ink coping over the slab and a jade boss at the centre.
    M("ink", box({ x: x - 4.6, y: y - 1.5, w: 9.2, d: 3, r: 0.5 }, z + 13, 0.9, { tone: "mid" }, 2, 0.25)), M("jade", S(G.sphereOf([x, y, z + 14.4], 0.8, P), { tone: "mid" }))];
  const rows = [];
  for (let i = 0; i < Math.min(lines, 7); i++) rows.push(k.pathOf([at([x - 2.8, face, z + 11.4 - i * 1.3]), at([x + (i % 2 ? 1.4 : 2.6), face, z + 11.4 - i * 1.3])]));
  out.push(L(rows.join(""), { tone: "lo", free: true }));
  return out.join("");
}

// --- the basin: anyone may draw; it has no box and reads no tally ----------------------------------

function basin(level, bowls) {
  const [x, y, r, h] = C.BASIN;
  const F = FV(x, y, 0);
  const profile = [[0, r - 3], [1.4, r - 2.4, 1], [3, r - 0.6, 1], [h - 1, r, 1], [h, r + 0.6]];
  const out = [shadow(x, y, r + 1, 0.35), M("ink", cyl(x, y, r - 2.4, 0, 0.8, { tone: "mid" }, 40, 0.2)), M("marble", S(G.solidOf(profile, F, P), { tone: "mid" }), S(G.ringBand(h - 0.2, h + 0.6, r - 1.4, r + 0.6, F, P), { tone: "mid" }), L(G.arcOf(F, h - 1.6, r - 0.15, P), { tone: "lo" }))];
  out.push(`<path class="iso-shade" data-shade="0" d="${k.ring(x, y, r - 1.4, h + 0.6, P, 48)}"/><path class="tw-water" d="${k.ring(x, y, r - 1.4, h - 0.8 + level * 0.4, P, 48)}"/>`);

  // Short, slightly uneven arcs spread from the stream's landing point; their ends fade instead of drawing a target.
  const zw = h - 0.8 + level * 0.4 + 0.02;
  for (const [r, from, to, phase] of [[1.8, -0.4, 1.9, 0], [3.1, 0.7, 3, 1], [4.5, 2.2, 4.5, 2]]) {
    const points = Array.from({ length: 31 }, (_, i) => {
      const a = from + ((to - from) * i) / 30;
      const rr = r * (1 + 0.035 * Math.sin(3 * a + phase));
      return at([x + 3 + rr * Math.cos(a), y - 6 + rr * Math.sin(a), zw]);
    });
    out.push(k.fadeLineSvg(points, { fade: [1.8, 1.8], tone: "faint", className: "cl-ripple" }));
  }
  // A ladle resting across the rim, its bowl in the water.
  out.push(M("ink", S(G.disc(-0.3, 0.3, 1.6, FV(x + r - 5.4, y - 1.5, zw), P), { tone: "mid" }), rod([x + r - 4, y - 2, h + 0.9], [x + r + 3, y - 6, h + 2.4], 0.4, { tone: "mid" }, 8)));
  for (const [i, [bx, by]] of C.BOWLS.entries()) {
    const B = FV(bx, by, 0);
    out.push(shadow(bx, by, 4, 0.3), M("marble", S(G.lathe([[0, 0], [0, 2], [0.8, 2.4, 1], [3.4, 4, 1], [4, 4.2]], B, P, { fill: "surface" }), { tone: "mid", inner: L(G.arcOf(B, 0.6, 2.3, P) + G.arcOf(B, 3.6, 4.07, P), { tone: "lo" }) })));
    if (bowls[i] > 0.05) out.push(`<path class="tw-water" d="${k.ring(bx, by, 2.8 + 1 * bowls[i], 1 + 2.6 * bowls[i], P, 28)}"/>`);
  }
  return out.join("");
}

// --- the mill: an overshot wheel, its shaft, a trip hammer and the trade's two lamps -----------------

// A rim on the axis F from s0 to s1: an open annulus, so what lies inside the wheel shows through.
function rimSvg(F, s0, s1, rIn, rOut) {
  const V = G.viewOf(P);
  const facing = F.a[0] * V[0] + F.a[1] * V[1] + F.a[2] * V[2];
  const [far, near] = facing > 0 ? [s0, s1] : [s1, s0];
  const ring = (s, r) => Array.from({ length: 56 }, (_, j) => at(G.pointOf(F, s, r, (j / 56) * Math.PI * 2)));
  const hole = k.pathOf(ring(near, rIn), true);
  const band = k.pathOf(G.hullOf([...ring(far, rOut), ...ring(near, rOut)]), true);
  const face = k.pathOf(ring(near, rOut), true) + hole;
  return `<g class="iso-solid"><path class="iso-fill" fill-rule="evenodd" d="${band + hole}"/><path class="iso-top" fill-rule="evenodd" d="${face}"/>${L(k.pathOf(ring(near, rOut), true), { tone: "faint" })}<path class="iso-line iso-edge" data-tone="mid" d="${band + hole}"/></g>`;
}
function wheel(turn) {
  const [cx, cy, cz, r, w] = C.WHEEL;
  const s0 = cy - w / 2;
  const F = G.frameOf([cx, s0, cz], Y3, X3, Z3);
  const V = G.viewOf(P);
  const TAU = Math.PI * 2;
  // A bearing post on its foot, carrying a pillow block and its cap.
  const post = (y) => M("ink", box({ x: cx - 4, y: y - 1.2, w: 8, d: 2.4, r: 0.4 }, 0, 1.2, { tone: "mid" }, 1), D([at([cx - 2.8, y + 1.2, 0.6]), at([cx + 2.8, y + 1.2, 0.6])], { size: 0.34 }), box({ x: cx - 1, y: y - 0.8, w: 2, d: 1.6, r: 0.3 }, 1.2, cz - 3.2, { tone: "mid" }, 1), box({ x: cx - 1.9, y: y - 1, w: 3.8, d: 2, r: 0.4 }, cz - 2, 1.6, { tone: "mid" }, 2, 0.2), box({ x: cx - 1.5, y: y - 1, w: 3, d: 2, r: 0.7 }, cz - 0.4, 1.5, { tone: "mid" }, 3, 0.2));
  const shaft = (y0, y1) => M("ink", S(G.disc(y0 - s0, y1 - s0, 1.1, F, P), { tone: "mid" }));
  const spokes = (s) => Array.from({ length: 6 }, (_, i) => { const t = turn + (i / 6) * TAU; return rod(G.pointOf(F, s, 2, t), G.pointOf(F, s, r - 1.4, t), 0.38, { tone: "mid" }, 8); }).join("");
  const back = s0 - 1.6, front = cy + w / 2 + 2.8;
  const out = [post(back), shaft(back - 1, s0), M("marble", rimSvg(F, 0, 0.8, r - 1.5, r), spokes(0.4))];
  // Fourteen buckets between the rims, far ones first.
  const buckets = [];
  for (let i = 0; i < 14; i++) {
    const a = turn + (i / 14) * TAU;
    const p = (s, rr, aa) => at(G.pointOf(F, s, rr, aa));
    const d = k.pathOf([p(0.8, r - 1.4, a), p(w - 0.8, r - 1.4, a), p(w - 0.8, r - 3.6, a + 0.16), p(0.8, r - 3.6, a + 0.16)], true);
    const c = G.pointOf(F, w / 2, r - 2.5, a + 0.08);
    buckets.push([c[0] * V[0] + c[1] * V[1] + c[2] * V[2], S({ fill: d, outline: d }, { tone: "mid", flat: true })]);
  }
  out.push(M("marble", ...buckets.sort((A, B) => A[0] - B[0]).map(([, svg]) => svg)));
  out.push(M("ink", S(G.disc(-0.6, w + 0.6, 2.2, F, P), { tone: "mid" })));
  out.push(M("marble", spokes(w - 0.4), rimSvg(F, w - 0.8, w, r - 1.5, r)));
  out.push(shaft(cy + w / 2, front + 1), M("ink", S(G.disc(w + 0.1, w + 1.4, 2.6, F, P), { tone: "mid", inner: L(G.circleOf(F, w + 1.4, 1.7, P, 24), { tone: "faint" }) }), D(G.dotsOf(F, w + 1.4, 2.1, 6, P, { all: true, phase: turn }), { size: 0.32 })));
  out.push(post(front), shaft(front + 1, C.PIVOT[1] + 2));
  const cam = G.frameOf([cx, C.PIVOT[1], cz], Y3, X3, Z3);
  out.push(M("ink", S(G.prismOf(cam, [[-1.2, -1.2], [1.2, -1.2], [3.6 * Math.cos(turn * 2), 3.6 * Math.sin(turn * 2)]], -1, 1, P), { tone: "mid" })));
  return out.join("");
}
function hammer(lift) {
  const [px, py, pz] = C.PIVOT;
  const head = 11, tail = 7;
  const mortar = [px + head, py];
  const mz = pz - 5;
  const out = [shadow(mortar[0], mortar[1], 5, 0.35), M("ink", cyl(mortar[0], mortar[1], 4.8, 0, 1.2, { tone: "mid" }, 28, 0.3)), M("marble", S(G.solidOf([[1.2, 3.4], [2, 3.6, 1], [mz - 4, 3.2, 1], [mz - 1.6, 4.2, 1], [mz, 4.6]], FV(mortar[0], mortar[1], 0), P), { tone: "mid" }), L(G.arcOf(FV(mortar[0], mortar[1], 0), 2.6, 3.56, P) + G.arcOf(FV(mortar[0], mortar[1], 0), mz - 0.4, 4.5, P), { tone: "lo" })), `<path class="iso-shade" data-shade="0" d="${k.ring(mortar[0], mortar[1], 3, mz, P, 24)}"/>`];
  for (const dy of [-3, 3]) out.push(M("ink", box({ x: px - 0.7, y: py + dy - 0.7, w: 1.4, d: 1.4, r: 0.2 }, 0, pz + 0.6, { tone: "mid" }, 1)));
  const a = 0.06 + lift * 0.4;
  const dir = [Math.cos(a), 0, Math.sin(a)];
  const F = G.frameOf([px, py, pz], dir, Y3, [-Math.sin(a), 0, Math.cos(a)]);
  out.push(M("marble", S(G.prismOf(F, [[-0.9, -0.8], [0.9, -0.8], [0.9, 0.8], [-0.9, 0.8]], -tail, head + 1, P), { tone: "mid" })));
  out.push(M("ink", S(G.disc(-3.6, 3.6, 0.7, G.frameOf([px, py, pz], Y3, X3, Z3), P), { tone: "mid" })));
  out.push(M("jade", S(G.disc(-5, 0.4, 1.6, G.frameOf(G.pointOf(F, head, 0, 0), Z3, X3, Y3), P), { tone: "mid" })));
  return out.join("");
}
function coinbox(coin) {
  const [x, y] = C.COINBOX;
  const z = C.STEPS[0].h;
  const out = [M("ink", box({ x: x - 4, y: y - 3, w: 8, d: 6, r: 0.6 }, z, 7, { tone: "mid" }, 2, 0.4), L(k.planOutline({ x: x - 2, y: y - 0.4, w: 4, d: 0.8, r: 0.3 }, z + 7, P, 2), { tone: "faint" }))];
  if (coin > 0) out.push(M("ink", S(G.disc(-0.4, 0.4, 2, G.frameOf([x, y, z + 7.2 + 9 * coin], Y3, X3, Z3), P), { tone: "hi" })));
  return out.join("");
}
// The mill's two legs: a lamp for the payment, a lamp for the grinding, a mark when both are done.
function millLamps(performed) {
  const [x, y] = C.LAMPS;
  const out = [shadow(x, y, 3, 0.3), M("marble", box({ x: x - 0.8, y: y - 0.8, w: 1.6, d: 1.6, r: 0.3 }, 0, 9, { tone: "mid" }, 1), box({ x: x - 7, y: y - 0.7, w: 14, d: 1.4, r: 0.4 }, 9, 6.4, { tone: "mid" }, 2, 0.3))];
  const lens = (u, on) => `<circle class="${on ? "cl-lens cl-paid" : "cl-lens"}" cx="${u}" cy="-12.2" r="1.5"/>`;
  out.push(`<g transform="${faceY(y + 0.72)}">${lens(x - 4, performed.includes("pay"))}${lens(x, performed.includes("grind"))}${L(`M${x + 2.6} -12.2l1.1 1.1l2 -2.4`, { tone: MD.cleared(performed) ? "hi" : "faint", free: true })}</g>`);
  return out.join("");
}

// --- the contribution's jar: sealed, filled once; its arrow shows what is left of Q ------------------

function jar(state) {
  const [x, y, r, h] = C.JAR;
  const F = FV(x, y, 0);
  const left = state.left ?? MD.remainingFor(state.account, state.origin);
  const profile = [[0, r - 1.6], [0.8, r - 0.6, 1], [h * 0.4, r, 1], [h * 0.8, r - 1, 1], [h - 0.8, r - 3, 1], [h, r - 3.2]];
  const out = [shadow(x, y, r + 1, 0.4), M("ink", cyl(x, y, r - 1.1, 0, 0.7, { tone: "mid" }, 36, 0.2)), M("marble", S(G.solidOf(profile, F, P, { smooth: true }), { tone: "mid" }))];
  out.push(M("marble", L(G.arcOf(F, h * 0.16, r - 0.2, P) + G.arcOf(F, h * 0.22, r - 0.1, P), { tone: "lo" })));
  // The lid, sealed with the contribution's mark: one dot per origin issued.
  out.push(M("jade", S(G.disc(h, h + 1.6, r - 2.6, F, P, { bevel: 0.4 }), { tone: "mid" }), box({ x: x + 2.2, y: y - 2, w: 4, d: 4, r: 0.4 }, h + 1.6, 2.4, { tone: "mid" }, 2, 0.3), D(Array.from({ length: state.origin }, (_, i) => at([x + 3.4 + i * 1, y, h + 4.02])), { size: 0.45, tone: "hi" })));
  // The float arrow through the lid: up Q steps when full, down one step a unit paid.
  const tip = h + 3 + left * C.Q_UP;
  out.push(M("jade", cyl(x - 2.4, y, 1.1, h + 1.6, 1.4, { tone: "mid" }, 16, 0.2)));
  out.push(M("jade", cyl(x - 2.4, y, 0.5, h + 3, tip - h - 3, { tone: "hi", crease: "none", lit: true }, 10), S(G.solidOf([[tip, 0.85], [tip + 2.2, 0.15]], FV(x - 2.4, y, 0), P), { tone: "hi", lit: true })));
  return out.join("");
}
// The Q ruler beside the jar: a tick per unit, Q at the top.
function qruler() {
  const [x, y] = C.QRULER;
  const h = C.JAR[3];
  const z0 = h + 3, top = z0 + MD.Q * C.Q_UP + 2;
  const out = [M("ink", box({ x: x - 1.6, y: y - 1.6, w: 3.2, d: 3.2, r: 0.4 }, 0, 1.4, { tone: "mid" }, 2)), M("marble", box({ x: x - 0.9, y: y - 0.6, w: 1.8, d: 1.2, r: 0.2 }, 1.4, top - 1.4, { tone: "mid" }, 1))];
  const face = y + 0.62;
  const ticks = [];
  for (let i = 0; i <= MD.Q; i++) ticks.push(k.pathOf([at([x - 0.9, face, z0 + i * C.Q_UP]), at([x + (i === MD.Q ? 0.9 : 0.1), face, z0 + i * C.Q_UP])]));
  out.push(L(ticks.join(""), { tone: "lo" }));
  out.push(k.faceTextSvg(`${faceY(face)} translate(${x - 1.4} ${-(z0 + MD.Q * C.Q_UP) + 1})`, "Q", { size: 2.8, tone: "mid", anchor: "end" }));
  return out.join("");
}
// The spigot on the jar's side turns toward the holder's cup; `pour` 0–1 runs one unit.
function spigot(toward, pour) {
  const [x, y, r] = C.JAR;
  const from = [x + r - 0.4, y + 1, 6];
  const i = Math.floor(toward), u = toward - i;
  const aCup = C.CUPS[i], bCup = C.CUPS[Math.min(C.CUPS.length - 1, i + 1)];
  const [cx, cy] = aCup.map((v, axis) => v + (bCup[axis] - v) * u);
  const a = Math.atan2(cy - from[1], cx - from[0]);
  const F = G.frameOf(from, [Math.cos(a), Math.sin(a), -0.05], Z3, [-Math.sin(a), Math.cos(a), 0]);
  const out = [M("jade", S(G.disc(0, 7, 0.9, F, P), { tone: "mid" }), S(G.disc(-0.6, 0.8, 1.7, F, P), { tone: "mid" }))];
  if (pour > 0.02) {
    const mouth = G.pointOf(F, 7, 0, 0);
    out.push(fall(mouth, [cx, cy, TRAY + 4.4], 0.9, Math.sin(pour * Math.PI)));
  }
  return out.join("");
}
// A holder's cup: jade for 甲, who made the contribution, marble for 丙; its water is what it received.
// The cups stand on an ink tray, TRAY high.
const TRAY = 0.8;
function cup(index, received) {
  const [x, y] = C.CUPS[index];
  const z = TRAY;
  const fill = Math.min(1, received / MD.Q);
  return M(index === 0 ? "jade" : "marble", S(G.lathe([[0, 0], [0, 2.8], [0.8, 3.2, 1], [4.6, 3.8, 1], [5.2, 4.1]], FV(x, y, z), P, { fill: "surface" }), { tone: "mid", inner: L(G.arcOf(FV(x, y, z), 0.9, 3.22, P), { tone: "lo" }) }))
    + (fill > 0 ? `<path class="tw-water" d="${k.ring(x, y, 3.1 + 0.6 * fill, z + 0.8 + 4 * fill, P, 28)}"/>` : "") + L(k.ring(x, y, 4.1, z + 5.2, P, 28), { tone: "mid" });
}
function tray() {
  const [[x0, y0], [, y1]] = C.CUPS;
  const plan = { x: x0 - 5.4, y: y0 - 5.4, w: 10.8, d: y1 - y0 + 10.8, r: 2 };
  return shadow(x0, (y0 + y1) / 2, 7, 0.3) + M("ink", box(plan, 0, TRAY, { tone: "mid" }, 4, 0.25), L(k.planOutline(k.insetPlan(plan, 1), TRAY, P, 4), { tone: "faint" }));
}
// The tally rack: a peg for each holder; the jade tally lies on its holder's peg.
function rack() {
  const [x, y] = C.RACK;
  const plan = { x: x - 2.4, y: y - 9, w: 4.8, d: 18, r: 0.6 };
  return shadow(x, y, 4, 0.3) + M("ink", box(plan, 0, 1.4, { tone: "mid" }, 2, 0.3), L(k.planOutline(k.insetPlan(plan, 0.8), 1.4, P, 2), { tone: "faint" }), D([at([x, y - 1.2, 1.4]), at([x, y + 1.2, 1.4])], { size: 0.36 }),
    ...[-6.5, 6.5].map((dy) => cyl(x, y + dy, 1.1, 1.4, 0.5, { tone: "mid" }, 16, 0.15) + cyl(x, y + dy, 0.6, 1.9, 4.5, { tone: "mid", crease: "none" }, 10) + S(G.sphereOf([x, y + dy, 6.6], 0.75, P), { tone: "mid" })));
}
function tally(where) {
  const [x, y] = C.RACK;
  const py = y + (-6.5 + 13 * where.t);
  const z = 1.9 + Math.sin(where.t * Math.PI) * 5 + where.lift;
  const F = G.frameOf([x - 3.4 + where.dx, py + where.dy, z], X3, Y3, Z3);
  return M("jade", S(G.prismOf(F, [[-0.9, -0.4], [0.9, -0.4], [0.9, 0.4], [-0.9, 0.4]], -4.6, 4.6, P), { tone: "hi", lit: true }));
}

// --- composition: back to front -----------------------------------------------------------------------

function composition(state) {
  return [
    WATER_DEFS,
    base(),
    `<g data-part="counter">${counter(state)}</g>`,
    `<g data-part="wheel">${wheel(state.turn)}</g>`,
    stand(),
    source(),
    `<g data-part="right">${rightTrough(state.open)}</g>`,
    `<g data-part="coinbox">${coinbox(state.coin)}</g>`,
    `<g data-part="tablet">${tablet(state.log.length)}</g>`,
    `<g data-part="vessel">${vessel(state.elapsed)}</g>`,
    ruler(),
    `<g data-part="seal">${seal(state)}</g>`,
    troughs(),
    `<g data-part="hammer">${hammer(state.lift)}</g>`,
    `<g data-part="lamps">${millLamps(state.legs)}</g>`,
    `<g data-part="basin">${basin(state.level, state.bowls)}</g>`,
    qruler(),
    `<g data-part="jar">${jar(state)}</g>`,
    `<g data-part="spigot">${spigot(state.tally.t, state.pour)}</g>`,
    tray(),
    `<g data-part="cup-0">${cup(0, state.shownReceived?.[0] ?? state.received[0])}</g>`,
    rack(),
    `<g data-part="cup-1">${cup(1, state.shownReceived?.[1] ?? state.received[1])}</g>`,
    `<g data-part="tally">${tally(state.tally)}</g>`,
    `<g class="cl-hits">${hitAreas()}</g>`,
  ].join("");
}
function hitAreas() {
  const zone = (name, points) => `<path data-hit="${name}" d="${k.pathOf(G.hullOf(points.map(at)), true)}"/>`;
  const boxPts = (x0, y0, x1, y1, z0, z1) => k.boxCorners({ x: x0, y: y0, w: x1 - x0, d: y1 - y0 }, z0, z1);
  const [bx, by, br, bh] = C.BASIN;
  const [jx, jy, jr, jh] = C.JAR;
  const [vx, vy, vz, vr, vh] = C.VESSEL;
  return [
    zone("basin", boxPts(bx - br - 6, by - br, bx + br + 4, C.BOWLS[1][1] + 5, 0, bh + 3)),
    zone("jar", boxPts(jx - jr, jy - jr, jx + jr + 6, jy + jr, 0, jh + 6)),
    zone("tally", boxPts(C.CUPS[0][0] - 5, C.CUPS[0][1] - 5, C.RACK[0] + 4, C.CUPS[1][1] + 5, 0, 10)),
    zone("mill", boxPts(C.GATE_X - 4, -46, C.LAMPS[0] + 8, C.PIVOT[1] + 5, 0, C.WHEEL[2] + C.WHEEL[3] + 2)),
    zone("keeper", boxPts(vx - vr - 1, vy - vr - 1, vx + vr + 1, vy + vr + 1, vz, vz + vh + 2)),
    zone("keeper", boxPts(C.RULER[0] - 1.8, C.RULER[1] - 1.4, C.RULER[0] + 1.8, C.RULER[1] + 1.4, vz, vz + vh + 8 * C.STEP_UP + 3)),
    zone("seal", boxPts(C.SEAL[0] - 5, C.SEAL[1] - 4, C.SEAL[0] + 5, C.SEAL[1] + 4, C.STEPS[0].h, C.STEPS[0].h + 11)),
  ].join("");
}

// The first frame: 甲's contribution has paid 甲 two of its six units; the mill has just cleared; the
// first seat is in force with two units of its term run.
const REST = {
  origin: 1, account: MD.pay(MD.issue({ slots: [] }, 1, "甲", MD.Q).account, 1, 2).account,
  holder: 0, received: [2, 0], pour: 0, tally: { t: 0, dx: 0, dy: 0, lift: 0 },
  legs: ["pay", "grind"], open: 0, coin: 0, turn: 0.4, lift: 0,
  elapsed: 2, force: true, seatAt: [0, 1], log: [1, 1, 1], level: 1, bowls: [0, 0],
};

const svg = k.figureSvg({
  width: WIDTH,
  height: HEIGHT,
  className: "cl-svg",
  label: "A stone water clock. A spring jar on a stepped stand pours three ways: down a trough to a basin anyone may draw from, with no box and no token; into the clock's vessel, whose float arrow rises beside a ruler marked with the keeper's term; and through a gate that opens only when the use is paid, onto a waterwheel that works a trip hammer, with two lamps for the payment and the grinding. In front stands a jar sealed with one contribution's mark: its float arrow shows what is left of the contribution's quantity Q, and its spigot turns to the cup of whoever holds the jade tally. What the cups have received plus what is left is always Q. When the time arrow passes the term's mark, the seal's lamp turns red; the tablet keeps every line for the next seat.",
  body: composition(REST),
});

const CSS = `
.cl-svg{--cl-fault:var(--cinnabar,#c8372d);--cl-force:#9fc7a9;--cl-water-light:#edf5ee;--cl-water:#b8d2c8;--cl-water-edge:#7fa89b;--cl-water-ink:#5f8e82}
.iso[data-theme="dark"] .cl-svg{--cl-water-light:#47685a;--cl-water:#29483b;--cl-water-edge:#1c342a;--cl-water-ink:#83aa98}
.cl-svg .tw-water{fill:var(--cl-water);fill:url(#cl-water-fill);fill-opacity:.86;stroke:var(--cl-water-edge);stroke-width:.45}
.cl-svg .cl-flow{opacity:.55;stroke:var(--cl-water-ink);stroke-width:.55}
.cl-svg .cl-fall{fill:var(--cl-water);fill:url(#cl-stream-fill);stroke:none}
.cl-svg .cl-stream-shine{fill:none;stroke:var(--cl-water-light);stroke-width:.45;stroke-linecap:round}
.cl-svg .cl-ripple{stroke:var(--cl-water-ink);stroke-width:.45}
.cl-svg .cl-glass-wall{fill:#d9e8e2;fill-opacity:.22;stroke:none}
.iso[data-theme="dark"] .cl-svg .cl-glass-wall{fill:#2a453a;fill-opacity:.3}
.cl-svg .cl-glass-shine{fill:none;stroke:#fff;stroke-width:.65}
.cl-svg .cl-lens{fill:#2a2f30;stroke:none;transition:fill .35s var(--anatomy-ease)}
.cl-svg .cl-lens.cl-force,.cl-svg .cl-lens.cl-paid{fill:var(--cl-force)}
.cl-svg .cl-lens.cl-lapsed{fill:var(--cl-fault)}
.cl-svg .cl-hits path{fill:transparent;cursor:pointer}
.cl-svg .cl-window{fill:#151819;stroke:none}
.cl-svg .cl-digit{fill:#eef2ef;font-family:var(--anatomy-mono);font-variant-numeric:tabular-nums}
.cl-svg .cl-digit.cl-q{fill:var(--cl-force)}
.iso-stage{outline:none;touch-action:pan-y}
.iso-stage:focus-visible{box-shadow:0 0 0 1px var(--anatomy-mid)}
${SWING_CSS}
@media (max-width:560px){.iso-plate:has(.cl-svg){overflow:hidden}.cl-svg.iso-svg{width:114%;max-width:none;margin:0 -7%}}
@media (prefers-reduced-motion:reduce){.cl-svg .cl-flow{animation:none}}
`;

const strip = (file) => readFileSync(join(HERE, file), "utf8").replace(/^export /gm, "");
const kitSource = strip("../kit/iso-kit.mjs");
const latheSource = `const LATHE = (() => {\n${strip("../kit/lathe.mjs").replace(/^import .*$/gm, "")}\nreturn { ${Object.keys(G).join(", ")} };\n})();`;
const modelSource = `const MD = (() => {\n${strip("model.mjs")}\nreturn { ${Object.keys(MD).join(", ")} };\n})();`;

const live = `
const P0 = ${JSON.stringify(P0)};
let P = P0;
${shipped({ C, COUNTER, TRAY, FRAME, X3, Y3, Z3, WATER_DEFS })}
const k = { ${Object.keys(k).join(", ")} };
const G = LATHE;
${shipped({ at, S, L, D, M, n2, faceY, rectD, box, cyl, FV, unit, rod, fall, shadow })}
${shipped({ rimSvg, base, counterFace, counter, tray, stand, source, trough, troughs, rightTrough, vessel, ruler, seal, tablet, basin, wheel, hammer, coinbox, millLamps, jar, qruler, spigot, cup, rack, tally, composition, hitAreas })}
${swingSource}
${liveScript()}
`;

// The page: a tour of the four claims; each part also answers a click.
function liveScript() {
  return String.raw`
const root = document.querySelector('[data-figure="clepsydra"]');
const stage = root.querySelector(".iso-stage");
const svg = stage.querySelector("svg");
const readout = root.querySelector("[data-readout]");
const still = matchMedia("(prefers-reduced-motion: reduce)");
const T = root.dataset;
const HOLDER = ["甲", "丙"], KEEPER = ["乙", "戊"];
const st = {
  origin: 1, account: MD.pay(MD.issue({ slots: [] }, 1, "甲", MD.Q).account, 1, 2).account,
  holder: 0, received: [2, 0], shownReceived: [2, 0], left: 4, pour: 0, tally: { t: 0, dx: 0, dy: 0, lift: 0 },
  legs: ["pay", "grind"], open: 0, coin: 0, turn: 0.4, lift: 0,
  elapsed: 2, force: true, seatAt: [0, 1], log: [1, 1, 1], level: 1, bowls: [0, 0],
};
// The clock: one tick per unit of time; the seat's own deadline decides its jurisdiction.
let clock = 2, seat = MD.seatOf("乙", 0), keeperIndex = 0;
let steps = [], step = null, stepTime = 0, touring = !still.matches, idle = 0, visible = false, frame = 0, last = 0, tourAt = 0;
const part = (name) => svg.querySelector('[data-part="' + name + '"]');
const inForce = () => MD.jurisdiction(seat, KEEPER[keeperIndex], clock);
const smooth = (value) => { const t = Math.max(0, Math.min(1, value)); return t * t * (3 - 2 * t); };
function syncAccount() {
  st.left = MD.remainingFor(st.account, st.origin);
  st.shownReceived = [...st.received];
}
function say() {
  const got = MD.receivedFor(st.account, st.origin), left = MD.remainingFor(st.account, st.origin);
  const elapsed = Math.max(0, clock - seat.granted);
  const reading = Number.isInteger(elapsed) ? elapsed : elapsed.toFixed(1);
  const term = inForce() ? T.term + " " + reading + "/" + MD.TERM : T.lapsed;
  const text = T.received + " " + got + " + " + T.left + " " + left + " = Q " + MD.Q + " · " + term;
  if (readout.textContent !== text) readout.textContent = text;
  stage.setAttribute("aria-valuetext", text);
}
let shown = {};
function paint(force = false) {
  const key = (v) => JSON.stringify(v);
  const want = {
    wheel: key([n2(st.turn)]), right: key([n2(st.open)]), coinbox: key([n2(st.coin)]), tablet: key([st.log.length]),
    vessel: key([n2(st.elapsed)]), seal: key([st.force, st.seatAt]), hammer: key([n2(st.lift)]), lamps: key(st.legs),
    basin: key([n2(st.level), st.bowls.map(n2)]), jar: key([n2(st.left), st.origin]), spigot: key([n2(st.tally.t), n2(st.pour)]),
    counter: key([MD.receivedFor(st.account, st.origin), MD.remainingFor(st.account, st.origin)]), "cup-0": key([n2(st.shownReceived[0])]), "cup-1": key([n2(st.shownReceived[1])]), tally: key([n2(st.tally.t), n2(st.tally.dx), n2(st.tally.dy), n2(st.tally.lift)]),
  };
  const draw = {
    wheel: () => wheel(st.turn), right: () => rightTrough(st.open), coinbox: () => coinbox(st.coin), tablet: () => tablet(st.log.length),
    vessel: () => vessel(st.elapsed), seal: () => seal(st), hammer: () => hammer(st.lift), lamps: () => millLamps(st.legs),
    basin: () => basin(st.level, st.bowls), jar: () => jar(st), spigot: () => spigot(st.tally.t, st.pour),
    counter: () => counter(st), "cup-0": () => cup(0, st.shownReceived[0]), "cup-1": () => cup(1, st.shownReceived[1]), tally: () => tally(st.tally),
  };
  for (const name of Object.keys(want)) if (force || want[name] !== shown[name]) part(name).innerHTML = draw[name]();
  shown = want;
  say();
}
const TOUR = [
  { kind: "draw", bowl: 0 }, { kind: "wait", t: 0.5 },
  { kind: "pay" }, { kind: "wait", t: 0.5 },
  { kind: "mill" }, { kind: "wait", t: 0.5 },
  { kind: "transfer" }, { kind: "wait", t: 0.5 },
  { kind: "pay" }, { kind: "wait", t: 0.4 },
  { kind: "try" }, { kind: "wait", t: 0.6 },
  { kind: "draw", bowl: 1 }, { kind: "wait", t: 0.4 },
  { kind: "time" }, { kind: "wait", t: 1.2 },
  { kind: "renew" }, { kind: "wait", t: 0.8 },
  { kind: "pay" }, { kind: "wait", t: 0.4 }, { kind: "pay" }, { kind: "wait", t: 0.5 },
  { kind: "mill" }, { kind: "wait", t: 0.5 },
  { kind: "transfer" }, { kind: "wait", t: 0.5 },
  { kind: "contribute" }, { kind: "wait", t: 1.2 },
];
const DURATION = { draw: 1.6, pay: 1.3, mill: 2.8, transfer: 1.1, try: 1.6, time: 2.4, renew: 1.6, contribute: 1.8 };
function begin(next) {
  step = next;
  stepTime = 0;
  if (step.kind === "pay") {
    step.result = MD.pay(st.account, st.origin, 1);
    step.paid = step.result.paid;
    step.holder = st.holder;
    step.fromLeft = st.left;
    step.fromReceived = [...st.shownReceived];
  } else if (step.kind === "transfer") {
    step.from = st.holder;
    step.to = 1 - st.holder;
  } else if (step.kind === "mill") st.legs = [];
  else if (step.kind === "time") step.from = clock;
  else if (step.kind === "renew") {
    // The vessel empties before the next grant replaces the seal and starts its own deadline.
    step.keeper = 1 - keeperIndex;
    step.result = MD.renew(st.log, KEEPER[step.keeper], clock);
    step.from = st.elapsed;
  } else if (step.kind === "contribute") {
    // A new origin arrives only when the new seal lands; the old one is not issued again.
    step.origin = st.origin + 1;
    step.account = MD.issue({ slots: [] }, step.origin, HOLDER[st.holder], MD.Q).account;
  }
}
function complete(next) {
  if (next.kind === "pay") {
    st.account = next.result.account;
    st.received[next.holder] += next.paid;
  } else if (next.kind === "transfer") {
    st.holder = next.to;
    st.account = MD.transfer(st.account, st.origin, HOLDER[st.holder]);
  } else if (next.kind === "renew") {
    keeperIndex = next.keeper;
    seat = next.result.seat;
    st.log = [...st.log, 1];
    st.seatAt = keeperIndex === 0 ? [0, 1] : [1, 0];
    st.elapsed = 0;
  } else if (next.kind === "contribute") {
    st.origin = next.origin;
    st.account = next.account;
    st.received = [0, 0];
  }
  st.force = inForce();
  syncAccount();
}
function advance(dt) {
  if (!step) {
    if (steps.length) begin(steps.shift());
    else if (touring) { begin({ ...TOUR[tourAt] }); tourAt = (tourAt + 1) % TOUR.length; }
    else return false;
  }
  stepTime += dt;
  const d = DURATION[step.kind] ?? step.t ?? 0;
  const t = d ? Math.min(1, stepTime / d) : 1;
  const bell = Math.sin(t * Math.PI);
  if (step.kind === "draw") { st.bowls[step.bowl] = Math.max(st.bowls[step.bowl], smooth(t)); st.level = 1 - 0.3 * bell; }
  else if (step.kind === "pay") {
    st.pour = step.paid ? t : 0;
    const delivered = smooth((t - 0.42) / 0.46);
    st.left = step.fromLeft - step.paid * delivered;
    st.shownReceived = [...step.fromReceived];
    st.shownReceived[step.holder] += step.paid * delivered;
  } else if (step.kind === "mill") {
    // The payment leg, then the grinding leg: the gate lifts for one run and the hammer falls.
    st.coin = t < 0.25 ? 1 - smooth(t / 0.25) : 0;
    if (t >= 0.25 && !st.legs.includes("pay")) st.legs = ["pay"];
    st.open = t < 0.3 ? 0 : t < 0.85 ? smooth((t - 0.3) / 0.2) : 1 - smooth((t - 0.85) / 0.15);
    st.turn += dt * 3.2 * st.open;
    st.lift = Math.abs(Math.sin(st.turn * 2)) * st.open;
    if (t >= 0.85 && !st.legs.includes("grind")) st.legs = ["pay", "grind"];
  } else if (step.kind === "transfer") {
    const u = smooth(t);
    st.tally = { t: step.from + (step.to - step.from) * u, dx: 0, dy: 0, lift: 0 };
  } else if (step.kind === "try") {
    // The tally is carried to the seal's lock and does not open it or change the seat's lamp.
    const reach = t < 0.5 ? smooth(t * 2) : smooth(2 - t * 2);
    const [rx, ry] = C.RACK, py = ry + (-6.5 + 13 * st.holder);
    st.tally = { t: st.holder, dx: (C.SEAL[0] - rx) * reach, dy: (C.SEAL[1] + 4 - py) * reach, lift: 14 * Math.sin(reach * Math.PI) + (C.STEPS[0].h + 4) * reach };
  } else if (step.kind === "time") {
    // Time runs past the term: the arrow rises past the mark, and no later step restores the seat.
    const target = Math.max(step.from, seat.deadline + 1);
    clock = step.from + (target - step.from) * smooth(t);
    st.elapsed = Math.min(MD.TERM + 1.6, clock - seat.granted);
    st.force = inForce();
  } else if (step.kind === "renew") st.elapsed = step.from * (1 - smooth(t));
  else if (step.kind === "contribute") st.tally = { t: st.holder, dx: 0, dy: 0, lift: 3 * bell };
  if (t >= 1) {
    if (step.kind === "draw") st.level = 1;
    if (step.kind === "pay") st.pour = 0;
    if (step.kind === "mill") { st.open = 0; st.lift = 0; }
    if (step.kind === "try") st.tally = { t: st.holder, dx: 0, dy: 0, lift: 0 };
    complete(step);
    step = null;
  }
  return true;
}
function tick(time) {
  const dt = last ? Math.min((time - last) / 1000, 1 / 30) : 1 / 60;
  last = time;
  const busy = advance(dt);
  paint();
  frame = visible && (busy || touring) ? requestAnimationFrame(tick) : 0;
}
const run = () => { if (!frame && visible) { last = 0; frame = requestAnimationFrame(tick); } };
const hold = () => { touring = false; clearTimeout(idle); idle = setTimeout(() => { touring = !still.matches; run(); }, 9000); };
function now(list) {
  if (!still.matches) { steps.push(...list); run(); return; }
  for (const next of list) { begin(next); stepTime = 1e3; advance(0); }
  paint();
}
const ACTION = { basin: () => [{ kind: "draw", bowl: 1 }], jar: () => [{ kind: "pay" }], tally: () => [{ kind: "transfer" }], mill: () => [{ kind: "mill" }], keeper: () => (inForce() ? [{ kind: "time" }] : [{ kind: "renew" }]), seal: () => [{ kind: "try" }] };
stage.addEventListener("click", (event) => {
  const hit = event.target.closest("[data-hit]");
  if (!hit) return;
  hold();
  steps = [];
  if (step?.kind === "wait") step = null;
  now(ACTION[hit.dataset.hit]());
});
const KEYS = ["basin", "jar", "tally", "mill", "keeper", "seal"];
let keyAt = 0;
stage.addEventListener("keydown", (event) => {
  if (event.key === "ArrowRight") keyAt = (keyAt + 1) % KEYS.length;
  else if (event.key === "ArrowLeft") keyAt = (keyAt + KEYS.length - 1) % KEYS.length;
  else if (event.key !== " " && event.key !== "Enter") return;
  event.preventDefault();
  hold();
  steps = [];
  if (step?.kind === "wait") step = null;
  now(ACTION[KEYS[keyAt]]());
});
new IntersectionObserver((entries) => { visible = entries[entries.length - 1].isIntersecting; if (visible) run(); }, { rootMargin: "120px 0px" }).observe(stage);
if (still.matches) touring = false;
paint(true);
mountSwing(stage, { onHold: hold, onSwing: (angle) => { P = swingOf(iso, P0, FRAME, angle); svg.innerHTML = composition(st); shown = {}; paint(true); } });
`;
}

const COPY = {
  en: {
    title: "Contribution settles, control renews",
    hint: "Click a part · ← → choose · drag to look round",
    keys: ["Basin: participation, with no token", "Arrow and tally: one contribution's claim, received ≤ Q", "Lamp: red when the keeper's term has run out"],
    refs: ["Result 4", "Result 5", "Result 7"],
    caption: [
      "Four kinds of claim, each with its own water. Anyone who arrives draws from the basin: participation comes before contribution, and the basin has no box to read a token.",
      "甲's contribution filled the sealed jar once with Q units. Its jade tally can pass from hand to hand and the spigot turns with it, but a transfer pays nothing and issues nothing: what the cups have received plus what the arrow shows is left is always Q, and a new contribution comes with a new seal.",
      "The mill is a scarce use: its gate lifts only when the use is paid, and the trade clears only when both legs are done, the payment and the grinding.",
      "The clock's own arrow measures the keeper's term. When it passes the term's mark the seal's lamp turns red, with the same seal still on its pedestal; the tablet keeps its lines, and the next seat is a new grant measured afresh. The tally opens no lock: a contribution does not become authority.",
    ],
    aria: "Water clock: click the basin to draw, the jar to pay one unit, the tally to pass it on, the mill to use it, the clock to let the term run or grant a new seat, the seal to try the tally on it",
    received: "received", left: "left", term: "term", lapsed: "term ended",
  },
  zh: {
    title: "贡献可以结清，控制必须续约",
    hint: "点击各处 · ← → 选择 · 拖动侧看",
    keys: ["水池：基础参与，不看筹子", "浮箭与玉筹：一份贡献的请求，累计受领 ≤ Q", "灯：守闸人任期已满时变红"],
    refs: ["结果 4", "结果 5", "结果 7"],
    caption: [
      "四种资格，各取各的水。来到这里的人都能从公共水池取水：参与先于贡献，水池上也没有读筹子的匣子。",
      "甲的贡献一次注满了封印的量壶，共 Q 个单位。它的玉筹可以转手，壶嘴随之转向；转让不付出一滴，也不再发行：各杯累计受领的，加上浮箭所示的剩余，始终等于 Q。新的贡献带着新的封印到来。",
      "水碓是稀缺的使用：用水当次付费，闸板才起；付费与碾米两条腿都实际履行，这笔交易才算清。",
      "漏刻自己的时间箭量着守闸人的任期。箭过任期刻度，即使原来那方印仍在印座上，灯也会变红；碑上的记录留下，下一任是一次新的授权，重新计时。玉筹开不了印：贡献不会变成权力。",
    ],
    aria: "漏刻水台：点击水池取水，点击量壶付一单位，点击玉筹转手，点击水碓用水，点击漏刻让任期走完或授予新任，点击印座用玉筹试印",
    received: "已受领", left: "余", term: "任期", lapsed: "任期已满",
  },
};
const bodyOf = (lang) => {
  const copy = COPY[lang];
  const data = ["received", "left", "term", "lapsed"].map((key) => `data-${key}="${copy[key]}"`).join(" ");
  return `<div data-figure="clepsydra" ${data}>${k.plateHtml({
    fig: "Fig 4.3",
    title: copy.title,
    hint: copy.hint,
    readout: `${copy.received} 2 + ${copy.left} 4 = Q 6 · ${copy.term} 2/5`,
    keys: [
      { mark: "raised", label: copy.keys[0] },
      { mark: "lit", label: copy.keys[1] },
      { mark: "red", label: copy.keys[2] },
    ],
    caption: copy.caption,
    refs: copy.refs,
    body: `<div class="iso-stage" tabindex="0" role="application" aria-label="${copy.aria}">${svg}</div>`,
  })}</div>`;
};

const script = `{\n${kitSource}\n${latheSource}\n${modelSource}\n${live}\n}`.replace(/<\/(script)/gi, "<\\/$1");
if (fragment) {
  const outDir = join(HERE, "../../src/generated");
  mkdirSync(outDir, { recursive: true });
  writeFileSync(join(outDir, "clepsydra.json"), JSON.stringify({ html: { zh: bodyOf("zh"), en: bodyOf("en") }, css: CSS, script }));
  console.log("wrote src/generated/clepsydra.json");
} else {
  mkdirSync(join(HERE, "out"), { recursive: true });
  const name = theme === "light" ? "clepsydra-light.html" : "clepsydra.html";
  writeFileSync(join(HERE, "out", name), k.pageHtml({ title: "Contribution settles, control renews", theme, body: `<style>${CSS}</style>${bodyOf(process.argv.includes("--zh") ? "zh" : "en")}`, script: `{\n${kitSource}\n${latheSource}\n${modelSource}\n${live}\n}`, width: 760 }));
  console.log("wrote out/" + name);
}
