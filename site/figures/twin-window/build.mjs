// Fig: twin observation machines and the shortest window (Theorems 3.3–3.4, O8).
// Two identical machines carry the states A = ι(e_2) = (e_2, 1, 3) and B = A + v_*, where v_* is the
// hidden state of §3.3. Each step shifts the cart line one cell right and lets the clock weight advance
// its ratchet by m teeth (A(h, m, c) = (Sh, m, c + m)). Two probes over cells 1 and 3 push their
// plungers out by r_j = h + m + 2(j + 1)c, and the recorder keeps every frame. For a = 2 frames the
// twins read the same; the third frame tells them apart.
//   bun build.mjs [--light]   → out/twin-window[-light].html (standalone, for checks)
//   bun build.mjs --fragment  → ../../src/generated/twin-window.json (for the site)
import { mkdirSync, readFileSync, writeFileSync } from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";
import * as k from "../kit/iso-kit.mjs";
import * as G from "../kit/lathe.mjs";
import { A_SCALE, CELLS, FRAMES, PROBES, TWIN, SIGNAL, cellAt, clockAt, responseOf } from "./model.mjs";
import { paperFigureCss, paperFigureSource, paperPlate } from "../paper-figure.mjs";
import { shipped, swingSource } from "../swing.mjs";

const HERE = dirname(fileURLToPath(import.meta.url));
const theme = process.argv.includes("--light") ? "light" : "dark";
const fragment = process.argv.includes("--fragment");

const WIDTH = 640;
const HEIGHT = 410;

// World: x along the cart lines (the shift runs toward +x), y toward the viewer, z up; the deck is z = 0.
// Machine A runs in front (y > 0), machine B behind it; the recorder stands at the right.
const C = {
  BASE: { x: -114, y: -38, w: 214, d: 76, r: 6 },
  BASE_H: 8,
  FOOT_H: 4,
  LANES: [19, -19], // y of A, B
  CELL: 15,
  X0: -54, // x of cell 0
  SLOTS: [-1, 6], // the cart slots drawn
  RAIL: { x0: -80, x1: 46, half: 4.6, w: 1.8, z: 5, h: 1.6 },
  LEGS: [-77, -16, 43],
  CART: { hx: 6, hy: 6.4, z: 8.2, h: 2.2, wheel: 1.2 },
  BEAD: { r: 1.6, pitch: 3.25 },
  PROBE: { z: 27, half: 3.2, park: 25.2, beam: { z: 33, h: 2.4 } },
  PLUNGER: { r: 1.3, unit: 0.66 },
  STAND: { x: -95, half: 5.5, h: 41, axle: 27.5, wheel: 9.4, teeth: 12, face: 7.6, drum: 2.4, drop: 1.6 },
  WEIGHT: { r: 2.9, h: 2.4, top: 14.5 },
  SHAFT: { x: -108, z: 5.5, r: 1.1, y0: -30, y1: 33 },
  REC: { x: 54, y: -14, w: 44, d: 44, h: 3.4, rows: [63, 77, 91], pins: [17.6, 12.6, 0.4, -4.6], unit: 0.9 },
};
const XC = (k) => C.X0 + C.CELL * k;

const FIT = [...k.boxCorners(C.BASE, -C.BASE_H - C.FOOT_H, 0), [C.STAND.x, C.LANES[1], C.STAND.h + 3], [XC(3), C.LANES[1], 58], [XC(1), C.LANES[0], 50], [C.REC.rows[2], -11, 28]];
const VIEW = { pad: 20, azimuth: 60, elevation: 40 };
const P0 = k.fitProjection(FIT, WIDTH, HEIGHT, VIEW);
const FRAME = { points: FIT, width: WIDTH, height: HEIGHT, pad: VIEW.pad };
let P = P0;

const STATES = [SIGNAL, TWIN];

// --- shared with the page --------------------------------------------------------------------

const at = (point) => k.iso(point, P);
const S = (paths, style) => k.solidSvg(paths, style);
const L = (d, style) => k.lineSvg(d, style);
const D = (points, style) => k.dotsSvg(points, style);
const M = (material, ...svg) => `<g data-mat="${material}">${svg.join("")}</g>`;
const depthAt = (x, y, z = 0) => k.depthOf([x, y, z], P);
const byDepth = (items, key) => [...items].sort((a, b) => depthAt(...key(a)) - depthAt(...key(b)));
const Y3 = [0, 1, 0];
const stackTop = (h) => C.CART.z + C.CART.h + (h ? (Math.abs(h) - 0.5) * C.BEAD.pitch + C.BEAD.r : 0);

const placeSvg = (id, x, y, z = 0) => {
  const [dx, dy] = at([x, y, z]);
  return `<use href="#${id}" x="${dx.toFixed(2)}" y="${dy.toFixed(2)}"/>`;
};

// All sixteen carts share one set of projected paths at each viewing angle.
function cartBody(camera) {
  const c = C.CART, top = c.z + c.h;
  const wheel = (x, y) => {
    const [dx, dy] = k.iso([x, y, C.RAIL.z + C.RAIL.h + c.wheel], camera);
    return M("ink", `<use href="#tw-wheel" x="${dx.toFixed(2)}" y="${dy.toFixed(2)}"/>`);
  };
  const half = C.RAIL.half;
  const deck = { x: -c.hx, y: -c.hy, w: 2 * c.hx, d: 2 * c.hy, r: 1 };
  return wheel(-3.2, -half) + wheel(3.2, -half)
    + S(k.slabOf(deck, c.z, c.h, camera, 3, 0.4), { tone: "hi", inner: L(k.sideSeam(deck, c.z + 0.7, camera, 3), { tone: "faint" }) })
    + D(k.corners(deck, 1.4).map(([x, y]) => k.iso([x, y, top], camera)), { size: 0.4 }) + L(k.ring(0, 0, 1.5, top, camera, 14), { tone: "lo" })
    + wheel(-3.2, half) + wheel(3.2, half);
}

function cartDefs() {
  const camera = { ...P, origin: [0, 0] };
  const { r } = C.BEAD, top = C.CART.z + C.CART.h;
  const bead = S(G.sphereOf([0, 0, 0], r, camera, { steps: 22 }), { tone: "hi" });
  const wheel = S(G.disc(-0.52, 0.52, C.CART.wheel, G.frameAlong([0, 0, 0], Y3), camera, { steps: 14 }), { tone: "mid" });
  const rods = [1, 2, 3, 4].map((n) => `<g id="tw-rod-${n}">${S(k.cylinder(0, 0, .48, top, stackTop(n) - top, camera, 10), { tone: "mid", crease: "none" })}</g>`).join("");
  return `<defs><g id="tw-wheel">${wheel}</g><g id="tw-cart">${cartBody(camera)}</g><g id="tw-bead">${bead}</g>${rods}</defs>`;
}

function cartSvg(x, y, h) {
  const n = Math.abs(h), body = M("marble", placeSvg("tw-cart", x, y));
  if (!n) return body;
  const beads = Array.from({ length: n }, (_, i) => placeSvg("tw-bead", x, y, C.CART.z + C.CART.h + C.BEAD.pitch * (i + 0.5))).join("");
  return body + M("ink", placeSvg("tw-rod-" + n, x, y)) + M(h > 0 ? "marble" : "ink", beads);
}
// Every cart of a lane at time s (fractional during a step): the cart that started at cell j sits at j + s.
function cartsSvg(lane, s) {
  const y = C.LANES[lane], v = STATES[lane], list = [];
  const [first, last] = C.SLOTS;
  for (let j = first - FRAMES; j <= last; j++) {
    const slot = j + s;
    // Fade carts at each end while their wheels are still on the rail.
    const fade = Math.min(1, (slot - first) * 5 + 1, (last - slot) * 5 + 1);
    if (fade <= 0) continue;
    const svg = cartSvg(XC(slot), y, cellAt(v, j, 0));
    list.push(fade < 0.999 ? `<g opacity="${fade.toFixed(2)}">${svg}</g>` : svg);
  }
  return list.join("");
}

// The clock: a ratchet wheel on an axle across the stand, turned c teeth from its index; the weight drops
// with every tooth it lets go.
function wheelSvg(lane, c) {
  const y = C.LANES[lane], st = C.STAND, F = G.frameOf([st.x, y + st.face, st.axle], Y3, [1, 0, 0], [0, 0, 1]);
  const turn = (-c * 2 * Math.PI) / st.teeth;
  const tooth = (i) => {
    const a0 = turn + (i * 2 * Math.PI) / st.teeth, a1 = a0 + (2 * Math.PI) / st.teeth;
    const p = (a, r) => [Math.cos(a) * r, Math.sin(a) * r];
    return { a: a0, poly: [p(a0, st.wheel - 0.2), p(a1 - 0.08, st.wheel - 0.2), p(a0 + 0.02, st.wheel + 1.9)] };
  };
  const teeth = Array.from({ length: st.teeth }, (_, i) => tooth(i));
  const V = G.viewOf(P);
  const facing = (t) => G.dot3(G.add3(G.mul3(F.u, Math.cos(t.a)), G.mul3(F.v, Math.sin(t.a))), V);
  const ticks = Array.from({ length: st.teeth }, (_, i) => {
    const a = turn + ((i + 0.5) * 2 * Math.PI) / st.teeth;
    return k.pathOf([G.pointOf(F, 1.6, st.wheel - 2.4, a), G.pointOf(F, 1.6, st.wheel - (i % 3 ? 1.2 : 0.6), a)].map(at));
  });
  const index = k.pathOf([G.pointOf(F, 1.6, st.drum, turn + Math.PI / 2), G.pointOf(F, 1.6, st.wheel - 0.6, turn + Math.PI / 2)].map(at));
  const tip = at(G.pointOf(F, 1.6, st.wheel - 0.6, turn + Math.PI / 2));
  return M("jade",
    ...teeth.filter((t) => facing(t) < 0).map((t) => S(G.prismOf(F, t.poly, 0, 1.6, P), { tone: "mid" })),
    S(G.disc(0, 1.6, st.wheel, F, P), { tone: "hi", inner: L(G.circleOf(F, 1.6, st.wheel - 2.4, P), { tone: "lo" }) }),
    ...teeth.filter((t) => facing(t) >= 0).map((t) => S(G.prismOf(F, t.poly, 0, 1.6, P), { tone: "mid" })),
    L(ticks.join(""), { tone: "lo" }), L(index, { tone: "hi" }), D([tip], { size: 0.7, tone: "hi" }),
    S(G.disc(1.6, 3.2, st.drum, F, P), { tone: "mid", inner: L(G.arcOf(F, 2.4, st.drum, P), { tone: "faint" }) }), S(G.disc(3.2, 3.8, st.drum + 0.6, F, P), { tone: "hi" }));
}
// The weight hangs from the wheel's drum on a cord off its right side, m brass discs on a hanger.
function weightSvg(lane, c) {
  const st = C.STAND, y = C.LANES[lane] + st.face + 2.4, w = C.WEIGHT, m = STATES[lane].m;
  const x = st.x + st.drum, top = w.top - st.drop * (c - STATES[lane].c);
  const out = [L(k.segment([x, y, st.axle], [x, y, top + 1.6], P), { tone: "mid" })];
  out.push(M("ink", S(k.cylinder(x, y, 0.9, top, 1.6, P, 12), { tone: "mid" })));
  for (let i = 0; i < m; i++) out.push(M("marble", S(k.cylinder(x, y, w.r, top - (i + 1) * w.h, w.h, P, 28, 0.4), { tone: "hi", inner: L(k.sideArc(x, y, w.r, top - (i + 1) * w.h + 0.6, P, 18), { tone: "faint" }) })));
  out.push(M("ink", S(k.cylinder(x, y, 1.4, top - m * w.h - 1.6, 1.6, P, 14), { tone: "mid" })));
  return out.join("");
}

// A probe's plunger, out by unit · r above the head.
function plungerSvg(lane, j, r) {
  const x = XC(PROBES[j]), y = C.LANES[lane], z0 = C.PROBE.beam.z + C.PROBE.beam.h, up = C.PLUNGER.unit * r;
  return M("marble", S(k.cylinder(x, y, C.PLUNGER.r, z0, up, P, 16), { tone: "hi", crease: "none", inner: L([5, 10, 15, 20].filter((u) => u < r).map((u) => k.sideArc(x, y, C.PLUNGER.r, z0 + C.PLUNGER.unit * u, P, 10)).join(""), { tone: "lo" }) }),
    S(k.cylinder(x, y, 1.9, z0 + up, 1.1, P, 18, 0.3), { tone: "hi" }));
}

// A recorder pin for frame t, probe j, machine `lane`: unit · r tall.
function pinSvg(t, j, lane, r, lit) {
  const x = C.REC.rows[t], y = C.REC.pins[2 * j + lane], h = C.REC.unit * r;
  if (h < 0.05) return "";
  return M(lane ? "ink" : "marble", S(k.cylinder(x, y, 1.35, C.REC.h, h, P, 16), { tone: "hi", lit, crease: "none" }),
    S(k.cylinder(x, y, 1.85, C.REC.h + h, 0.9, P, 18, 0.3), { tone: "hi", lit }));
}
// The row lamp: jade while the twins' frames agree, red once they differ.
function lampSvg(t, state) {
  const x = C.REC.rows[t];
  const y = (C.REC.pins[1] + C.REC.pins[2]) / 2;
  const material = state === "split" ? "cinnabar" : state ? "jade" : "ink";
  return M(material, S(G.sphereOf([x, y, C.REC.h + 1.25], 1.25, P), { tone: state ? "hi" : "mid" }));
}

// --- static art ------------------------------------------------------------------------------

function base() {
  const out = [`<path class="iso-halo" d="${k.haloOf(C.BASE, -C.BASE_H - C.FOOT_H, C.BASE_H, P)}"/>`];
  for (const [x, y] of byDepth(k.corners(C.BASE, 16), ([x, y]) => [x, y])) {
    out.push(M("ink", S(k.cylinder(x, y, 6.4, -C.BASE_H - C.FOOT_H, 1.4, P, 22), { tone: "lo" }), S(k.cylinder(x, y, 4.8, -C.BASE_H - C.FOOT_H + 1.4, C.FOOT_H - 1.4, P, 22), { tone: "mid" })));
  }
  const screws = k.corners(C.BASE, 8);
  out.push(M("marble", S(k.slabOf(C.BASE, -C.BASE_H, C.BASE_H, P, 8, 1.4), { tone: "mid", inner: L(k.sideSeam(C.BASE, -3.4, P, 8), { tone: "faint" }) }),
    L(k.planOutline(k.insetPlan(C.BASE, 4.5), 0, P), { tone: "lo" }), L(screws.map(([x, y]) => k.ring(x, y, 2, 0, P, 16)).join(""), { tone: "lo" }), D(screws.map(([x, y]) => at([x, y, 0])), { size: 0.5 })));
  return out.join("");
}

// One rail of a lane, with the legs under it.
function railSvg(lane, side) {
  const y = C.LANES[lane] + side * C.RAIL.half, r = C.RAIL;
  const plan = { x: r.x0, y: y - r.w / 2, w: r.x1 - r.x0, d: r.w, r: 0.4 };
  const legs = C.LEGS.map((lx) => M("ink", S(k.slabOf({ x: lx - 1.1, y: y - 1.1, w: 2.2, d: 2.2, r: 0.4 }, 0, r.z, P, 2, 0.3), { tone: "mid" }), S(k.slabOf({ x: lx - 2.6, y: y - 2.6, w: 5.2, d: 5.2, r: 0.8 }, 0, 1.2, P, 3, 0.3), { tone: "mid" })));
  const rail = M("ink", S(k.slabOf(plan, r.z, r.h, P, 2, 0.3), { tone: "mid" }), L(k.lineOnTop([r.x0 + 2.4, y], [r.x1 - 2.4, y], r.z + r.h, P), { tone: "faint" }));
  // Bumpers at both ends of the rail; the centre groove runs between them.
  const stop = (x) => M("jade", S(k.slabOf({ x: x - 1.2, y: y - 1.5, w: 2.4, d: 3, r: 0.5 }, r.z + r.h, 1.6, P, 2, 0.3), { tone: "mid" }));
  return legs.join("") + rail + stop(r.x0 + 1.2) + stop(r.x1 - 1.2);
}
// Cell plates between the rails: an engraved tab per spatial cell, its index in pips; the probed cells ringed.
function cellsSvg(lane) {
  const y = C.LANES[lane], z = C.RAIL.z - 1.4, out = [];
  const bed = { x: C.RAIL.x0 + 3, y: y - C.RAIL.half + 1, w: C.RAIL.x1 - C.RAIL.x0 - 6, d: 2 * C.RAIL.half - 2, r: 0.6 };
  out.push(M("jade", S(k.slabOf(bed, z - 1, 1, P, 2, 0.3), { tone: "mid" })));
  for (let cell = 0; cell < CELLS; cell++) {
    const x = XC(cell);
    out.push(L(k.lineOnTop([x - C.CELL / 2, bed.y], [x - C.CELL / 2, bed.y + bed.d], z, P), { tone: "lo" }));
    out.push(D(Array.from({ length: cell }, (_, i) => at([x - (cell - 1) * 0.6 + i * 1.2, bed.y + bed.d - 0.9, z])), { size: 0.35, tone: "hi" }));
  }
  out.push(L(k.lineOnTop([XC(CELLS) - C.CELL / 2, bed.y], [XC(CELLS) - C.CELL / 2, bed.y + bed.d], z, P), { tone: "lo" }));
  return out.join("");
}

// The probe gantry of a lane at cell i_j: a column outside the line (in front of A, behind B), so nothing
// stands between the twins, and an arm out over the cart line. Both machines carry the same pair.
function gantryColumn(lane, j) {
  const x = XC(PROBES[j]), side = lane ? -1 : 1, y = C.LANES[lane] + side * 12, pb = C.PROBE.beam;
  const foot = { x: x - 3.6, y: y - 3.6, w: 7.2, d: 7.2, r: 1.2 };
  return M("ink", S(k.slabOf(foot, 0, 1.6, P, 3, 0.4), { tone: "mid" }), D(k.corners(foot, 1.3).map(([cx, cy]) => at([cx, cy, 1.6])), { size: 0.4 }),
    S(k.cylinder(x, y, 1.8, 1.6, pb.z - 1.6, P, 20), { tone: "mid", crease: "none", inner: L([8, 20].map((z) => k.sideArc(x, y, 1.8, z, P, 12)).join(""), { tone: "faint" }) }));
}
// The arm, with a(j + 1) pips on its end cap: the clock's weight in this probe's reading.
function gantryArm(lane, j) {
  const x = XC(PROBES[j]), side = lane ? -1 : 1, ly = C.LANES[lane], y = ly + side * 12, p = C.PROBE, pb = p.beam;
  const y0 = Math.min(y, ly - side * p.half) - 2, y1 = Math.max(y, ly - side * p.half) + 2;
  const arm = { x: x - 1.8, y: side > 0 ? ly - p.half : y0, w: 3.6, d: side > 0 ? y1 - (ly - p.half) : ly + p.half - y0, r: 0.6 };
  const cap = { x: x - 2.8, y: y - 2.8, w: 5.6, d: 5.6, r: 1 }, n = A_SCALE * (j + 1);
  return M("jade", S(k.slabOf(arm, pb.z, pb.h, P, 2, 0.3), { tone: "mid" })) +
    M("ink", S(k.slabOf(cap, pb.z - 0.6, pb.h + 1.4, P, 3, 0.4), { tone: "mid" }),
      D(Array.from({ length: n }, (_, i) => at([x - 1.1 + (i % 2) * 2.2, y + (n > 2 ? -1.1 + Math.floor(i / 2) * 2.2 : 0), pb.z + pb.h + 0.8])), { size: 0.42, tone: "hi" }));
}
// A probe head hanging under the arm over a lane.
function probeHead(lane, j) {
  const x = XC(PROBES[j]), y = C.LANES[lane], p = C.PROBE, pb = p.beam;
  const head = { x: x - p.half, y: y - p.half, w: 2 * p.half, d: 2 * p.half, r: 0.8 };
  return M("marble", S(k.slabOf(head, p.z, pb.z - p.z, P, 3, 0.4), { tone: "hi", inner: L(k.sideSeam(head, p.z + 1.2, P, 3), { tone: "faint" }) })) +
    L(k.ring(x, y, 2.1, pb.z + pb.h, P, 18), { tone: "lo" });
}
// The feeler drops from the head onto the cart below: on its top bead, or on the deck when the cell is
// empty. While the line moves it is parked clear of every stack. `drop` ∈ [0, 1] eases between the two.
function feelerSvg(lane, j, h, drop) {
  const x = XC(PROBES[j]), y = C.LANES[lane], p = C.PROBE, tip = p.park + (stackTop(h) + 0.8 - p.park) * drop;
  return M("ink", S(k.cylinder(x, y, 0.45, tip, p.z - tip, P, 10), { tone: "mid", crease: "none" }), S(k.cylinder(x, y, 1, p.z - 1.6, 1.6, P, 14), { tone: "mid" })) +
    M("ink", S(G.sphereOf([x, y, tip], 0.8, P), { tone: "hi" }));
}

// The clock stand: two posts and a cap; the axle runs from the back post through the front one and carries
// the wheel outside it, like the face of a wall clock.
function standBack(lane) {
  const y = C.LANES[lane], st = C.STAND, F = G.frameAlong([st.x, y - st.half, st.axle], Y3);
  return post(st.x, y - st.half) + M("ink", S(G.disc(1.6, st.half * 2, 0.8, F, P), { tone: "mid", crease: "none" }));
}
function standFront(lane) {
  const y = C.LANES[lane], st = C.STAND, F = G.frameAlong([st.x, y + st.half, st.axle], Y3);
  const cap = { x: st.x - 3, y: y - st.half - 2, w: 6, d: 2 * st.half + 4 + st.face - st.half, r: 0.8 };
  return post(st.x, y + st.half) + M("ink", S(k.slabOf(cap, st.h, 2.2, P, 3, 0.4), { tone: "mid" }), D([at([st.x, y - st.half, st.h + 2.2]), at([st.x, y + st.half, st.h + 2.2])], { size: 0.45 })) +
    M("marble", S(G.disc(0, st.face - st.half, 0.8, F, P), { tone: "mid", crease: "none" }), S(G.disc(0.2, 1.2, 1.9, F, P), { tone: "hi" }));
}
// The pawl: a short lever hung from the cap's front end, resting on the wheel's top teeth.
function pawlSvg(lane) {
  const y = C.LANES[lane], st = C.STAND, z0 = st.h, z1 = st.axle + st.wheel + 1.3;
  const F = G.frameAlong([st.x - 1.2, y + st.face + 0.8, z0], [0.3, 0, -1]);
  return M("ink", S(G.disc(0, Math.hypot(0.3 * (z0 - z1), z0 - z1), 0.6, F, P), { tone: "mid" }));
}
function post(x, y) {
  const st = C.STAND;
  return M("ink", S(k.slabOf({ x: x - 3, y: y - 3, w: 6, d: 6, r: 1 }, 0, 1.6, P, 3, 0.4), { tone: "mid" }), S(k.cylinder(x, y, 1.6, 1.6, st.h - 1.6, P, 16), { tone: "mid", crease: "none", inner: L(k.sideArc(x, y, 1.6, 12, P, 10), { tone: "faint" }) }));
}

// The step shaft under both stands, with a gearbox at each lane and the crank in front.
function shaftSvg() {
  const sh = C.SHAFT, F = G.frameAlong([sh.x, sh.y0, sh.z], Y3);
  const boxes = C.LANES.map((y) => ({ x: sh.x - 3.4, y: y - 4, w: 9, d: 8, r: 1 }));
  return M("ink", S(G.disc(0, sh.y1 - sh.y0, sh.r, F, P), { tone: "mid", crease: "none" })) +
    boxes.map((b) => M("ink", S(k.slabOf(b, 0, 9.4, P, 3, 0.5), { tone: "mid", inner: L(k.sideSeam(b, 6, P, 3), { tone: "faint" }) }), D(k.corners(b, 1.3).map(([x, y]) => at([x, y, 9.4])), { size: 0.4 }))).join("");
}
// The drive from a lane's gearbox to the sprocket at the head of its cart line.
function driveSvg(lane) {
  const y = C.LANES[lane], x0 = C.SHAFT.x + 5.6, x1 = C.RAIL.x0 + 2, z = 5.2;
  const F = G.frameAlong([x0, y, z], [1, 0, 0]), S2 = G.frameAlong([x1, y - C.RAIL.half + 1, z], Y3);
  return M("ink", S(G.disc(0, x1 - x0, 0.9, F, P), { tone: "mid", crease: "none" })) +
    M("ink", S(G.disc(0, 2 * C.RAIL.half - 2, 3.2, S2, P), { tone: "hi", inner: L(G.circleOf(S2, 2 * C.RAIL.half - 2, 1.4, P), { tone: "lo" }) }));
}
function crankSvg(angle) {
  const sh = C.SHAFT, y = sh.y1;
  const arm = [sh.x + Math.cos(angle) * 4.6, y + 1.2, sh.z + Math.sin(angle) * 4.6];
  const F = G.frameAlong([sh.x, y, sh.z], Y3), K = G.frameAlong(arm, Y3);
  return M("ink", S(G.disc(0, 1.2, 2.2, F, P), { tone: "mid" }), S(G.prismOf(G.frameOf([sh.x, y, sh.z], Y3, [Math.cos(angle), 0, Math.sin(angle)], [-Math.sin(angle), 0, Math.cos(angle)]), [[0, -1.1], [4.6, -0.9], [4.6, 0.9], [0, 1.1]], 0.2, 1.2, P), { tone: "mid" })) +
    M("jade", S(G.disc(0, 5.2, 1.3, K, P), { tone: "hi", inner: L(G.arcOf(K, 2.6, 1.3, P), { tone: "faint" }) }));
}

function recorderSvg() {
  const r = C.REC, tray = { x: r.x, y: r.y, w: r.w, d: r.d, r: 2 };
  const sockets = r.rows.flatMap((x) => r.pins.map((y) => k.ring(x, y, 2.2, r.h, P, 18))).join("");
  const pips = r.rows.map((x, t) => D(Array.from({ length: t + 1 }, (_, i) => at([x - t * 0.7 + i * 1.4, r.y + r.d - 2, r.h])), { size: 0.45, tone: t === FRAMES - 1 ? "hi" : "mid" })).join("");
  // A rule between the two probes' pairs, and the window's frame a + 1 boxed.
  const last = { x: r.rows[2] - 6, y: r.y + 2, w: 12, d: r.d - 4, r: 1.4 };
  return M("jade", S(k.slabOf(tray, 0, r.h, P, 4, 0.5), { tone: "mid", inner: L(k.sideSeam(tray, 1.2, P, 4), { tone: "faint" }) }),
    L(k.planOutline(k.insetPlan(tray, .65), r.h, P, 4), { className: "polished-edge" }),
    L(sockets, { tone: "lo" }), L(k.lineOnTop([r.x, (r.pins[1] + r.pins[2]) / 2], [r.x + r.w, (r.pins[1] + r.pins[2]) / 2], r.h, P), { tone: "faint" }), L(k.planOutline(last, r.h, P, 3), { tone: "mid" }), pips,
    D(k.corners(tray, 2).map(([x, y]) => at([x, y, r.h])), { size: 0.45 }),
    k.faceTextSvg(k.sideMatrix([r.x + r.w, r.y + r.d - 6], 1, P, "right"), "a + 1 = 3", { size: 2.4, tone: "hi" }));
}

function laneLabel(lane) {
  return k.faceTextSvg(k.topMatrix([-68, C.LANES[lane] + 10], 0, P), lane === 0 ? "A" : "B", { size: 5, anchor: "middle", tone: "hi" });
}

// The live view: time s ∈ [0, a] (fractional during a step), what each plunger shows, how far each pin is up.
function composition(view) {
  const lane = (index) => [
    railSvg(index, -1),
    cellsSvg(index),
    `<g data-part="carts-${index}">${cartsSvg(index, view.s)}</g>`,
    railSvg(index, 1),
    laneLabel(index),
  ].join("");
  // A probe from the top down: feeler, head, arm, plunger; A's columns stand in front of everything of A.
  const probes = (index) => [0, 1].map((j) => `<g data-part="feeler-${index}-${j}">${feelerSvg(index, j, cellAt(STATES[index], PROBES[j], Math.round(view.s)), view.drop)}</g>` + probeHead(index, j) + (index ? "" : gantryColumn(index, j)) + gantryArm(index, j) + `<g data-part="plunger-${index}-${j}">${plungerSvg(index, j, view.plungers[index][j])}</g>`).join("");
  const stand = (index) => [
    standBack(index),
    standFront(index),
    `<g data-part="wheel-${index}">${wheelSvg(index, clockAt(STATES[index], view.s))}</g>`,
    pawlSvg(index),
    `<g data-part="weight-${index}">${weightSvg(index, clockAt(STATES[index], view.s))}</g>`,
  ].join("");
  const pins = (t) => [0, 1].flatMap((j) => [1, 0].map((who) => `<g data-part="pin-${t}-${j}-${who}">${pinSvg(t, j, who, view.pins[t][j][who], view.lit === t)}</g>`)).join("") + `<g data-part="lamp-${t}">${lampSvg(t, view.lamps[t])}</g>`;
  return [
    cartDefs(),
    base(),
    shaftSvg(),
    driveSvg(1),
    stand(1),
    gantryColumn(1, 0), gantryColumn(1, 1),
    lane(1),
    probes(1),
    driveSvg(0),
    stand(0),
    `<g data-part="crank">${crankSvg(view.s * 2 * Math.PI)}</g>`,
    lane(0),
    probes(0),
    recorderSvg(),
    ...[0, 1, 2].map(pins),
  ].join("");
}

// The resting view after `frames` recorded frames (1 … a + 1).
function viewAt(frames) {
  const t = frames - 1;
  const reading = STATES.map((v) => responseOf(v, t));
  const rows = [0, 1, 2].map((row) => (row < frames ? [0, 1].map((j) => STATES.map((v) => responseOf(v, row)[j])) : [[0, 0], [0, 0]]));
  return {
    s: t,
    drop: 1,
    plungers: reading,
    pins: rows,
    lamps: [0, 1, 2].map((row) => (row < frames ? (responseOf(STATES[0], row).join() === responseOf(STATES[1], row).join() ? "same" : "split") : null)),
    lit: frames === FRAMES ? FRAMES - 1 : -1,
  };
}
const pair = (r) => "(" + r.join(", ") + ")";
function readoutOf(frames, lang) {
  const t = frames - 1, a = responseOf(STATES[0], t), b = responseOf(STATES[1], t), same = a.join() === b.join();
  const zh = lang === "zh";
  const frame = zh ? "第 " + frames + " 帧" : "Frame " + frames;
  return frame + (same ? " · A = B " + pair(a) : " · A " + pair(a) + " · B " + pair(b));
}
const REST = viewAt(FRAMES);
const art = composition(REST);
const CSS = paperFigureCss;

const strip = (file) => readFileSync(join(HERE, file), "utf8").replace(/^export /gm, "");
const kitSource = strip("../kit/iso-kit.mjs");
const latheSource = `const LATHE = (() => {\n${strip("../kit/lathe.mjs").replace(/^import .*$/gm, "")}\nreturn { ${Object.keys(G).join(", ")} };\n})();`;
const MODEL = ["A_SCALE", "FRAMES", "PROBES", "TWIN", "SIGNAL", "cellAt", "clockAt", "responseOf"];
const modelSource = `const { ${MODEL.join(", ")} } = (() => {\n${strip("model.mjs")}\nreturn { ${MODEL.join(", ")} };\n})();`;
const live = `
const P0 = ${JSON.stringify(P0)};
let P = P0;
${shipped({ C, CELLS, FRAME })}
const STATES = [SIGNAL, TWIN];
const k = { ${Object.keys(k).join(", ")} };
const G = LATHE;
${shipped({ XC, at, S, L, D, M, depthAt, byDepth, Y3, stackTop, placeSvg, cartBody, cartDefs, cartSvg, cartsSvg, wheelSvg, weightSvg, plungerSvg, pinSvg, lampSvg, base, railSvg, cellsSvg, gantryColumn, gantryArm, probeHead, feelerSvg, standBack, standFront, pawlSvg, post, shaftSvg, driveSvg, crankSvg, recorderSvg, laneLabel, composition, viewAt, pair, readoutOf })}
${swingSource}
${paperFigureSource}
const root = document.querySelector('[data-figure="twin-window"]');
const lang = root.lang;
const stage = root.querySelector(".iso-stage");
const svgEl = stage.querySelector("svg");
const paintPart = partPainter(stage);
const readout = root.querySelector("[data-readout]");
const buttons = [...root.querySelectorAll("[data-frame]")];
const still = matchMedia("(prefers-reduced-motion: reduce)");
let frames = FRAMES;
const view = viewAt(FRAMES);
let goal = viewAt(FRAMES), moving = false;
let touring = !still.matches, tourClock = 0;

function goTo(next) {
  if (next === frames) return;
  frames = next;
  goal = viewAt(frames);
  for (const button of buttons) button.setAttribute("aria-pressed", String(Number(button.dataset.frame) === frames));
  if (still.matches) { settle(); return; }
  moving = true;
  view.lit = -1;
  readout.textContent = root.dataset.moving;
  run();
}
function settle() {
  Object.assign(view, viewAt(frames));
  moving = false;
  paint();
  const text = readoutOf(frames, lang);
  if (readout.textContent !== text) readout.textContent = text;
}
function move(dt) {
  if (view.s !== goal.s && view.drop === 0) {
    const d = goal.s - view.s, distance = dt * (d < 0 ? 2.7 : 1.6);
    view.s += Math.sign(d) * Math.min(distance, Math.abs(d));
  }
  const docked = view.s === goal.s;
  view.drop = easeTo(view.drop, Number(docked), dt, 0.07, 0.025);
  const sampled = docked && view.drop === 1;
  for (let lane = 0; lane < 2; lane++) for (let j = 0; j < 2; j++) {
    if (sampled) view.plungers[lane][j] = easeTo(view.plungers[lane][j], goal.plungers[lane][j], dt, 0.12, 0.06);
  }
  let pinsReady = true;
  for (let t = 0; t < FRAMES; t++) {
    let rowReady = true;
    for (let j = 0; j < 2; j++) for (let who = 0; who < 2; who++) {
      const want = goal.pins[t][j][who];
      if (sampled || want === 0) view.pins[t][j][who] = easeTo(view.pins[t][j][who], want, dt, 0.13, 0.06);
      rowReady &&= view.pins[t][j][who] === want;
    }
    pinsReady &&= rowReady;
    view.lamps[t] = rowReady ? goal.lamps[t] : null;
  }
  const probesReady = view.plungers.every((row, lane) => row.every((n, j) => n === goal.plungers[lane][j]));
  if (sampled && pinsReady && probesReady) settle();
  else paint();
}
function paint() {
  for (let lane = 0; lane < 2; lane++) {
    const c = clockAt(STATES[lane], view.s);
    paintPart("carts-" + lane, view.s, () => cartsSvg(lane, view.s));
    paintPart("wheel-" + lane, c, () => wheelSvg(lane, c));
    paintPart("weight-" + lane, c, () => weightSvg(lane, c));
    for (let j = 0; j < 2; j++) {
      const r = view.plungers[lane][j], h = cellAt(STATES[lane], PROBES[j], Math.round(view.s));
      paintPart("plunger-" + lane + "-" + j, r, () => plungerSvg(lane, j, r));
      paintPart("feeler-" + lane + "-" + j, view.drop ? h + ":" + view.drop : 0, () => feelerSvg(lane, j, h, view.drop));
    }
  }
  paintPart("crank", view.s, () => crankSvg(view.s * 2 * Math.PI));
  for (let t = 0; t < FRAMES; t++) {
    for (let j = 0; j < 2; j++) for (let who = 0; who < 2; who++) {
      const r = view.pins[t][j][who], lit = view.lit === t;
      paintPart("pin-" + t + "-" + j + "-" + who, r + ":" + lit, () => pinSvg(t, j, who, r, lit));
    }
    paintPart("lamp-" + t, view.lamps[t], () => lampSvg(t, view.lamps[t]));
  }
}
function step(dt) {
  if (moving) move(dt);
  else if (touring) {
    tourClock += dt;
    if (tourClock > (frames === FRAMES ? 4.2 : 1.65)) { tourClock = 0; goTo(frames % FRAMES + 1); }
  }
  return moving || touring;
}
const run = playOnScreen(stage, still, step, () => { touring = false; settle(); });
const hold = () => { touring = false; readout.setAttribute("aria-live", "polite"); };
const choose = (next) => { hold(); goTo(next); };
root.addEventListener("focusin", hold);
buttons.forEach((button) => button.addEventListener("click", () => choose(Number(button.dataset.frame))));
stage.addEventListener("click", () => choose(frames % FRAMES + 1));
stage.addEventListener("keydown", (event) => {
  if (event.key === "ArrowRight" || event.key === "ArrowUp" || event.key === " " || event.key === "Enter") choose(frames % FRAMES + 1);
  else if (event.key === "ArrowLeft" || event.key === "ArrowDown") choose((frames + FRAMES - 2) % FRAMES + 1);
  else if (event.key === "Home") choose(1);
  else if (event.key === "End") choose(FRAMES);
  else return;
  event.preventDefault();
});
mountSwing(stage, { touch: false, limit: 24, home: 2500, onHold: hold, onDragStart: run.pause, onDragEnd: run.resume, onSwing: (angle) => { P = swingOf(k.iso, P0, FRAME, angle); svgEl.innerHTML = composition(view); paintPart.reset(); } });
// For checks: drive.mjs sets the window directly.
window.__twinWindow = (n) => { choose(n); settle(); };
`;

const COPY = {
  en: {
    title: "Twin observation machines",
    hint: "Drag to rotate · ← → step through frames",
    moving: "Moving to the selected frame…",
    frames: "Observation frames",
    frame: (n) => `Frame ${n}`,
    keys: ["Recorder pins · white for A, graphite for B", "Red lamp · first differing frame", "Cart beads · white +1, graphite −1"],
    refs: ["Theorems 3.3–3.4", "Example 3.2"],
    caption: [
      "At copy scale a = 2, two frames agree and the third splits. Each step shifts the carts one cell right and advances the clock by the mass m. The probes at cells 1 and 3 add that cell’s value, the mass, and respectively 2 or 4 times the current clock.",
      "At the start, A carries a unit signal at cell 2, with (m, c) = (1, 3). B carries (−3, −1, −4, −1), with (m, c) = (2, 3). Its negative beads cancel the extra mass and clock contributions in the first two frames: both machines read (7, 13), then (9, 18). A two-frame update would have to predict two different continuations from the same input.",
      "In frame 3, cell 1 has no spatial contribution. The readings split into A (11, 21) and B (16, 29). For this two-column observer, three frames recover the initial mass, clock and four spatial coordinates h₀ to h₃. Those six values determine every future reading.",
    ],
    aria: "Twin observation machines. Arrow keys step through frames 1 to 3.",
    alt: "Two conveyors carry signed beads past two probes. Each clock advances by its mass. The recorder shows equal pin heights for the first two frames and unequal heights beside a red lamp for the third.",
  },
  zh: {
    title: "孪生观测机",
    hint: "拖动旋转 · ← → 切换帧",
    moving: "正在切换观测帧…",
    frames: "观测帧",
    frame: (n) => `第 ${n} 帧`,
    keys: ["记录针 · 白色为 A，石墨色为 B", "朱红灯 · 第一帧不同的读数", "车上珠子 · 白色 +1，石墨色 −1"],
    refs: ["定理 3.3–3.4", "例 3.2"],
    caption: [
      "复制尺度 a = 2 时，两台机器前两帧读数相同，第三帧分开。每一步，小车整体右移一格，时钟按质量 m 前进。格 1 与格 3 的探头各取所在格的值，加上质量，再分别加上当前时钟的 2 倍与 4 倍。",
      "起初 A 在格 2 有单位信号，(m, c) = (1, 3)。B 装有 (−3, −1, −4, −1)，(m, c) = (2, 3)。负值在前两帧抵消了 B 多出的质量和时钟贡献。两台先读 (7, 13)，再读 (9, 18)。两帧更新若要成立，同一输入就得产生两种后续读数。",
      "第三帧的格 1 没有空间项，A 读 (11, 21)，B 读 (16, 29)。对这台两列观测器，三帧可以恢复初始质量、时钟和四个空间坐标 h₀ 至 h₃。这六个值确定所有未来读数。",
    ],
    aria: "孪生观测机。方向键切换第 1 至第 3 帧。",
    alt: "两列小车载着有号珠子经过两枚探头。每台时钟按质量前进。记录盘前两帧的针高相同，第三帧针高不同，朱红灯亮起。",
  },
};
const bodyOf = (lang) => {
  const copy = COPY[lang];
  const svg = k.figureSvg({ width: WIDTH, height: HEIGHT, className: "paper-figure-art", label: copy.alt, body: art });
  const buttons = Array.from({ length: FRAMES }, (_, i) => `<button type="button" data-frame="${i + 1}" aria-pressed="${i + 1 === FRAMES}">${copy.frame(i + 1)}</button>`).join("");
  return `<div data-figure="twin-window" lang="${lang}" data-moving="${copy.moving}">${paperPlate({
    title: copy.title,
    hint: copy.hint,
    readout: readoutOf(FRAMES, lang),
    keys: [
      { mark: "lit", label: copy.keys[0] },
      { mark: "red", label: copy.keys[1] },
      { mark: "dim", label: copy.keys[2] },
    ],
    caption: copy.caption,
    refs: copy.refs,
    body: `<div class="iso-stage paper-figure-stage" data-advance tabindex="0" role="group" aria-label="${copy.aria}">${svg}</div><div class="paper-figure-controls" role="group" aria-label="${copy.frames}">${buttons}</div>`,
  })}</div>`;
};

const script = `{\n${kitSource}\n${latheSource}\n${modelSource}\n${live}\n}`;
if (fragment) {
  const outDir = join(HERE, "../../src/generated");
  mkdirSync(outDir, { recursive: true });
  writeFileSync(join(outDir, "twin-window.json"), JSON.stringify({ html: { zh: bodyOf("zh"), en: bodyOf("en") }, css: CSS, script: script.replace(/<\/(script)/gi, "<\\/$1") }));
  console.log("wrote src/generated/twin-window.json");
} else {
  mkdirSync(join(HERE, "out"), { recursive: true });
  const lang = process.argv.includes("--zh") ? "zh" : "en";
  const name = theme === "light" ? "twin-window-light.html" : "twin-window.html";
  writeFileSync(join(HERE, "out", name), k.pageHtml({ title: COPY[lang].title, theme, body: `<style>${CSS}</style>${bodyOf(lang)}`, script, width: 740 }));
  console.log("wrote out/" + name);
}
