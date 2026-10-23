// Fig: a glass dome stamped direction by direction with the sign of the response curvature,
// the five terms summed on a Kelvin cord (Theorem 1.2, §§7–11).
//   bun build.mjs [--light] [--zh] → out/curvature-dome[-light].html (standalone, for checks)
//   bun build.mjs --fragment       → ../../src/generated/curvature-dome.json (for the site)
import { mkdirSync, readFileSync, writeFileSync } from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";
import * as k from "../kit/iso-kit.mjs";
import * as G from "../kit/lathe.mjs";
import * as M from "./model.mjs";

const HERE = dirname(fileURLToPath(import.meta.url));
const theme = process.argv.includes("--light") ? "light" : "dark";
const fragment = process.argv.includes("--fragment");

const WIDTH = 640;

// World: x along the bench, y toward the viewer, z up.
const C = {
  PLATE: { x: -130, y: -72, w: 334, d: 138, r: 8 },
  PLATE_H: 10,
  FOOT_H: 5,
  // The dome: the hub sits at the centre of the sphere of directions; the glass is its upper half.
  DOME: { c: [-56, -4], z: 36, R: 58 },
  BASE: { r: 66, h: 2.4 },
  RING: { rIn: 53, rOut: 63, h: 2.6 },
  LEGS: [252, 12, 132],
  LEG_R: 59.5,
  // Headings in the world plane: +e1 points front-left, +e3 front-right (e1 × e2 = e3, e2 up).
  E1: 117,
  STAMP: 1.5,
  // The window: two balls of radius BW; the observation ball slides out to SLIDE along n.
  BW: 12.5,
  SLIDE: 10,
  // The Kelvin frame: fixed pulleys below, moving pulleys above, all in the plane y = FRAME.y.
  FRAME: { y: 22, postY: 10, x0: 60, r: 5, zF: 34, zM: 68, beam: 98, left: 44 },
  GAIN: 10, // cord travel per 10⁻²⁰ of curvature
  DRUM: { r: 10.6 },
  DIAL: { r: 14 },
  // The cord's free end is held taut by a spring to the bench; its hook sits at rest + travel.
  SPRING: { rest: 30, r: 2.6, turns: 9, foot: 4.2 },
  FINE: 50, // the range lever's second scale: the needle turns 50× faster
  SELECTOR: [100, 52],
  LABEL: { x: 130, y: 44, w: 46, d: 13, r: 1.5 },
};
C.FIXED = Array.from({ length: 6 }, (_, i) => C.FRAME.x0 + 20 * i);
C.MOVING = Array.from({ length: 5 }, (_, i) => C.FRAME.x0 + 10 + 20 * i);
// Crossheads in the paper's order: the two quantum source legs, the reader contact, the two field legs.
C.HEADS = [
  { term: "Q", pulleys: [0, 1] },
  { term: "C", pulleys: [2] },
  { term: "G", pulleys: [3, 4] },
].map((head) => ({ ...head, x: head.pulleys.reduce((sum, i) => sum + C.MOVING[i], 0) / head.pulleys.length }));
C.DRUM.x = C.FIXED[5] + C.FRAME.r + C.DRUM.r;
C.DRUM.z = C.FRAME.zM;
C.RIGHT = C.DRUM.x;

// The frame: fit the width, then size the height to the drawing.
const FIT = [
  ...k.boxCorners(C.PLATE, -C.PLATE_H - C.FOOT_H, 0),
  [C.DOME.c[0], C.DOME.c[1], C.DOME.z + C.DOME.R + 7],
  [C.DOME.c[0] - C.DOME.R, C.DOME.c[1], C.DOME.z + 20],
  [C.FRAME.left, C.FRAME.postY, C.FRAME.beam + 6],
  [C.RIGHT, C.FRAME.postY, C.FRAME.beam + 6],
];
const VIEW = { pad: 18, azimuth: 72, elevation: 30 };
const HEIGHT = (() => {
  const wide = k.fitProjection(FIT, WIDTH, 10000, VIEW);
  const ys = FIT.map((point) => k.iso(point, wide)[1]);
  return Math.ceil(Math.max(...ys) - Math.min(...ys) + 2 * VIEW.pad);
})();
const P = k.fitProjection(FIT, WIDTH, HEIGHT, VIEW);

// --- live drawing: one factory shared by the build (first frame) and the page --------------

function makeLive(k, G, P, C, M) {
  const at = (p) => k.iso(p, P);
  const S = (paths, style) => k.solidSvg(paths, style);
  const L = (d, style) => k.lineSvg(d, style);
  const D = (points, style) => k.dotsSvg(points, style);
  const seg = (a, b) => k.segment(a, b, P);
  const poly = (points, closed = false) => k.pathOf(points.map(at), closed);
  const depth = (p) => k.depthOf(p, P);
  const add = (a, b) => [a[0] + b[0], a[1] + b[1], a[2] + b[2]];
  const mul = (s, a) => [s * a[0], s * a[1], s * a[2]];
  const dot = (a, b) => a[0] * b[0] + a[1] * b[1] + a[2] * b[2];
  const cross = (a, b) => [a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]];
  const unit = (v) => { const n = Math.hypot(...v) || 1; return [v[0] / n, v[1] / n, v[2] / n]; };
  const TAU = Math.PI * 2;
  const RAD = Math.PI / 180;
  const cA = Math.cos(P.azimuth * RAD), sA = Math.sin(P.azimuth * RAD), cE = Math.cos(P.elevation * RAD), sE = Math.sin(P.elevation * RAD);
  const V = [cA * cE, sA * cE, sE]; // toward the viewer
  const loop = (c, u, v, r, n = 56) => Array.from({ length: n }, (_, i) => add(c, add(mul(r * Math.cos((i / n) * TAU), u), mul(r * Math.sin((i / n) * TAU), v))));
  // A closed 3D loop split into what lies behind and in front of a reference depth.
  function halves(points, ref) {
    const out = { back: [], front: [] };
    const n = points.length;
    let start = 0;
    while (start < n && depth(points[start]) < ref === depth(points[(start + n - 1) % n]) < ref) start++;
    if (start === n) {
      (depth(points[0]) < ref ? out.back : out.front).push(poly(points, true));
      return { back: out.back.join(""), front: out.front.join("") };
    }
    let run = [points[start]];
    for (let i = 1; i <= n; i++) {
      const p = points[(start + i) % n];
      if (depth(p) < ref !== depth(run[0]) < ref) {
        run.push(p);
        (depth(run[0]) < ref ? out.back : out.front).push(poly(run));
        run = [p];
      } else run.push(p);
    }
    if (run.length > 1) (depth(run[0]) < ref ? out.back : out.front).push(poly(run));
    return { back: out.back.join(""), front: out.front.join("") };
  }
  const rod = (from, to, r, style, steps = 14) => {
    const length = Math.hypot(to[0] - from[0], to[1] - from[1], to[2] - from[2]);
    return length < 0.05 ? "" : S(G.disc(0, length, r, G.frameAlong(from, [to[0] - from[0], to[1] - from[1], to[2] - from[2]]), P, { steps }), style);
  };

  // Directions. n is in the paper's basis (e1, e2, e3); the world puts e2 up and e1, e3 on the bench.
  const h1 = C.E1 * RAD, h3 = (C.E1 - 90) * RAD;
  const E1 = [Math.cos(h1), Math.sin(h1), 0], E3 = [Math.cos(h3), Math.sin(h3), 0];
  const world = (n) => [n[0] * E1[0] + n[2] * E3[0], n[0] * E1[1] + n[2] * E3[1], n[1]];
  const HUB = [C.DOME.c[0], C.DOME.c[1], C.DOME.z];
  const nOf = (state) => M.directionOf(state.el, state.az);

  // Paints are inline so the drawing reads the same wherever its SVG is shown on its own.
  const PAINT = { 1: "fill:var(--anatomy-lit)", 0: "fill:var(--anatomy-mid)", [-1]: "fill:var(--anatomy-lo)" };
  const GLASS = "fill:var(--anatomy-face);opacity:.5";
  // The stamps on the glass: a small disc in the tangent plane, its state written by the arm.
  const STAMPS = M.stamps().map((stamp) => {
    const w = world(stamp.n);
    const t1 = Math.abs(w[2]) > 0.99 ? [1, 0, 0] : unit(cross([0, 0, 1], w));
    const t2 = cross(w, t1);
    const c = add(HUB, mul(C.DOME.R, w));
    const rim = Array.from({ length: 12 }, (_, i) => add(c, add(mul(C.STAMP * Math.cos((i / 12) * TAU), t1), mul(C.STAMP * Math.sin((i / 12) * TAU), t2))));
    return { ...stamp, w, front: dot(w, V) > 0, rim, c };
  });
  function stampSvg(stamp, v) {
    if (v === 2) return "";
    const d = poly(stamp.rim, true);
    if (v === 0) return `<path data-v="0" d="${d}" style="${PAINT[0]}"/><path d="${poly(stamp.rim.slice(0, 7), true)}" style="${PAINT[1]}"/>`;
    return `<path data-v="${v}" d="${d}" style="${PAINT[v]}"/>`;
  }
  // Unstamped places show as a faint printed dot; the arm overwrites them as it passes.
  function stamps(state, side) {
    const wantFront = side === "front";
    const marks = [], blank = [];
    STAMPS.forEach((stamp, i) => {
      if (stamp.front !== wantFront) return;
      const v = state.stamps[i];
      if (v === 2) blank.push(at(stamp.c));
      else marks.push(stampSvg(stamp, v));
    });
    return D(blank, { size: 0.45, tone: "lo" }) + marks.join("");
  }

  // The window at the hub: the incoming ball fixed, the observation ball at s along n.
  function lensHull(w, s) {
    const R = C.BW, points = [];
    const N = 220;
    for (let i = 0; i < N; i++) {
      const z = 1 - (2 * (i + 0.5)) / N, r = Math.sqrt(1 - z * z), a = i * Math.PI * (3 - Math.sqrt(5));
      const u = [r * Math.cos(a), r * Math.sin(a), z];
      const along = dot(u, w);
      if (along >= s / (2 * R)) points.push(at(add(HUB, mul(R, u))));
      if (along <= -s / (2 * R)) points.push(at(add(add(HUB, mul(s, w)), mul(R, u))));
    }
    // The rim where the two spheres meet.
    const rho = Math.sqrt(Math.max(0, R * R - (s * s) / 4));
    const t1 = Math.abs(w[2]) > 0.99 ? [1, 0, 0] : unit(cross([0, 0, 1], w)), t2 = cross(w, t1);
    const rim = loop(add(HUB, mul(s / 2, w)), t1, t2, rho, 48);
    rim.forEach((p) => points.push(at(p)));
    return { hull: k.pathOf(G.hullOf(points), true), rim, t1, t2 };
  }

  // The hub, the arm and the window. Parts are sorted by depth; the arm's outer half goes
  // behind or in front of the window balls depending on which way it points.
  function arm(state) {
    const n = nOf(state), w = world(n);
    const heading = Math.atan2(w[1], w[0]);
    const horiz = [Math.cos(heading), Math.sin(heading), 0];
    const axis = [-horiz[1], horiz[0], 0]; // trunnion axis, horizontal and across the arm
    const R = C.DOME.R, B = C.BW, s = state.s;
    const out = [];
    const ref = depth(HUB);
    // Ghost balls: back rings first.
    const inRings = [halves(loop(HUB, [1, 0, 0], [0, 1, 0], B, 64), ref), halves(loop(HUB, horiz, [0, 0, 1], B, 64), ref)];
    const obs = add(HUB, mul(s, w));
    const lens = lensHull(w, s);
    const obsRing = halves(loop(obs, lens.t1, lens.t2, B, 64), depth(obs));
    out.push(L(inRings.map((ring) => ring.back).join("") + obsRing.back, { tone: "faint" }));
    out.push(`<path d="${G.sphereOf(HUB, B, P, { steps: 48 }).outline}" style="${GLASS}"/>`);
    if (s > 0.05) out.push(`<path d="${G.sphereOf(obs, B, P, { steps: 48 }).outline}" style="${GLASS}"/>`);
    // The arm's outer half when it points away from the viewer.
    const head0 = R - 7, head1 = R - 2.6;
    const outer = () => [
      rod(add(HUB, mul(B, w)), add(HUB, mul(head0, w)), 0.8, { tone: "mid" }),
      rod(add(HUB, mul(head0, w)), add(HUB, mul(head1, w)), 1.9, { tone: "hi" }, 18),
      L(seg(add(HUB, mul(head1, w)), add(HUB, mul(R - 0.7, w))), { tone: state.nib > 0 ? "lit" : "hi" }),
      D([at(add(HUB, mul(R - 0.7, w)))], { size: 0.7, tone: state.nib > 0 ? "hi" : "mid" }),
    ].join("");
    const away = dot(w, V) < 0;
    if (away) out.push(outer());
    // Hub parts.
    const z0 = C.DOME.z - 7.2;
    const parts = [];
    parts.push([depth([HUB[0], HUB[1], z0]), S(k.cylinder(HUB[0], HUB[1], 4.2, z0, 1.8, P, 28, 0.3), { tone: "mid" }) + L(k.lineOnTop([HUB[0] + horiz[0] * 1.2, HUB[1] + horiz[1] * 1.2], [HUB[0] + horiz[0] * 3.8, HUB[1] + horiz[1] * 3.8], z0 + 1.8, P), { tone: "hi" })]);
    for (const side of [-1, 1]) {
      const c = add(HUB, mul(side * 3.3, axis));
      const F = G.frameOf([c[0], c[1], z0 + 1.8], axis, horiz, [0, 0, 1]);
      parts.push([depth(add(c, [0, 0, -2])), S(G.prismOf(F, [[-1.6, 0], [1.6, 0], [1.6, 7.2], [-1.6, 7.2]], -0.6, 0.6, P), { tone: "mid" })]);
    }
    parts.push([depth(HUB) + 0.01, rod(add(HUB, mul(-4.6, axis)), add(HUB, mul(4.6, axis)), 1.05, { tone: "mid" }, 12)]);
    // The counterweight behind the pivot, the inner arm, and the sleeve that carries the observation ball.
    parts.push([depth(add(HUB, mul(-5, w))), rod(HUB, add(HUB, mul(-5.2, w)), 0.8, { tone: "mid" }) + rod(add(HUB, mul(-5.2, w)), add(HUB, mul(-7.6, w)), 2.6, { tone: "mid" }, 20)]);
    parts.push([depth(add(HUB, mul(B / 2, w))), rod(HUB, add(HUB, mul(B, w)), 0.8, { tone: "mid" })]);
    if (s > 0.05) parts.push([depth(obs) + 0.02, rod(add(obs, mul(-0.9, w)), add(obs, mul(0.9, w)), 1.5, { tone: "hi" }, 16)]);
    parts.sort((a, b) => a[0] - b[0]);
    out.push(parts.map(([, svg]) => svg).join(""));
    // The lens: the part of the incoming window the observation window still sees.
    out.push(`<path d="${lens.hull}" style="fill:var(--anatomy-mid);opacity:.3"/>`);
    const rim = halves(lens.rim, depth(add(HUB, mul(s / 2, w))));
    out.push(L(rim.back, { tone: "lo" }), L(rim.front, { tone: "hi" }));
    out.push(L(inRings.map((ring) => ring.front).join("") + obsRing.front, { tone: "lo" }));
    out.push(L(G.sphereOf(HUB, B, P, { steps: 48 }).outline, { tone: "mid" }));
    if (s > 0.05) out.push(L(G.sphereOf(obs, B, P, { steps: 48 }).outline, { tone: "mid" }));
    if (!away) out.push(outer());
    return out.join("");
  }

  // The Kelvin frame. Each crosshead lifts its pulleys; the cord's free end rises by twice the
  // sum of all pulley lifts, so it rises GAIN per unit of nᵀKn.
  const liftOf = (head, state) => {
    const value = state.terms[head.term];
    return (C.GAIN * value) / (2 * head.pulleys.length);
  };
  const lifts = (state) => C.MOVING.map((_, i) => liftOf(C.HEADS.find((head) => head.pulleys.includes(i)), state));
  const outputOf = (state) => 2 * lifts(state).reduce((sum, h) => sum + h, 0);
  const valueOf = (state) => outputOf(state) / C.GAIN;
  const zMoving = (state, i) => C.FRAME.zM + lifts(state)[i];
  const arc = (c, r, a0, a1, steps = 10) => Array.from({ length: steps + 1 }, (_, i) => { const a = a0 + ((a1 - a0) * i) / steps; return [c[0] + r * Math.cos(a), c[1], c[2] + r * Math.sin(a)]; });
  function cord(state) {
    const { y, r, zF } = C.FRAME;
    const points = [[C.FIXED[0] - r, y, C.FRAME.zM + 4.6]];
    for (let i = 0; i < 6; i++) {
      points.push(...arc([C.FIXED[i], y, zF], r, Math.PI, 2 * Math.PI));
      if (i < 5) points.push(...arc([C.MOVING[i], y, zMoving(state, i)], r, Math.PI, 0));
    }
    points.push(...arc([C.DRUM.x, y, C.DRUM.z], C.DRUM.r, Math.PI, 0, 24));
    points.push([C.DRUM.x + C.DRUM.r, y, hookOf(state) + 1.6]);
    return L(poly(points), { tone: "hi" });
  }
  const hookOf = (state) => C.SPRING.rest + outputOf(state);
  function heads(state) {
    const { y, r } = C.FRAME;
    const out = [];
    for (const head of C.HEADS) {
      const z = C.FRAME.zM + liftOf(head, state);
      const xs = head.pulleys.map((i) => C.MOVING[i]);
      const x0 = Math.min(...xs) - 7, x1 = Math.max(...xs) + 7;
      // Pulleys with their groove ring and hub.
      for (const x of xs) {
        const F = G.frameOf([x, y, z], [0, 1, 0], [1, 0, 0], [0, 0, 1]);
        out.push(S(G.disc(-1.4, 1.4, r + 0.6, F, P, { steps: 32 }), { tone: "hi" }));
        out.push(`<path class="iso-top" d="${G.circleOf(F, 1.4, r + 0.6, P, 32)}"/>`);
        out.push(L(G.circleOf(F, 1.45, r - 1.2, P, 28), { tone: "lo" }));
        out.push(L(G.spokesOf(F, 1.45, 2.2, r - 1.2, 4, P, { phase: (z - C.FRAME.zM) / r }), { tone: "lo" }));
        out.push(S(G.disc(1.4, 2.2, 1.5, F, P, { steps: 14 }), { tone: "mid" }));
      }
      // The block: a bar over the pulleys with a cheek down to each axle on the front.
      const barZ = z + r + 2;
      out.push(S(k.slabOf({ x: x0, y: y - 5.2, w: x1 - x0, d: 7.8, r: 0.8 }, barZ, 2.6, P, 2, 0.3), { tone: "mid" }));
      for (const x of xs) out.push(S(k.slabOf({ x: x - 1.4, y: y + 2.4, w: 2.8, d: 1.2, r: 0.3 }, z - 0.4, barZ - z + 0.4, P, 2), { tone: "mid" }));
      out.push(D(xs.map((x) => at([x, y + 3.6, z])), { size: 0.6, tone: "hi" }));
      // Bushings on the two guide rods behind.
      for (const x of [x0 + 1.2, x1 - 1.2]) out.push(S(k.cylinder(x, y - 4.2, 1.6, barZ - 1.6, 5.8, P, 16), { tone: "mid" }));
      // The nut on the lead screw.
      out.push(S(k.cylinder(head.x, y - 1.2, 2.2, barZ + 2.6, 2.4, P, 6), { tone: "hi" }));
    }
    return out.join("");
  }
  // Lead screws from the motors down to each block; they turn as the block moves.
  function screws(state) {
    const { y } = C.FRAME, out = [];
    for (const head of C.HEADS) {
      const top = C.FRAME.beam - 9;
      const bottom = C.FRAME.zM + liftOf(head, state) + C.FRAME.r + 2 + 5;
      out.push(S(k.cylinder(head.x, y - 1.2, 0.95, bottom, top - bottom, P, 12), { tone: "mid", crease: "none" }));
      const threads = [];
      const phase = (liftOf(head, state) * 0.9) % 1.6;
      for (let z = bottom + 0.8 + ((phase + 1.6) % 1.6); z < top - 0.6; z += 1.6) threads.push(k.sideArc(head.x, y - 1.2, 0.95, z, P, 8));
      out.push(L(threads.join(""), { tone: "lo" }));
    }
    return out.join("");
  }
  // The drum turns with the cord; the needle reads its turn, through the 50:1 train on the fine range.
  function needle(state) {
    const { x, z } = C.DRUM;
    const y = C.FRAME.y + 5.4;
    const turn = outputOf(state) / C.DRUM.r;
    const fine = state.range > 0.5;
    const angle = Math.max(-2.62, Math.min(2.62, turn * (fine ? C.FINE : 1)));
    const length = C.DIAL.r - 2.6;
    const tip = [x + length * Math.sin(angle), y, z + length * Math.cos(angle)];
    const tail = [x - 3 * Math.sin(angle), y, z - 3 * Math.cos(angle)];
    return [
      L(poly([tail, tip]), { tone: "lit" }),
      D([at(tail)], { size: 0.9, tone: "hi" }),
      S(G.disc(0, 0.9, 1.6, G.frameOf([x, y - 0.2, z], [0, 1, 0], [1, 0, 0], [0, 0, 1]), P, { steps: 16 }), { tone: "hi" }),
    ].join("");
  }
  // The tension spring: a hook ring where the cord ends, a coil down to the eye on the bench.
  function spring(state) {
    const x = C.DRUM.x + C.DRUM.r, y = C.FRAME.y, top = hookOf(state);
    const { r, turns, foot } = C.SPRING;
    const eye = foot + 1.6;
    const z0 = eye + 2.6, z1 = top - 2.6;
    const back = [], front = [];
    let run = [], near = null;
    const count = Math.round(turns * 18);
    for (let i = 0; i <= count; i++) {
      const a = (i / count) * turns * TAU;
      const p = [x + r * Math.cos(a), y + r * Math.sin(a), z0 + ((z1 - z0) * i) / count];
      const facing = Math.cos(a) * V[0] + Math.sin(a) * V[1] > 0;
      if (near === null) near = facing;
      run.push(at(p));
      if (facing !== near) { (near ? front : back).push(k.pathOf(run)); run = [at(p)]; near = facing; }
    }
    if (run.length > 1) (near ? front : back).push(k.pathOf(run));
    const ring = (z) => L(G.circleOf(G.frameOf([x, y, z], [0, 1, 0], [1, 0, 0], [0, 0, 1]), 0, 1.6, P, 16), { tone: "hi" });
    // Integer turns: the coil starts and ends on +x; short legs reach the eye and the hook.
    return [
      L(back.join(""), { tone: "lo" }),
      L(poly([[x + r, y, z0], [x, y, eye + 1.6]]) + poly([[x + r, y, z1], [x, y, top - 1.6]]), { tone: "hi" }),
      L(front.join(""), { tone: "hi" }),
      ring(top),
    ].join("");
  }
  // A clutch lever on a motor: down engages the drive, up lets the block fall back to rest.
  function clutch(index, f) {
    const head = C.HEADS[index];
    const pivot = [head.x + 4.2, C.FRAME.y + 4.4, C.FRAME.beam - 5];
    const a = -0.5 + f * 1.4;
    const tip = [pivot[0] + 5 * Math.cos(a), pivot[1], pivot[2] + 5 * Math.sin(a)];
    return [
      rod(pivot, tip, 0.55, { tone: "mid" }, 10),
      S(G.sphereOf(tip, 1.25, P, { steps: 16 }), { tone: "hi" }),
      S(G.disc(0, 0.8, 1.2, G.frameOf(pivot, [0, 1, 0], [1, 0, 0], [0, 0, 1]), P, { steps: 12 }), { tone: "mid" }),
    ].join("");
  }
  function rangeLever(f) {
    // On the bezel's upper right: up for the coarse scale, swung out for the fine.
    const pivot = [C.DRUM.x + (C.DIAL.r - 1.2) * 0.72, C.FRAME.y + 6, C.DRUM.z + (C.DIAL.r - 1.2) * 0.72];
    const a = Math.PI / 2 - 0.15 - f * 0.9;
    const tip = [pivot[0] + 5.4 * Math.cos(a), pivot[1], pivot[2] + 5.4 * Math.sin(a)];
    return [rod(pivot, tip, 0.5, { tone: "mid" }, 10), S(G.sphereOf(tip, 1.1, P, { steps: 14 }), { tone: "hi" }), D([at(pivot)], { size: 0.7, tone: "hi" })].join("");
  }
  // The selector on the bench: five pips for all five terms, two for the quantum legs alone.
  function selector(f) {
    const [x, y] = C.SELECTOR;
    const z = 2.2;
    const a = (-150 + f * 120) * RAD;
    return [
      S(k.cylinder(x, y, 4.2, z, 3.6, P, 28, 0.4), { tone: "hi" }),
      L(k.knurl(x, y, 4.2, z, z + 3.6, 28, P), { tone: "lo" }),
      L(k.lineOnTop([x + Math.cos(a) * 1.2, y + Math.sin(a) * 1.2], [x + Math.cos(a) * 3.6, y + Math.sin(a) * 3.6], z + 3.65, P), { tone: "lit" }),
    ].join("");
  }
  return { arm, stamps, cord, heads, screws, needle, spring, clutch, rangeLever, selector, valueOf };
}

const LIVE = makeLive(k, G, P, C, M);

// --- states -------------------------------------------------------------------------------

const AXES = { e1: { el: 0, az: 0 }, e2: { el: Math.PI / 2, az: 0 }, e3: { el: 0, az: Math.PI / 2 } };
const allStamped = (mode) => Int8Array.from(M.stamps(), ({ n }) => M.verdict(mode, n));
// The dial reads what the five terms add to; it must be the model's sum on every direction.
for (const mode of M.MODES) for (const stamp of M.stamps()) {
  const value = LIVE.valueOf({ terms: M.terms(mode, stamp.n) });
  const [lo, hi] = M.enclosure(mode, stamp.n);
  const centre = mode === "five" ? (lo + hi) / 2 - (M.QC[0] + M.QC[1]) / 2 + (M.HALF_S[0] + M.HALF_S[1]) / 2 : (lo + hi) / 2;
  if (Math.abs(value - centre) > 1e-12) throw new Error(`dial off the model: ${mode} ${stamp.n} dial ${value} model ${centre}`);
}
function restingState() {
  return { mode: "five", el: AXES.e2.el, az: AXES.e2.az, s: 0.55 * C.SLIDE, phi: Math.acos(-0.1), swing: 1, engaged: 1, nib: 1, range: 0, clutch: [0, 0], selector: 0, terms: M.terms("five", M.directionOf(AXES.e2.el, AXES.e2.az)), stamps: allStamped("five") };
}

// --- static art ----------------------------------------------------------------------------

const at = (point) => k.iso(point, P);
const S = (paths, style) => k.solidSvg(paths, style);
const L = (d, style) => k.lineSvg(d, style);
const D = (points, style) => k.dotsSvg(points, style);
const RAD = Math.PI / 180;
const [DX, DY] = C.DOME.c;

function base() {
  const { PLATE, PLATE_H, FOOT_H } = C;
  const out = [`<path class="iso-halo" d="${k.haloOf(PLATE, -PLATE_H - FOOT_H, PLATE_H, P)}"/>`];
  const feet = k.corners(PLATE, 24).sort((a, b) => k.depthOf([...a, 0], P) - k.depthOf([...b, 0], P));
  for (const [x, y] of feet) {
    out.push(S(k.cylinder(x, y, 8, -PLATE_H - FOOT_H, 1.6, P, 28), { tone: "lo" }));
    out.push(S(k.cylinder(x, y, 6, -PLATE_H - FOOT_H + 1.6, FOOT_H - 1.6, P, 28), { tone: "mid" }));
  }
  out.push(S(k.slabOf(PLATE, -PLATE_H, PLATE_H, P, 8, 1.6), { tone: "mid", inner: L(k.sideSeam(PLATE, -4, P, 8), { tone: "faint" }) }));
  out.push(L(k.planOutline(k.insetPlan(PLATE, 5), 0, P), { tone: "lo" }));
  const screws = k.corners(PLATE, 11);
  out.push(L(screws.map(([x, y]) => k.ring(x, y, 2.2, 0, P, 16)).join(""), { tone: "lo" }));
  out.push(D(screws.map(([x, y]) => at([x, y, 0])), { size: 0.5 }));
  return out.join("");
}

// The label plate and the selector's dial on the bench in front of the frame.
function benchFront() {
  const out = [];
  const label = C.LABEL;
  out.push(S(k.slabOf(label, 0, 0.8, P, 3, 0.3), { tone: "lo", crease: "none" }));
  for (const [index, y] of [label.y + 4.2, label.y + 7.4, label.y + 10.2].entries()) out.push(L(k.lineOnTop([label.x + 5, y], [label.x + [38, 30, 22][index], y], 0.8, P), { tone: "faint", free: true }));
  out.push(D([at([label.x + 2, label.y + 2.4, 0.8]), at([label.x + label.w - 2, label.y + label.d - 2.4, 0.8])], { size: 0.4 }));
  const [x, y] = C.SELECTOR;
  out.push(S(k.cylinder(x, y, 9.5, 0, 2.2, P, 40, 0.4), { tone: "mid" }));
  out.push(L(k.ring(x, y, 7.6, 2.2, P, 40), { tone: "lo" }));
  // Detents: five pips at one stop, two at the other.
  const pips = (angle, count) => Array.from({ length: count }, (_, i) => {
    const a = (angle + (i - (count - 1) / 2) * 9) * RAD;
    return at([x + Math.cos(a) * 8.6, y + Math.sin(a) * 8.6, 2.2]);
  });
  out.push(D(pips(-150, 5), { size: 0.55, tone: "hi" }), D(pips(-30, 2), { size: 0.55, tone: "hi" }));
  return out.join("");
}

// The dome stand: a turned base on the bench, three legs, a ring, the post to the hub.
function domeStand() {
  const out = [];
  const z = C.DOME.z;
  out.push(`<path class="iso-halo" d="${k.haloOf({ x: DX - C.BASE.r, y: DY - C.BASE.r, w: 2 * C.BASE.r, d: 2 * C.BASE.r, r: C.BASE.r }, 0, 4, P)}" style="filter:blur(6px)"/>`);
  out.push(S(k.cylinder(DX, DY, C.BASE.r, 0, C.BASE.h, P, 96, 0.6), { tone: "mid" }));
  out.push(L(k.ring(DX, DY, C.BASE.r - 3.5, C.BASE.h, P, 96), { tone: "lo" }));
  const legs = C.LEGS.map((h) => [DX + C.LEG_R * Math.cos(h * RAD), DY + C.LEG_R * Math.sin(h * RAD)]).sort((a, b) => k.depthOf([...a, 0], P) - k.depthOf([...b, 0], P));
  for (const [x, y] of legs) {
    out.push(S(k.cylinder(x, y, 3.6, C.BASE.h, 1.4, P, 20, 0.3), { tone: "mid" }));
    out.push(S(k.cylinder(x, y, 1.7, C.BASE.h + 1.4, z - C.RING.h - C.BASE.h - 1.4, P, 14), { tone: "mid", crease: "none" }));
  }
  // The post's boss and column up to the turntable.
  out.push(S(k.cylinder(DX, DY, 7, C.BASE.h, 2.6, P, 32, 0.4), { tone: "mid" }));
  out.push(L(k.ring(DX, DY, 5, C.BASE.h + 2.6, P, 28), { tone: "lo" }));
  out.push(D([0, 120, 240].map((a) => at([DX + 5.8 * Math.cos(a * RAD), DY + 5.8 * Math.sin(a * RAD), C.BASE.h + 2.6])), { size: 0.4 }));
  out.push(S(k.cylinder(DX, DY, 2.3, C.BASE.h + 2.6, z - 7.2 - C.BASE.h - 2.6, P, 16), { tone: "mid", crease: "none" }));
  out.push(S(k.cylinder(DX, DY, 3.1, z - 10.4, 3.2, P, 20, 0.3), { tone: "mid" }));
  return out.join("");
}
// The ring the glass sits on, with pins on ±e1 and ±e3, and the glass's back surface.
function domeRing() {
  const out = [];
  const z = C.DOME.z;
  const F = G.frameOf([DX, DY, z - C.RING.h], [0, 0, 1], [1, 0, 0], [0, 1, 0]);
  out.push(S(G.ringBand(0, C.RING.h, C.RING.rIn, C.RING.rOut, F, P), { tone: "mid" }));
  // The glass lip resting on the ring.
  out.push(S(G.ringBand(C.RING.h, C.RING.h + 1.5, C.DOME.R - 0.6, C.DOME.R + 1.6, F, P), { tone: "lo" }));
  return out.join("");
}
// Pins outside the glass on ±e1, ±e3: the far ones are seen through it, the near ones in front.
function axisPins(side) {
  const z = C.DOME.z;
  const out = [];
  const ref = k.depthOf([DX, DY, z], P);
  const pins = [[C.E1, 1], [C.E1 - 90, 1], [C.E1 + 180, 0], [C.E1 + 90, 0]]
    .map(([h, plus]) => [DX + 61.7 * Math.cos(h * RAD), DY + 61.7 * Math.sin(h * RAD), plus])
    .filter(([x, y]) => (k.depthOf([x, y, z], P) > ref) === (side === "front"))
    .sort((a, b) => k.depthOf([a[0], a[1], 0], P) - k.depthOf([b[0], b[1], 0], P));
  for (const [x, y, plus] of pins) {
    out.push(S(k.cylinder(x, y, plus ? 1.2 : 0.95, z, plus ? 3.4 : 2, P, 14), { tone: plus ? "hi" : "mid" }));
  }
  return out.join("");
}
// The glass: a back surface, the rim seen through it, the outline and two reflections in front.
function glassBack() {
  const R = C.DOME.R, z = C.DOME.z;
  const pts = [];
  for (let i = 0; i < 96; i++) {
    const a = (i / 96) * 2 * Math.PI;
    pts.push(at([DX + R * Math.cos(a), DY + R * Math.sin(a), z]));
  }
  // Upper half of the limb: points of the limb circle above the rim's plane.
  const cA = Math.cos(P.azimuth * RAD), sA = Math.sin(P.azimuth * RAD), cE = Math.cos(P.elevation * RAD), sE = Math.sin(P.elevation * RAD);
  const V = [cA * cE, sA * cE, sE];
  const F = G.frameAlong([DX, DY, z], V);
  for (let i = 0; i < 128; i++) {
    const p = G.pointOf(F, 0, R, (i / 128) * 2 * Math.PI);
    if (p[2] >= z) pts.push(at(p));
  }
  const hull = k.pathOf(G.hullOf(pts), true);
  return `<path d="${hull}" style="fill:var(--anatomy-face);opacity:.5"/>`;
}
function rimLoop() {
  const R = C.DOME.R + 1.6, z = C.DOME.z + 1.5;
  return Array.from({ length: 96 }, (_, i) => { const a = (i / 96) * 2 * Math.PI; return [DX + R * Math.cos(a), DY + R * Math.sin(a), z]; });
}
function glassFront() {
  const R = C.DOME.R, z = C.DOME.z;
  const cA = Math.cos(P.azimuth * RAD), sA = Math.sin(P.azimuth * RAD), cE = Math.cos(P.elevation * RAD), sE = Math.sin(P.elevation * RAD);
  const V = [cA * cE, sA * cE, sE];
  const F = G.frameAlong([DX, DY, z], V);
  // The silhouette: the limb over the top closed by the front of the rim.
  const pts = [];
  for (let i = 0; i < 96; i++) { const a = (i / 96) * 2 * Math.PI; pts.push(at([DX + R * Math.cos(a), DY + R * Math.sin(a), z])); }
  for (let i = 0; i < 160; i++) { const p = G.pointOf(F, 0, R, (i / 160) * 2 * Math.PI); if (p[2] >= z) pts.push(at(p)); }
  const out = [L(k.pathOf(G.hullOf(pts), true), { tone: "mid" })];
  // Two reflections of a window on the upper left, as arcs of meridians.
  const refl = (h, e0, e1) => Array.from({ length: 16 }, (_, i) => {
    const e = (e0 + ((e1 - e0) * i) / 15) * RAD;
    return [DX + (R - 0.3) * Math.cos(e) * Math.cos(h * RAD), DY + (R - 0.3) * Math.cos(e) * Math.sin(h * RAD), z + (R - 0.3) * Math.sin(e)];
  });
  out.push(L(k.pathOf(refl(118, 30, 64).map(at)) + k.pathOf(refl(112, 36, 58).map(at)), { tone: "faint", free: true }));
  return out.join("");
}
// The knob on top of the glass marks e2.
function knob() {
  const z = C.DOME.z + C.DOME.R;
  return [
    S(k.cylinder(DX, DY, 3.6, z - 0.4, 1.6, P, 28, 0.3), { tone: "mid" }),
    S(k.cylinder(DX, DY, 1.4, z + 1.2, 2, P, 14), { tone: "mid" }),
    S(G.sphereOf([DX, DY, z + 5], 2.6, P, { steps: 24 }), { tone: "hi" }),
  ].join("");
}

// The frame: two posts at the back, a lower rail with the fixed pulleys, a beam with the motors.
function frameBack() {
  const { y, postY, beam, left, zF, r } = C.FRAME;
  const out = [];
  for (const x of [left, C.RIGHT]) {
    out.push(S(k.slabOf({ x: x - 3.5, y: postY - 3.5, w: 7, d: 7, r: 1 }, 0, beam + 4, P, 2, 0.4), { tone: "mid" }));
    // The foot reaches back from the post's front face, clear of the spring in front.
    out.push(S(k.slabOf({ x: x - 5.2, y: postY - 8, w: 10.4, d: 11.5, r: 1.2 }, 0, 2.2, P, 2, 0.4), { tone: "mid" }));
    out.push(D([[-3.6, -6.4], [3.6, 1.6]].map(([dx, dy]) => at([x + dx, postY + dy, 2.2])), { size: 0.4 }));
  }
  // Lower rail and fixed pulley brackets.
  out.push(S(k.slabOf({ x: left - 3.5, y: postY - 3, w: C.RIGHT - left + 7, d: y - postY + 6, r: 0.8 }, zF - r - 5.6, 3.4, P, 2, 0.4), { tone: "mid" }));
  out.push(D([left + 10, (left + C.RIGHT) / 2, C.RIGHT - 10].map((x) => at([x, y + 3, zF - r - 2.2])), { size: 0.4 }));
  // The cord's anchor: a bracket from the left post with an eye.
  const zA = C.FRAME.zM + 7.2;
  out.push(S(k.slabOf({ x: C.FIXED[0] - C.FRAME.r - 0.5, y: y - 0.5, w: 1, d: 1, r: 0.2 }, C.FRAME.zM + 6.4, zA - C.FRAME.zM - 6.4, P, 2), { tone: "mid" }));
  out.push(S(k.slabOf({ x: left + 3.5, y: postY + 3.5, w: 2.6, d: y - postY - 5.1, r: 0.3 }, zA, 2.4, P, 2), { tone: "mid" }));
  out.push(S(k.slabOf({ x: left + 3.5, y: y - 1.6, w: C.FIXED[0] - C.FRAME.r - left - 2.5, d: 3.2, r: 0.4 }, zA, 2.4, P, 2), { tone: "mid" }));
  out.push(L(G.circleOf(G.frameOf([C.FIXED[0] - C.FRAME.r, y + 0.6, C.FRAME.zM + 5.8], [0, 1, 0], [1, 0, 0], [0, 0, 1]), 0, 1.2, P, 14), { tone: "hi" }));
  return out.join("");
}
function fixedPulleys() {
  const { y, zF, r } = C.FRAME;
  const out = [];
  for (const x of C.FIXED) {
    for (const dy of [-2.4, 2.4]) out.push(S(k.slabOf({ x: x - 1.6, y: y + dy - 0.6, w: 3.2, d: 1.2, r: 0.3 }, zF - r - 2.2, r + 2.2, P, 2), { tone: "mid" }));
    const F = G.frameOf([x, y, zF], [0, 1, 0], [1, 0, 0], [0, 0, 1]);
    out.push(S(G.disc(-1.4, 1.4, r + 0.6, F, P, { steps: 32 }), { tone: "mid" }));
    out.push(`<path class="iso-top" d="${G.circleOf(F, 1.4, r + 0.6, P, 32)}"/>`);
    out.push(L(G.circleOf(F, 1.45, r - 1.2, P, 28), { tone: "lo" }));
    out.push(S(G.disc(1.4, 2.2, 1.5, F, P, { steps: 14 }), { tone: "mid" }));
  }
  return out.join("");
}
function frameBeam() {
  const { y, postY, beam, left } = C.FRAME;
  const out = [];
  out.push(S(k.slabOf({ x: left - 3.5, y: postY - 3.5, w: C.RIGHT - left + 7, d: y - postY + 8, r: 1 }, beam, 4, P, 2, 0.5), { tone: "mid", inner: L(k.sideSeam({ x: left - 3.5, y: postY - 3.5, w: C.RIGHT - left + 7, d: y - postY + 8, r: 1 }, beam + 2, P, 2), { tone: "faint" }) }));
  out.push(D([left, C.RIGHT].map((x) => at([x, y + 4.5, beam + 4])), { size: 0.45 }));
  // Guide rods behind each block, hanging from the beam to a stop.
  for (const head of C.HEADS) {
    const xs = head.pulleys.map((i) => C.MOVING[i]);
    for (const x of [Math.min(...xs) - 5.8, Math.max(...xs) + 5.8]) {
      out.push(S(k.cylinder(x, y - 4.2, 0.85, 44, beam - 44, P, 10), { tone: "mid", crease: "none" }));
      out.push(S(k.cylinder(x, y - 4.2, 1.8, 43, 1.2, P, 14), { tone: "mid" }));
    }
  }
  return out.join("");
}
function motors() {
  const { y, beam } = C.FRAME;
  const out = [];
  for (const head of C.HEADS) {
    const box = { x: head.x - 4.5, y: y - 5.5, w: 9, d: 9, r: 1 };
    out.push(S(k.slabOf(box, beam - 9, 9, P, 2, 0.5), { tone: "mid", inner: L(k.sideSeam(box, beam - 4.5, P, 2), { tone: "faint" }) }));
    out.push(D([at([box.x + 1.6, box.y + box.d, beam - 1.6]), at([box.x + box.w - 1.6, box.y + box.d, beam - 1.6])], { size: 0.4 }));
    out.push(S(k.cylinder(head.x, y - 1.2, 2.4, beam - 10.4, 1.4, P, 16), { tone: "mid" }));
  }
  return out.join("");
}
// The spring's foot on the bench: a small block with an eye.
function springFoot() {
  const x = C.DRUM.x + C.DRUM.r, y = C.FRAME.y;
  const { foot } = C.SPRING;
  return [
    S(k.slabOf({ x: x - 3, y: y - 3, w: 6.6, d: 6.6, r: 0.9 }, 0, foot, P, 2, 0.4), { tone: "mid" }),
    D([at([x - 1.9, y + 2.1, foot]), at([x + 2.3, y - 1.9, foot])], { size: 0.4 }),
    L(G.circleOf(G.frameOf([x, y, foot + 1.6], [0, 1, 0], [1, 0, 0], [0, 0, 1]), 0, 1.6, P, 16), { tone: "hi" }),
  ].join("");
}
// The dial over the drum, and its post bracket.
function dialFace() {
  const { x, z } = C.DRUM;
  const y = C.FRAME.y;
  const out = [];
  out.push(S(k.slabOf({ x: x - 2.4, y: C.FRAME.postY + 3.5, w: 4.8, d: y - C.FRAME.postY - 3.5, r: 0.4 }, z - 2.4, 4.8, P, 2), { tone: "mid" }));
  const F = G.frameOf([x, y, z], [0, 1, 0], [1, 0, 0], [0, 0, 1]);
  out.push(S(G.disc(-1.6, 1.6, C.DRUM.r, F, P, { steps: 48 }), { tone: "mid" }));
  out.push(S(G.disc(2.4, 5, C.DIAL.r, F, P, { steps: 64 }), { tone: "mid" }));
  const face = G.frameOf([x, y + 5.05, z], [0, 1, 0], [1, 0, 0], [0, 0, 1]);
  out.push(`<path class="iso-fill" d="${G.circleOf(face, 0, C.DIAL.r - 1.2, P, 64)}" style="fill:var(--anatomy-face)"/>`);
  out.push(L(G.circleOf(face, 0, C.DIAL.r - 1.2, P, 64), { tone: "lo" }));
  // Ticks from −2.5 to 2.5 (×10⁻²⁰ on the coarse range, ×2·10⁻²² on the fine), zero at the top.
  const tick = (value, r0, r1) => {
    const a = (value / 2.5) * 0.75 * Math.PI;
    return k.pathOf([[x + r0 * Math.sin(a), y + 5.1, z + r0 * Math.cos(a)], [x + r1 * Math.sin(a), y + 5.1, z + r1 * Math.cos(a)]].map(at));
  };
  const minor = [], major = [];
  for (let i = -10; i <= 10; i++) (i % 2 === 0 ? major : minor).push(tick(i / 4, C.DIAL.r - (i % 2 === 0 ? 4.4 : 3.4), C.DIAL.r - 2.2));
  out.push(L(minor.join(""), { tone: "lo" }), L(major.join(""), { tone: "mid" }), L(tick(0, C.DIAL.r - 5.4, C.DIAL.r - 2.2), { tone: "hi" }));
  const arcOf = (from, to) => Array.from({ length: 33 }, (_, i) => {
    const a = (from + ((to - from) * i) / 32) * 0.75 * Math.PI / 2.5;
    return [x + (C.DIAL.r - 2.2) * Math.sin(a), y + 5.1, z + (C.DIAL.r - 2.2) * Math.cos(a)];
  });
  out.push(L(k.pathOf(arcOf(0, 2.5).map(at)), { tone: "hi" }), L(k.pathOf(arcOf(-2.5, 0).map(at)), { tone: "lo" }));
  out.push(D([[-1, 1], [1, 1], [-1, -1], [1, -1]].map(([dx, dz]) => at([x + dx * (C.DIAL.r - 2.2) * 0.72, y + 5.1, z + dz * (C.DIAL.r - 2.2) * 0.72])), { size: 0.35 }));
  return out.join("");
}
// The cable from the dial's contact to the stamp: it leaves the right post's back face, runs
// behind the frame and plugs into a socket on the rim of the dome's base.
function cable() {
  const y = C.FRAME.postY - 11;
  const x = DX + Math.sqrt(C.BASE.r ** 2 - (y - DY) ** 2);
  const out = [S(k.slabOf({ x: x - 0.2, y: y - 2.2, w: 4, d: 4.4, r: 0.6 }, 0, 3.2, P, 2, 0.3), { tone: "mid" })];
  out.push(k.wireSvg(at([C.RIGHT, C.FRAME.postY - 3.5, 8]), at([x + 3.8, y, 1.6]), { via: [at([C.RIGHT, y, 0.6]), at([x + 7, y, 0.6])], tone: "lo" }));
  return out.join("");
}

const part = (name, inner) => `<g data-part="${name}">${inner}</g>`;
const REST = restingState();
function body(state) {
  return [
    base(),
    part("cable", cable()),
    domeStand(),
    domeRing(),
    axisPins("back"),
    glassBack(),
    L(halvesOf(rimLoop()).back, { tone: "lo" }),
    part("stamps-back", `<g style="opacity:.45">${LIVE.stamps(state, "back")}</g>`),
    part("arm", LIVE.arm(state)),
    part("stamps-front", LIVE.stamps(state, "front")),
    glassFront(),
    axisPins("front"),
    knob(),
    // The frame.
    frameBack(),
    frameBeam(),
    fixedPulleys(),
    part("cord", LIVE.cord(state)),
    part("screws", LIVE.screws(state)),
    part("heads", LIVE.heads(state)),
    motors(),
    part("clutch-1", LIVE.clutch(1, state.clutch[0])),
    part("clutch-2", LIVE.clutch(2, state.clutch[1])),
    springFoot(),
    part("spring", LIVE.spring(state)),
    dialFace(),
    part("needle", LIVE.needle(state)),
    part("range", LIVE.rangeLever(state.range)),
    benchFront(),
    part("selector", LIVE.selector(state.selector)),
  ].join("");
}
function halvesOf(points) {
  const ref = k.depthOf([DX, DY, C.DOME.z], P);
  const back = [], front = [];
  let run = [points[0]], side = k.depthOf(points[0], P) < ref;
  for (const p of [...points.slice(1), points[0]]) {
    const now = k.depthOf(p, P) < ref;
    run.push(p);
    if (now !== side) { (side ? back : front).push(k.pathOf(run.map(at))); run = [p]; side = now; }
  }
  (side ? back : front).push(k.pathOf(run.map(at)));
  return { back: back.join(""), front: front.join("") };
}

const svg = k.figureSvg({
  width: WIDTH,
  height: HEIGHT,
  className: "cd-svg",
  label:
    "A glass dome over a pivoting arm, and beside it a frame of pulleys and one cord. Every direction of the external momentum is a point on the dome; the arm points the observation window along that direction and stamps the glass with the sign of the response curvature there: solid where it is certainly positive, faint where certainly negative, half where the enclosure touches zero. The cord runs over five pulleys, the five terms of the response, and its free end turns the dial: two pulleys for the quantum source legs, one for the reader contact, two for the field propagation legs. With all five, the stamps light a cap around the vertical axis e2 and leave the whole e1–e3 plane dark: two negative directions and one positive. With the quantum legs alone every stamp is dark.",
  body: body(REST),
});

const CSS = `
.iso-stage{outline:none;cursor:pointer;touch-action:pan-y}
.iso-stage:focus-visible{box-shadow:0 0 0 1px var(--anatomy-mid)}
@media (max-width:560px){.cd-svg.iso-svg{width:104%;max-width:none;margin:0 -2%}}
`;

const COPY = {
  en: {
    title: "Two minuses, one plus",
    hint: "Click: witnesses · ← →: axis",
    keys: ["Solid stamp: curvature certainly positive along that direction", "Faint stamp: certainly negative · half: enclosure touches zero", "Pulleys: quantum legs ×2 · reader contact · field legs ×2"],
    refs: ["Theorem 1.2", "§§7–11"],
    caption: [
      "A dome of directions: every point on it is a direction n, and the arm visits each one to stamp the sign of the response curvature there.",
      "The external momentum d = sn shifts the observation window along n; the complete response reads R(0) + a(n)|s| + s²·nᵀKn + o(s²). The two-ball intersection at the hub thins at once, so the |s| term (the cusp of the sharp window) is taken out first; the curvature K is what is left at second order. n and −n read the same, so the upper half holds every direction.",
      "Each stamp comes from the strict enclosure of nᵀKn: the field legs’ leading tensor diag(−1.3032, 2.1923, −1.6906)·10⁻²⁰ of (10.7), widened by the whole-ball remainder 2.07·10⁻²² and the quantum legs with contact, [−3.130, −2.672]·10⁻²². The cord adds the five terms on the dial.",
      "The whole e₁–e₃ plane comes out negative and e₂ positive, so the tensor’s inertia is (2, 1, 0): for the full tensor, mixed entries included, not just three axes. The leading tensor’s zero cone rises 37.6° above the plane toward e₁ and 41.3° toward e₃; the four half stamps sit where the enclosure cannot yet tell.",
      "Unhook the field legs and the contact, and leave only the quantum source legs, whose windows do not move: every direction reads negative, [−3.13, −2.67]·10⁻²² on the dial’s fine range.",
    ],
    aria: "Curvature dome: arrow keys point the arm at e1, e2, e3; click or Space switches between all five terms and the quantum legs alone",
    labels: { undecided: "undecided", quantum: "2 legs", axes: ["e₁", "e₂", "e₃"] },
  },
  zh: {
    title: "两负一正",
    hint: "点击：换证人 · ← →：轴",
    keys: ["实印：该方向曲率确定为正", "淡印：确定为负 · 半印：区间触及零", "滑轮：量子源腿 ×2 · 读出接触 · 场传播腿 ×2"],
    refs: ["定理 1.2", "§§7–11"],
    caption: [
      "一座方向罩：罩上每一点是一个方向 n，悬臂逐一走过，给那个方向的响应曲率盖上正负。",
      "外动量 d = sn 把观察窗沿 n 推开，完整响应读作 R(0) + a(n)|s| + s²·nᵀKn + o(s²)。罩心的两球交集一推就变薄，所以先扣掉 |s| 项（尖窗的尖点），曲率 K 是剩下的二阶系数。n 与 −n 读数相同，半球即全部方向。",
      "每枚印都按 nᵀKn 的严格区间盖下：场传播腿的主张量 (10.7) diag(−1.3032, 2.1923, −1.6906)·10⁻²⁰，加上整球余项 2.07·10⁻²²，再加量子源腿与接触 [−3.130, −2.672]·10⁻²²。绳子在表盘上把五项相加。",
      "整个 e₁–e₃ 平面为负、e₂ 为正，于是张量惯性是 (2, 1, 0)——这是含混合项在内的整个张量，不只三根轴。主张量的零锥在 e₁ 一侧离平面 37.6°，在 e₃ 一侧 41.3°；四枚半印落在区间还分不出正负的地方。",
      "把场传播腿与接触脱开，只留窗口不动的量子源两腿：每个方向都读负，表盘细档上是 [−3.13, −2.67]·10⁻²²。",
    ],
    aria: "曲率罩：方向键把臂指向 e₁、e₂、e₃；点击或空格在五项俱全与只留量子源腿之间切换",
    labels: { undecided: "未定", quantum: "两腿", axes: ["e₁", "e₂", "e₃"] },
  },
};

function readoutOf(labels, state, M) {
  const n = M.directionOf(state.el, state.az);
  const [lo, hi] = M.enclosure(state.mode, n);
  const axis = state.axis === undefined ? null : labels.axes[state.axis];
  // Elevation above the e1–e3 plane, then azimuth from e1 toward e3.
  const where = axis ?? `${Math.round((state.el * 180) / Math.PI)}°/${(((Math.round((state.az * 180) / Math.PI) % 360) + 360) % 360)}°`;
  const range = state.mode === "quantum" ? `[${(lo * 100).toFixed(3)}, ${(hi * 100).toFixed(3)}]·10⁻²²` : `[${lo.toFixed(4)}, ${hi.toFixed(4)}]·10⁻²⁰`;
  const verdict = lo > 0 ? " +" : hi < 0 ? " −" : ` · ${labels.undecided}`;
  return `${state.mode === "quantum" ? labels.quantum + " · " : ""}${where} · nᵀKn ${range}${verdict}`.replace(/-/g, "−");
}

const bodyOf = (lang) => {
  const copy = COPY[lang];
  return `<div data-figure="curvature-dome" data-labels='${JSON.stringify(copy.labels)}'>${k.plateHtml({
    fig: "Fig 1.2",
    title: copy.title,
    hint: copy.hint,
    readout: readoutOf(copy.labels, { ...REST, axis: 1 }, M),
    keys: [
      { mark: "lit", label: copy.keys[0] },
      { mark: "dim", label: copy.keys[1] },
      { mark: "raised", label: copy.keys[2] },
    ],
    caption: copy.caption,
    refs: copy.refs,
    body: `<div class="iso-stage" tabindex="0" role="slider" aria-label="${copy.aria}" aria-valuemin="0" aria-valuemax="2" aria-valuenow="1">${svg}</div>`,
  })}</div>`;
};

const strip = (file) => readFileSync(join(HERE, file), "utf8").replace(/^export /gm, "");
const kitSource = strip("../kit/iso-kit.mjs");
const latheSource = `const LATHE = (() => {\n${strip("../kit/lathe.mjs").replace(/^import .*$/gm, "")}\nreturn { disc, frameOf, frameAlong, sphereOf, prismOf, circleOf, spokesOf, hullOf };\n})();`;
const modelSource = `const MODEL = (() => {\n${strip("model.mjs")}\nreturn { directionOf, enclosure, verdict, terms, stamps, MODES };\n})();`;
const live = `
const P = ${JSON.stringify(P)};
const C = ${JSON.stringify(C)};
const kit = { iso, depthOf, pathOf, solidSvg, lineSvg, dotsSvg, segment, slabOf, cylinder, lineOnTop, knurl, sideArc, ring };
const LIVE = (${makeLive.toString()})(kit, LATHE, P, C, MODEL);
const readoutOf = ${readoutOf.toString()};
const root = document.querySelector('[data-figure="curvature-dome"]');
const stage = root.querySelector(".iso-stage");
const readout = root.querySelector("[data-readout]");
const labels = JSON.parse(root.dataset.labels);
const parts = {};
for (const node of stage.querySelectorAll("[data-part]")) parts[node.dataset.part] = node;
const still = matchMedia("(prefers-reduced-motion: reduce)");
const TAU = Math.PI * 2;
const AXES = [{ el: 0, az: 0 }, { el: Math.PI / 2, az: 0 }, { el: 0, az: Math.PI / 2 }];
const RING_RATE = 0.55; // rings per second while scanning
const CLIMB = 0.12; // a ring's climb to the next, in rings
const DEG10 = Math.PI / 18;
const ease = (f) => f * f * (3 - 2 * f);
const STAMPS = MODEL.stamps();
// Where the scan meets each stamp: ring j turns once from az0(j), then climbs to the next ring.
const az0 = (j) => TAU * j * (1 + CLIMB);
const TRIGGER = STAMPS.map(({ ring, az }) => (ring === 9 ? 9 * (1 + CLIMB) : ring * (1 + CLIMB) + ((((az - az0(ring)) % TAU) + TAU) % TAU) / TAU));
const ORDER = STAMPS.map((_, i) => i).sort((a, b) => TRIGGER[a] - TRIGGER[b]);
const SCAN_END = 9 * (1 + CLIMB);
function scanAt(u) {
  const j = Math.min(8, Math.floor(u / (1 + CLIMB)));
  const t = u - j * (1 + CLIMB);
  const az = az0(j) + TAU * Math.min(t, 1 + CLIMB);
  if (t <= 1) return { el: j * DEG10, az };
  const top = j === 8 ? Math.PI / 2 : (j + 1) * DEG10;
  return { el: j * DEG10 + (top - j * DEG10) * ease(Math.min(1, (t - 1) / CLIMB)), az };
}
const verdictHere = () => MODEL.verdict(state.mode, MODEL.directionOf(state.el, state.az));
let state = ${JSON.stringify({ ...REST, stamps: undefined, terms: undefined })};
state.stamps = Int8Array.from(STAMPS, ({ n }) => MODEL.verdict("five", n));
state.axis = 1;
let queue = [], task = null, touring = !still.matches, visible = false, frame = 0, last = 0, idle = 0, dirty = true;
// The tour: read the three axes, swap in the quantum legs alone and scan, read e2, swap back and scan.
const TOUR = [["dwell", 1, 3.2], ["go", 0], ["dwell", 0, 3.2], ["go", 2], ["dwell", 2, 3.2], ["alter"], ["go", "start"], ["scan"], ["go", 1], ["dwell", 1, 4], ["alter"], ["go", "start"], ["scan"], ["go", 1]];
let tourAt = 0;
function say() {
  const text = readoutOf(labels, state, MODEL);
  if (readout.textContent !== text) readout.textContent = text;
  stage.setAttribute("aria-valuetext", text);
  if (state.axis !== undefined) stage.setAttribute("aria-valuenow", String(state.axis));
}
function draw() {
  const n = MODEL.directionOf(state.el, state.az);
  // The field legs' block follows its clutch; the quantum legs never let go; the contact reads 0.
  const five = MODEL.terms("five", n), quantum = MODEL.terms("quantum", n);
  state.terms = { G: five.G * state.engaged + quantum.G * (1 - state.engaged), Q: five.Q, C: 0 };
  state.nib = verdictHere();
  const set = (name, html) => { parts[name].innerHTML = html; };
  set("arm", LIVE.arm(state));
  set("cord", LIVE.cord(state));
  set("screws", LIVE.screws(state));
  set("heads", LIVE.heads(state));
  set("spring", LIVE.spring(state));
  set("needle", LIVE.needle(state));
  set("range", LIVE.rangeLever(state.range));
  set("clutch-1", LIVE.clutch(1, state.clutch[0]));
  set("clutch-2", LIVE.clutch(2, state.clutch[1]));
  set("selector", LIVE.selector(state.selector));
  if (dirty) {
    set("stamps-back", '<g style="opacity:.45">' + LIVE.stamps(state, "back") + "</g>");
    set("stamps-front", LIVE.stamps(state, "front"));
    dirty = false;
  }
  say();
}
const stamp = (i) => { const v = MODEL.verdict(state.mode, STAMPS[i].n); if (state.stamps[i] !== v) { state.stamps[i] = v; dirty = true; } };
function targetOf(arg) {
  return arg === "start" ? { el: 0, az: 0 } : AXES[arg];
}
function begin(next) {
  const [kind, arg, time] = next;
  task = { kind, arg, time: time ?? 0, t: 0 };
  if (kind === "go") {
    const to = targetOf(arg);
    const from = { el: state.el, az: state.az };
    // At the zenith the heading is free: turn it to the target's before leaving.
    if (from.el > 1.55) from.az = to.az;
    let daz = (((to.az - from.az) % TAU) + TAU) % TAU;
    if (daz > Math.PI) daz -= TAU;
    if (to.el > 1.55) daz = 0;
    task.from = from;
    task.to = { el: to.el, az: from.az + daz };
    const angle = Math.hypot(to.el - from.el, daz * Math.cos((to.el + from.el) / 2));
    task.time = 0.5 + angle / 1.5;
    state.axis = undefined;
  } else if (kind === "dwell") {
    state.axis = arg;
  } else if (kind === "alter") {
    state.mode = state.mode === "five" ? "quantum" : "five";
  } else if (kind === "scan") {
    task.u = 0;
    task.next = 0;
    state.axis = undefined;
  }
}
function finishScan() {
  if (task && task.kind === "scan") while (task.next < ORDER.length) stamp(ORDER[task.next++]);
}
function nextTask() {
  if (queue.length) return queue.shift();
  if (!touring) return ["dwell", state.axis ?? 1, 1e9];
  return TOUR[tourAt++ % TOUR.length];
}
function follow(value, target, dt, tau) {
  return value + (target - value) * (1 - Math.exp(-dt / tau));
}
function step(dt) {
  // The selector, clutches, range lever and the field legs' block follow the mode.
  const five = state.mode === "five" ? 1 : 0;
  state.selector = follow(state.selector, 1 - five, dt, 0.12);
  state.clutch = [follow(state.clutch[0], 1 - five, dt, 0.1), follow(state.clutch[1], 1 - five, dt, 0.1)];
  state.engaged = follow(state.engaged, five, dt, 0.35);
  state.range = follow(state.range, 1 - five, dt, 0.15);
  // The observation window slides along n with the field legs; the quantum legs' windows stay put.
  state.swing = follow(state.swing ?? five, five, dt, 0.4);
  state.phi += dt * 1.7;
  state.s = state.swing * C.SLIDE * (0.5 - 0.5 * Math.cos(state.phi));
  if (!task) begin(nextTask());
  task.t += dt;
  if (task.kind === "go") {
    const f = ease(Math.min(1, task.t / task.time));
    state.el = task.from.el + (task.to.el - task.from.el) * f;
    state.az = task.from.az + (task.to.az - task.from.az) * f;
    if (f >= 1) task = null;
  } else if (task.kind === "dwell") {
    if (task.t >= task.time) task = null;
  } else if (task.kind === "alter") {
    if (task.t >= 0.6) task = null;
  } else if (task.kind === "scan") {
    task.u = Math.min(SCAN_END, task.u + dt * RING_RATE);
    const at = scanAt(task.u);
    state.el = at.el;
    state.az = at.az;
    while (task.next < ORDER.length && TRIGGER[ORDER[task.next]] <= task.u + 1e-9) stamp(ORDER[task.next++]);
    if (task.u >= SCAN_END) { state.az = state.az % TAU; task = null; }
  }
}
function tick(time) {
  const dt = last ? Math.min((time - last) / 1000, 1 / 30) : 1 / 60;
  last = time;
  step(dt);
  draw();
  frame = visible && !still.matches ? requestAnimationFrame(tick) : 0;
}
const run = () => { if (!frame && visible && !still.matches) { last = 0; frame = requestAnimationFrame(tick); } };
const hold = () => { touring = false; clearTimeout(idle); idle = setTimeout(() => { touring = !still.matches; if (task && task.time > 1e8) task = null; }, 9000); };
// Without motion every change lands at once: the whole dome restamped, the arm on its axis.
function instant() {
  while (queue.length || (task && task.time < 1e8)) {
    if (!task) begin(queue.shift());
    if (task.kind === "scan") { finishScan(); task = null; continue; }
    if (task.kind === "go") { state.el = task.to.el; state.az = task.to.az; task = null; continue; }
    if (task.kind === "dwell") { task.time = 1e9; break; }
    task = null;
  }
  const five = state.mode === "five" ? 1 : 0;
  state.selector = state.range = 1 - five;
  state.clutch = [1 - five, 1 - five];
  state.engaged = state.swing = five;
  state.s = five * C.SLIDE * 0.55;
  draw();
}
function alter() {
  hold();
  finishScan();
  queue = [["alter"], ["go", "start"], ["scan"], ["go", state.axis ?? 1], ["dwell", state.axis ?? 1, 1e9]];
  task = null;
  if (still.matches) instant();
  run();
}
function inspect(direction) {
  hold();
  finishScan();
  const axis = ((state.axis ?? 1) + direction + 3) % 3;
  queue = [["go", axis], ["dwell", axis, 1e9]];
  task = null;
  if (still.matches) instant();
  run();
}
stage.addEventListener("keydown", (event) => {
  if (event.key === "ArrowRight" || event.key === "ArrowDown") inspect(1);
  else if (event.key === "ArrowLeft" || event.key === "ArrowUp") inspect(-1);
  else if (event.key === " " || event.key === "Enter") alter();
  else return;
  event.preventDefault();
});
stage.addEventListener("click", alter);
new IntersectionObserver((entries) => { visible = entries[entries.length - 1].isIntersecting; if (visible) run(); }, { rootMargin: "120px 0px" }).observe(stage);
if (still.matches) task = { kind: "dwell", arg: 1, time: 1e9, t: 0 };
say();
`;

const script = `{\n${kitSource}\n${latheSource}\n${modelSource}\n${live}\n}`.replace(/<\/(script)/gi, "<\\/$1");
if (fragment) {
  const outDir = join(HERE, "../../src/generated");
  mkdirSync(outDir, { recursive: true });
  writeFileSync(join(outDir, "curvature-dome.json"), JSON.stringify({ html: { zh: bodyOf("zh"), en: bodyOf("en") }, css: CSS, script }));
  console.log("wrote src/generated/curvature-dome.json");
} else {
  mkdirSync(join(HERE, "out"), { recursive: true });
  const name = theme === "light" ? "curvature-dome-light.html" : "curvature-dome.html";
  const lang = process.argv.includes("--zh") ? "zh" : "en";
  writeFileSync(join(HERE, "out", name), k.pageHtml({ title: COPY[lang].title, theme, body: `<style>${CSS}</style>${bodyOf(lang)}`, script, width: 760 }));
  console.log("wrote out/" + name);
}
