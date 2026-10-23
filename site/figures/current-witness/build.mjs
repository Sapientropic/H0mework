// Fig: a three-pen chart recorder on which one current testifies three times (§1, Theorems 8.1–8.2).
//   bun build.mjs [--light]   → out/current-witness[-light].html (standalone, for checks)
//   bun build.mjs --fragment  → ../../src/generated/current-witness.json (for the site)
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

// World: x along the bench, y toward the viewer, z up. Every moving part is placed by C.
const C = {
  PLATE: { x: -152, y: -52, w: 352, d: 86, r: 8 },
  PLATE_H: 10,
  FOOT_H: 5,
  // The chart board; the paper runs right to left over its face.
  BOARD: { x: -124, y: -42, w: 130, d: 6, r: 1.2 },
  BOARD_H: 140,
  PAPER_Z: [16, 134],
  SPOOL: { r: 6, flange: 8.6, take: -133.6, supply: 15.6 },
  X_PEN: -10,
  GAIN: 8, // chart units per normalised reading ωJ/(sε)
  LANES: [112, 71, 24], // baselines: finite evolution, two legs, Kubo
  PAPER_V: 8, // chart units per unit of ωt
  RUN: 2 * Math.PI,
  GAP: 0.9,
  // Pen bars ride a column between the chart and the rack.
  Y_BAR: -29.4,
  COLUMN: [32, -33],
  // The rack: two back posts, three cantilevered shelves stepping back as they rise.
  POSTS: [[44, -40], [188, -40]],
  TIERS: [
    { z: 0, h: 3, plan: { x: 40, y: -44, w: 152, d: 74, r: 3 } },
    { z: 43.6, h: 2.4, plan: { x: 40, y: -44, w: 152, d: 64, r: 3 } },
    { z: 97.6, h: 2.4, plan: { x: 40, y: -44, w: 152, d: 56, r: 3 } },
  ],
  X_IN: 52,
  // Station 1: the window's two blocks as Bloch spheres, read by feelers through a beam.
  SPHERES: [{ block: 1, c: [98, -1, 121] }, { block: -1, c: [158, -1, 121] }],
  R_SPHERE: 15,
  ARROW: 10.5,
  FEELER: { dx: 8.5, rod: 27, foot: 4.4 },
  GUIDE_Z: 137.5,
  STAND: [136.5, -24],
  CONE: { x: 132, z: 126.4, R: 10 * (8 / 10.5), step: 10 },
  IDLER: { r: 2, z: 132 },
  STAND_TOP: 164,
  DIAL: [66, 0],
  // Two slide switches that follow the testimony: Q on the top shelf, the leg count in the middle.
  SWITCHES: [{ tier: 2, plan: { x: 170, y: -2, w: 18, d: 8, r: 1.5 }, marks: ["B", "T"] }, { tier: 1, plan: { x: 158, y: 8, w: 18, d: 8, r: 1.5 }, marks: ["2", "1"] }],
  // Station 2: the state derivative δu as two meshed gears, bra and ket, each read by a yoke.
  GEARS: { c: [[86, -2.5, 61], [114, -2.5, 61]], tip: 15, root: 13, teeth: 20, t: 3, pin: 8, stem: 19.5, guide: 72 },
  // Station 3: a disc-and-wheel integrator for the Kubo kernel.
  DISC: { c: [124, -6], r: 30, z: 6, h: 3 },
  WHEEL: { r: 6, travel: 14, pinion: 3.2 },
  YOKE: { c: [174, 10, 21.5], r: 14 },
};
C.Y_P = C.BOARD.y + C.BOARD.d + 0.4;
// Lane 2's baseline is where the yokes put the balance bar with both pins at the bottom.
C.LANES[1] = C.GEARS.c[0][2] - C.GEARS.pin + C.GEARS.stem;
C.WHEEL.axle = C.DISC.z + C.DISC.h + C.WHEEL.r;
// Disc rate so that the rack moves GAIN per unit reading: rack = pinion·ψ, ψ = (Ω·travel/2r)(1 − cos 2x).
C.OMEGA_DISC = (C.GAIN * 2 * C.WHEEL.r) / (C.WHEEL.pinion * C.WHEEL.travel);

// The frame: fit the width, then size the height to the drawing so the card has no dead band.
const FIT = [
  ...k.boxCorners(C.PLATE, -C.PLATE_H - C.FOOT_H, 0),
  [C.BOARD.x, C.BOARD.y, C.BOARD_H + 4],
  [C.SPOOL.take - 9, C.Y_P - 6, C.BOARD_H],
  [C.POSTS[1][0], C.POSTS[1][1], 150],
  [C.SPHERES[1].c[0] + 16, 10, 166],
  [C.YOKE.c[0] + 20, 30, 0],
];
const VIEW = { pad: 20, azimuth: 72, elevation: 30 };
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
  const TAU = Math.PI * 2;
  const loop = (c, u, v, r, n = 56) => Array.from({ length: n }, (_, i) => add(c, add(mul(r * Math.cos((i / n) * TAU), u), mul(r * Math.sin((i / n) * TAU), v))));
  // A closed 3D loop split into what lies behind and in front of a reference depth.
  function halves(points, ref) {
    const out = { back: [], front: [] };
    const n = points.length;
    let start = 0;
    while (start < n && depth(points[start]) < ref === depth(points[(start + n - 1) % n]) < ref) start++;
    if (start === n) {
      (depth(points[0]) < ref ? out.back : out.front).push(poly(points, true));
      return out;
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
  const rotX = (mu, [x, y, z]) => [x, y * Math.cos(mu) - z * Math.sin(mu), y * Math.sin(mu) + z * Math.cos(mu)];
  // Bloch coordinates (σx, σy, σz) to the sphere's frame: σz along +x, σx up, σy toward −y.
  const blochToWorld = (mu, [sx, sy, sz]) => rotX(mu, [sz, -sy, sx]);
  const rodFrame = (from, to) => G.frameAlong(from, [to[0] - from[0], to[1] - from[1], to[2] - from[2]]);
  const rod = (from, to, r, style) => {
    const length = Math.hypot(to[0] - from[0], to[1] - from[1], to[2] - from[2]);
    return length < 0.05 ? "" : S(G.disc(0, length, r, rodFrame(from, to), P, { steps: 14 }), style);
  };

  // The block's Bloch vector. Between runs the state is prepared again: it eases from where the
  // run ended back to the start (0, 0, 1) while the axis tilts to the next ε.
  function blochOf(state, index) {
    const { block } = C.SPHERES[index];
    if (!state.reset) return M.bloch(state.a, state.x, block);
    const from = M.bloch(state.reset.a, C.RUN, block), f = state.reset.f;
    const v = [from[0] * (1 - f), from[1] * (1 - f), from[2] * (1 - f) + f];
    const n = Math.hypot(...v) || 1;
    return [v[0] / n, v[1] / n, v[2] / n];
  }
  // Station 1 — one sphere. mu is the mount angle about x: π mounts the block upside down (Q).
  function sphere(state, index) {
    const { block, c } = C.SPHERES[index];
    const mu = index === 0 ? state.mu : 0;
    const R = C.R_SPHERE;
    const S3 = blochOf(state, index);
    const tip = add(c, mul(C.ARROW, blochToWorld(mu, S3)));
    const tilt = state.tilt ?? state.a;
    const r = Math.hypot(1, tilt);
    const axis = blochToWorld(mu, [tilt / r, 0, -block / r]);
    const ref = depth(c);
    const u = rotX(mu, [1, 0, 0]), v = rotX(mu, [0, 1, 0]), w = rotX(mu, [0, 0, 1]);
    const rings = [halves(loop(c, u, v, R, 72), ref), halves(loop(c, v, w, R, 72), ref), halves(loop(c, u, w, R, 72), ref)];
    // The globe's own outline: the circle where a sphere of radius R turns away from the viewer.
    const glass = G.sphereOf(c, R, P, { steps: 64 }).outline;
    // The tip's path: the circle about the axis through the start point (+x of the frame).
    const start = blochToWorld(mu, [0, 0, 1]);
    const along = axis[0] * start[0] + axis[1] * start[1] + axis[2] * start[2];
    const centre = add(c, mul(C.ARROW * along, axis));
    const e1 = add(start, mul(-along, axis));
    const e1n = Math.hypot(...e1) || 1;
    const u1 = mul(1 / e1n, e1);
    const v1 = [axis[1] * u1[2] - axis[2] * u1[1], axis[2] * u1[0] - axis[0] * u1[2], axis[0] * u1[1] - axis[1] * u1[0]];
    const cone = poly(loop(centre, u1, v1, C.ARROW * e1n, 48), true);
    const feeler = feelerAt(tip, index);
    const parts = [
      `<path class="iso-fill" d="${glass}" style="fill:var(--anatomy-face);opacity:.55"/>`,
      L(rings.map((ring) => ring.back).join(""), { tone: "faint" }),
      L(cone, { tone: "faint" }),
      rod(add(c, mul(-3.6, axis)), add(c, mul(3.6, axis)), 1.15, { tone: "mid" }),
      S(G.sphereOf(c, 1.9, P, { steps: 20 }), { tone: "mid" }),
      rod(c, tip, 0.5, { tone: "hi" }),
      S(G.sphereOf(tip, 1.15, P, { steps: 16 }), { tone: "hi", lit: true }),
      feeler,
      L(rings.map((ring) => ring.front).join(""), { tone: "lo" }),
      L(glass, { tone: "mid" }),
    ];
    return parts.join("");
  }
  // A feeler: a flat round foot resting on the arrow's tip ball, its rod rising to the beam.
  function feelerAt(tip, index) {
    const { c } = C.SPHERES[index];
    const x = c[0] + C.FEELER.dx, z = tip[2] + 1.15;
    return S(k.cylinder(x, c[1], C.FEELER.foot, z, 0.6, P, 28), { tone: "lo", crease: "none" }) + S(k.cylinder(x, c[1], 0.7, z + 0.6, C.FEELER.rod - 0.6, P, 10), { tone: "mid", crease: "none" });
  }
  const tipHeight = (state, index) => {
    const { c } = C.SPHERES[index];
    const mu = index === 0 ? state.mu : 0;
    return c[2] + C.ARROW * blochToWorld(mu, blochOf(state, index))[2];
  };
  const beamEnds = (state) => C.SPHERES.map(({ c }, index) => [c[0] + C.FEELER.dx, c[1], tipHeight(state, index) + 1.15 + C.FEELER.rod]);
  const middleOf = (state) => { const [a, b] = beamEnds(state); return (a[2] + b[2]) / 2; };
  const REST_MIDDLE = C.SPHERES[0].c[2] + 1.15 + C.FEELER.rod;
  const stepOf = (a) => C.CONE.step * a; // the cone step the cord rides for ε = aω

  function beam(state) {
    const [a, b] = beamEnds(state);
    const dir = unit([b[0] - a[0], 0, b[2] - a[2]]);
    const up = [-dir[2], 0, dir[0]];
    const length = Math.hypot(b[0] - a[0], b[2] - a[2]);
    const Fb = G.frameOf(add(a, mul(-3, dir)), dir, [0, 1, 0], up);
    const mid = [(a[0] + b[0]) / 2, a[1], (a[2] + b[2]) / 2];
    // The slide block reaches forward over the cone's steps, so each step's cord lands under it.
    const block = { x: C.STAND[0] - 5, y: C.STAND[1] - 2.6, w: 10, d: 12, r: 0.8 };
    const z = mid[2];
    return [
      // The slide block on the stand, its arm forward to the beam's middle pin.
      S(k.slabOf(block, z - 4, 8, P, 2, 0.3), { tone: "mid" }),
      S(G.prismOf(G.frameOf([C.STAND[0], C.STAND[1] + 9.4, z], [0, 1, 0], [1, 0, 0], [0, 0, 1]), [[-1.2, -1.2], [1.2, -1.2], [1.2, 1.2], [-1.2, 1.2]], 0, mid[1] - C.STAND[1] - 9.4, P), { tone: "mid" }),
      S(G.prismOf(Fb, [[-1.4, -1.6], [1.4, -1.6], [1.4, 1.6], [-1.4, 1.6]], 0, length + 6, P), { tone: "hi" }),
      D([at([a[0], a[1] + 1.5, a[2]]), at([b[0], b[1] + 1.5, b[2]]), at([mid[0], mid[1] + 1.5, mid[2]])], { size: 0.8, tone: "hi" }),
    ].join("");
  }
  function unit(v) { const n = Math.hypot(...v) || 1; return [v[0] / n, v[1] / n, v[2] / n]; }

  // The cone pulley turns with the slide; its drum winds the lane-1 pen cord.
  function pulley(state) {
    const lift = middleOf(state) - REST_MIDDLE;
    const step = stepOf(state.a);
    const turn = lift / step;
    const F = G.frameOf([C.CONE.x, C.STAND[1] + 3, C.CONE.z], [0, -1, 0], [1, 0, 0], [0, 0, 1]);
    const out = [];
    out.push(S(G.disc(0, 3.2, C.CONE.R, F, P), { tone: "mid" }));
    out.push(L(G.spokesOf(F, 0, 3, C.CONE.R - 2, 6, P, { phase: -turn }), { tone: "lo" }));
    const steps = M.AMPLITUDES.map(stepOf);
    for (const [index, r] of steps.entries()) out.push(S(G.disc(-1.6 - index * 1.6, -index * 1.6, r + 0.8, F, P, { steps: 28 }), { tone: r === step ? "hi" : "mid" }));
    // Cord from the step's right side up to the slide block.
    const blockBottom = middleOf(state) - 4;
    const cordX = C.CONE.x + step;
    const cordY = C.STAND[1] + 3 + 1.6 + steps.indexOf(step) * 1.6 - 0.8;
    out.push(L(seg([cordX, cordY, C.CONE.z], [cordX, cordY, blockBottom]), { tone: "hi" }));
    return out.join("");
  }
  // The lane-1 cord: from the drum's top over the idler and down to the pen bar.
  function penCord(state, penZ) {
    const y = C.Y_BAR;
    const top = C.CONE.z + C.CONE.R;
    return L(k.pathOf([at([C.CONE.x, y, top]), at([C.X_IN + C.IDLER.r, y, top]), at([C.X_IN, y, top - C.IDLER.r]), at([C.X_IN, y, penZ + 1.8])]), { tone: "hi" });
  }

  // Station 2 — the two gears. The ket gear turns φ = 2ωt, the bra gear −φ (complex conjugate).
  function gearFace(cx, cy, cz, angle, mirror) {
    const g = C.GEARS, points = [];
    const pitch = TAU / g.teeth;
    for (let i = 0; i < g.teeth; i++) {
      const t = (mirror ? Math.PI - angle - i * pitch + pitch / 2 : angle + i * pitch);
      const step = mirror ? -1 : 1;
      for (const [dt, r] of [[-0.3, g.root], [-0.18, g.tip], [0.18, g.tip], [0.3, g.root]]) {
        const a = t + step * dt * pitch;
        points.push([cx + r * Math.cos(a), cy, cz + r * Math.sin(a)]);
      }
    }
    return points;
  }
  function gears(state) {
    const g = C.GEARS, phi = 2 * state.x;
    const out = [];
    g.c.forEach(([cx, cy, cz], index) => {
      const mirror = index === 1;
      const back = gearFace(cx, cy - g.t / 2, cz, phi, mirror), front = gearFace(cx, cy + g.t / 2, cz, phi, mirror);
      const hull = poly(back, true);
      out.push(`<path class="iso-fill" d="${hull}"/><path class="iso-shade" data-shade="1" d="${hull}"/>`);
      // Tooth flanks between the faces, then the front face.
      const flanks = [];
      for (let i = 0; i < front.length; i += 2) flanks.push(seg(back[i + 1], front[i + 1]));
      const face = poly(front, true);
      out.push(L(hull, { tone: "lo" }));
      out.push(`<path class="iso-fill" d="${face}"/><path class="iso-top" d="${face}"/>`);
      out.push(L(face, { tone: "hi" }));
      const F = G.frameOf([cx, cy + g.t / 2, cz], [0, 1, 0], [1, 0, 0], [0, 0, 1]);
      out.push(L(G.circleOf(F, 0, 3.4, P, 24), { tone: "lo" }));
      out.push(S(G.disc(0, 1.2, 2.2, F, P, { steps: 18 }), { tone: "mid" }));
    });
    return out.join("");
  }
  const pinOf = (state, index) => {
    const g = C.GEARS, phi = 2 * state.x, [cx, cy, cz] = g.c[index];
    const side = index === 0 ? 1 : -1;
    return [cx + side * g.pin * Math.sin(phi), cy + g.t / 2, cz - g.pin * Math.cos(phi)];
  };
  // The yoke's slot height for each leg; an unhooked leg stays latched at rest.
  const yokeZ = (state, index) => (index === 1 && state.unhooked > 0.5 ? C.GEARS.c[1][2] - C.GEARS.pin : pinOf(state, index)[2]);
  function yokes(state) {
    const g = C.GEARS, out = [];
    g.c.forEach(([cx, cy, cz], index) => {
      const pin = pinOf(state, index);
      const z = yokeZ(state, index);
      const y0 = cy + g.t / 2 + 0.6;
      const hooked = !(index === 1 && state.unhooked > 0.5);
      out.push(S(G.disc(0, hooked ? 3.6 : 1.4, 1.1, G.frameOf(pin, [0, 1, 0], [1, 0, 0], [0, 0, 1]), P, { steps: 14 }), { tone: "hi" }));
      const slot = { x: cx - g.pin - 2.4, y: y0 + 1.4, w: 2 * g.pin + 4.8, d: 1.6, r: 0.4 };
      out.push(S(k.slabOf(slot, z - 1.8, 3.6, P, 2), { tone: "mid" }));
      out.push(L(k.pathOf([[cx - g.pin - 1, z - 0.5], [cx + g.pin + 1, z - 0.5], [cx + g.pin + 1, z + 0.5], [cx - g.pin - 1, z + 0.5]].map(([x, zz]) => at([x, y0 + 3, zz])), true), { tone: "lo" }));
      out.push(S(k.slabOf({ x: cx - 1, y: y0 + 1.6, w: 2, d: 1.4, r: 0.3 }, z + 1.8, g.stem - 1.8, P, 2), { tone: "mid" }));
    });
    // Whiffletree: one bar across the two stems; its middle drives the lane-2 pen bar.
    const [l, r] = g.c.map(([cx], index) => [cx, g.c[0][1] + g.t / 2 + 2.3, yokeZ(state, index) + g.stem]);
    const mid = [(l[0] + r[0]) / 2, l[1], (l[2] + r[2]) / 2];
    const dir = unit([r[0] - l[0], 0, r[2] - l[2]]);
    const Fb = G.frameOf(add(l, mul(-2.4, dir)), dir, [0, 1, 0], [-dir[2], 0, dir[0]]);
    out.push(S(G.prismOf(Fb, [[-1.2, -1.5], [1.2, -1.5], [1.2, 1.5], [-1.2, 1.5]], 0, Math.hypot(r[0] - l[0], r[2] - l[2]) + 4.8, P), { tone: "hi" }));
    out.push(D([l, r, mid].map((p) => at([p[0], p[1] + 1.3, p[2]])), { size: 0.8, tone: "hi" }));
    // The middle pin reaches back to the lane-2 pen bar.
    out.push(S(k.slabOf({ x: mid[0] - 1, y: C.Y_BAR + 1, w: 2, d: mid[1] - 1.2 - C.Y_BAR - 1, r: 0.3 }, mid[2] - 1, 2, P, 2), { tone: "mid" }));
    // The latch that holds an unhooked leg: a hook swung over the right yoke's slot bar.
    const latch = [C.GEARS.c[1][0] + g.pin + 3.4, C.GEARS.c[1][1] + 5.4, C.GEARS.c[1][2] - g.pin + 2.6];
    const swing = state.unhooked * 1.2;
    out.push(L(seg(latch, [latch[0] - 3.2 * swing, latch[1], latch[2] - 1.2 * swing]), { tone: "hi" }));
    return out.join("");
  }
  const lane2Z = (state) => (yokeZ(state, 0) + yokeZ(state, 1)) / 2 + C.GEARS.stem;

  // Station 3 — the integrator. The wheel rides at radius travel·sin 2x and turns ∫ of it.
  const wheelX = (state) => C.DISC.c[0] + C.WHEEL.travel * Math.sin(2 * state.x);
  const wheelTurn = (state) => (C.OMEGA_DISC * C.WHEEL.travel * (1 - Math.cos(2 * state.x))) / (2 * C.WHEEL.r);
  function integrator(state) {
    const { c, r, z, h } = C.DISC;
    const top = z + h;
    const out = [];
    const disc = state.discTurn;
    // Rings and radial marks on the disc top turn with it.
    const marks = [];
    for (let i = 0; i < 12; i++) {
      const a = disc + (i / 12) * TAU;
      marks.push(k.lineOnTop([c[0] + Math.cos(a) * 4.5, c[1] + Math.sin(a) * 4.5], [c[0] + Math.cos(a) * (r - 2), c[1] + Math.sin(a) * (r - 2)], top, P));
    }
    out.push(L(marks.join(""), { tone: "faint" }));
    const wx = wheelX(state);
    // The wheel (axis along x) and its fork on the carriage.
    const F = G.frameOf([wx, c[1], C.WHEEL.axle], [1, 0, 0], [0, 1, 0], [0, 0, 1]);
    const turn = wheelTurn(state);
    out.push(S(G.disc(-1.4, 1.4, C.WHEEL.r, F, P, { steps: 36 }), { tone: "hi" }));
    out.push(L(G.spokesOf(F, 1.45, 1.4, C.WHEEL.r - 0.8, 5, P, { phase: turn }), { tone: "mid" }));
    out.push(L(G.circleOf(F, 1.45, C.WHEEL.r - 0.8, P, 32), { tone: "lo" }));
    const fork = { x: wx - 4.8, y: c[1] - 5, w: 9.6, d: 10, r: 1 };
    out.push(S(k.slabOf({ x: fork.x, y: fork.y + 1, w: 1.6, d: 8, r: 0.3 }, C.WHEEL.axle - 1, 9, P, 2), { tone: "mid" }));
    out.push(S(k.slabOf({ x: fork.x + fork.w - 1.6, y: fork.y + 1, w: 1.6, d: 8, r: 0.3 }, C.WHEEL.axle - 1, 9, P, 2), { tone: "mid" }));
    out.push(S(k.slabOf(fork, C.WHEEL.axle + 8, 2.4, P, 2, 0.3), { tone: "mid" }));
    // Rail sleeves and the connecting rod to the yoke's crosshead.
    for (const dy of [-9, 9]) out.push(S(G.disc(-3, 3, 1.9, G.frameOf([wx, c[1] + dy, 22], [1, 0, 0], [0, 1, 0], [0, 0, 1]), P, { steps: 16 }), { tone: "mid" }));
    return out.join("");
  }
  function axle(state) {
    const turn = wheelTurn(state);
    const F = G.frameOf([C.X_IN, C.DISC.c[1], C.WHEEL.axle], [1, 0, 0], [0, 1, 0], [0, 0, 1]);
    const out = [];
    out.push(S(G.disc(0, C.DISC.c[0] + C.WHEEL.travel + 12 - C.X_IN, 0.9, F, P, { steps: 12 }), { tone: "mid" }));
    // Pinion at the left end; rack behind it rising with the integral.
    out.push(S(G.disc(-0.8, 3.2, C.WHEEL.pinion, F, P, { steps: 22 }), { tone: "mid" }));
    out.push(L(G.spokesOf(F, 3.25, 0.8, C.WHEEL.pinion - 0.4, 3, P, { phase: turn }), { tone: "lo" }));
    return out.join("");
  }
  const lane3Z = (state) => C.LANES[2] + C.WHEEL.pinion * wheelTurn(state);
  function rack(state) {
    const top = lane3Z(state);
    const y = C.DISC.c[1] - C.WHEEL.pinion - 1.2;
    const plan = { x: C.X_IN - 1.2, y: y - 1.2, w: 2.4, d: 2.4, r: 0.3 };
    const out = [S(k.slabOf(plan, top - 30, 30, P, 2), { tone: "mid" })];
    const teeth = [];
    for (let z = top - 29; z < top - 1; z += 1.4) if (z > 3.5) teeth.push(k.pathOf([at([C.X_IN - 1.2, y + 1.2, z]), at([C.X_IN + 1.2, y + 1.2, z])]));
    out.push(L(teeth.join(""), { tone: "lo" }));
    // Stub back to the pen bar.
    out.push(S(k.slabOf({ x: C.X_IN - 1, y: C.Y_BAR, w: 2, d: y - 1.2 - C.Y_BAR, r: 0.3 }, top - 1.2, 2.4, P, 2), { tone: "mid" }));
    return out.join("");
  }
  function yoke(state) {
    const [x, y, z] = C.YOKE.c;
    const a = 2 * state.x;
    const F = G.frameOf([x, y, z], [0, 1, 0], [1, 0, 0], [0, 0, 1]);
    const pin = [x + C.YOKE.r * Math.sin(a), y + 2.6, z + C.YOKE.r * Math.cos(a)];
    const wx = wheelX(state);
    const out = [];
    out.push(L(G.spokesOf(F, 2.45, 2.4, C.YOKE.r + 0.4, 4, P, { phase: Math.PI / 2 - a }), { tone: "lo" }));
    out.push(S(G.disc(2.4, 4.4, 1.2, G.frameOf(pin, [0, 1, 0], [1, 0, 0], [0, 0, 1]), P, { steps: 12 }), { tone: "hi" }));
    // Crosshead: a vertical slotted bar at the pin's x, joined to the carriage by a rod along x.
    const slot = { x: pin[0] - 1.6, y: y + 4.4, w: 3.2, d: 1.6, r: 0.4 };
    out.push(S(k.slabOf(slot, z - C.YOKE.r - 3, 2 * C.YOKE.r + 6, P, 2), { tone: "mid" }));
    out.push(L(k.pathOf([[-0.5, -C.YOKE.r - 1.5], [0.5, -C.YOKE.r - 1.5], [0.5, C.YOKE.r + 1.5], [-0.5, C.YOKE.r + 1.5]].map(([dx, dz]) => at([pin[0] + dx, y + 6, z + dz])), true), { tone: "lo" }));
    out.push(S(G.disc(0, pin[0] - wx - 3, 0.9, G.frameOf([wx + 3, C.DISC.c[1] + 9, 22], [1, 0, 0], [0, 1, 0], [0, 0, 1]), P, { steps: 10 }), { tone: "mid" }));
    return out.join("");
  }

  // The paper: moving time rules, the three traces and the preparation marks.
  function paper(state) {
    const y = C.Y_P + 0.05;
    const left = C.BOARD.x + 1.5;
    const rules = [], majors = [];
    const step = (C.PAPER_V * Math.PI) / 4;
    const offset = state.paper % (step * 4);
    for (let i = 0; i < 40; i++) {
      const x = C.X_PEN + 22 - ((i * step + (step * 4 - offset)) % (step * 40));
      if (x < left || x > C.BOARD.x + C.BOARD.w - 1.5) continue;
      const major = i % 4 === 0;
      for (const base of C.LANES) (major ? majors : rules).push(k.pathOf([at([x, y, base]), at([x, y, base + 2 * C.GAIN])]));
    }
    return L(rules.join(""), { tone: "faint", free: true }) + L(majors.join(""), { tone: "lo", free: true });
  }
  function traces(state) {
    const y = C.Y_P + 0.08;
    const out = [], marks = [];
    for (const run of state.runs) {
      const lanes = [[], [], []];
      for (const sample of run.samples) {
        const x = C.X_PEN - (state.paper - sample.p);
        if (x < C.BOARD.x + 1) continue;
        sample.z.forEach((z, lane) => lanes[lane].push(at([x, y, z])));
      }
      for (const points of lanes) if (points.length > 1) out.push(k.pathOf(points));
      const mx = C.X_PEN - (state.paper - run.p0);
      if (mx > C.BOARD.x + 1) marks.push(k.pathOf([at([mx, y, C.PAPER_Z[0] + 1]), at([mx, y, C.PAPER_Z[0] + 4])]));
    }
    return L(out.join(""), { tone: "lit", free: true }) + L(marks.join(""), { tone: "hi", free: true });
  }
  function spoolMarks(state) {
    const out = [];
    for (const [x, wound] of [[C.SPOOL.take, C.SPOOL.r + 1.2], [C.SPOOL.supply, C.SPOOL.r + 2.4]]) {
      const a = state.paper / wound;
      const y = C.Y_P - wound;
      out.push(k.lineOnTop([x + Math.cos(a) * 3.4, y + Math.sin(a) * 3.4], [x + Math.cos(a) * C.SPOOL.flange, y + Math.sin(a) * C.SPOOL.flange], C.PAPER_Z[1] + 2, P));
    }
    return L(out.join(""), { tone: "mid" });
  }

  // Pen bars: each slides on the column; the stylus at X_PEN writes on the paper.
  function penBar(z, lane) {
    const y = C.Y_BAR;
    const right = lane === 1 ? (C.GEARS.c[0][0] + C.GEARS.c[1][0]) / 2 : C.X_IN;
    const out = [];
    out.push(S(k.slabOf({ x: C.X_PEN - 2, y: y - 1, w: right - C.X_PEN + 3, d: 2, r: 0.4 }, z - 1, 2, P, 2), { tone: "hi" }));
    // Slide block on the column.
    const [cx, cy] = C.COLUMN;
    out.push(S(k.slabOf({ x: cx - 3.2, y: cy - 3, w: 6.4, d: 6.2, r: 0.8 }, z - 3.5, 7, P, 2, 0.3), { tone: "mid" }));
    // Stylus holder and the stylus to the paper.
    out.push(S(k.slabOf({ x: C.X_PEN - 2.2, y: C.Y_P + 0.8, w: 4.4, d: y - C.Y_P - 1.6, r: 0.5 }, z - 1.6, 3.2, P, 2), { tone: "mid" }));
    out.push(L(seg([C.X_PEN, C.Y_P + 0.9, z], [C.X_PEN, C.Y_P + 0.05, z]), { tone: "lit" }));
    return out.join("");
  }

  // Lane 1 hangs from the drum: the slide's lift times R over the cone step 16a, i.e. ωJ/(sε)·GAIN.
  const lane1Z = (state) => C.LANES[0] + ((middleOf(state) - REST_MIDDLE) * C.CONE.R) / stepOf(state.a);
  // The ε knob on the top shelf: its pointer sits on the detent for the current ε/ω.
  function knob(a) {
    const [x, y] = C.DIAL;
    const z0 = C.TIERS[2].z + C.TIERS[2].h + 1.6;
    const angle = -0.9 + Math.max(0, M.AMPLITUDES.indexOf(a)) * 0.9;
    return [
      S(k.cylinder(x, y, 3.6, z0, 3.4, P, 26), { tone: "hi" }),
      L(k.knurl(x, y, 3.6, z0, z0 + 3.4, 24, P), { tone: "lo" }),
      L(k.lineOnTop([x, y], [x + Math.sin(angle) * 3.2, y - Math.cos(angle) * 3.2], z0 + 3.45, P), { tone: "mid" }),
    ].join("");
  }

  // A switch's knob slides from its first mark to its second as f goes 0 → 1.
  function switchKnob(index, f) {
    const { tier, plan } = C.SWITCHES[index];
    const z0 = C.TIERS[tier].z + C.TIERS[tier].h + 2.4;
    const x = plan.x + 4.5 + f * (plan.w - 9), y = plan.y + plan.d / 2;
    return [S(k.cylinder(x, y, 1, z0, 1.6, P, 12), { tone: "mid" }), S(k.cylinder(x, y, 2.6, z0 + 1.6, 3.4, P, 22), { tone: "hi" }), L(k.knurl(x, y, 2.6, z0 + 1.6, z0 + 5, 18, P), { tone: "lo" })].join("");
  }
  const lanesOf = (state) => [lane1Z(state), lane2Z(state), lane3Z(state)];
  return { sphere, beam, pulley, penCord, gears, yokes, integrator, axle, rack, yoke, paper, traces, spoolMarks, penBar, knob, switchKnob, lanesOf };
}

const LIVE = makeLive(k, G, P, C, M);

// --- the run clock -------------------------------------------------------------------------

// A run prepares the state at t = 0 and records 0 ≤ ωt ≤ 2π; a short gap separates runs.
// The pens are placed by the machines alone; they must land where the model says (8.14)/(1.11)/(1.12) put them.
for (const mode of M.MODES) for (const a of M.AMPLITUDES) for (let i = 0; i <= 48; i++) {
  const x = (i / 48) * C.RUN;
  const state = { a, mode, x, mu: mode === "readT" ? 0 : Math.PI, unhooked: mode === "oneLeg" ? 1 : 0 };
  const pens = LIVE.lanesOf(state), t = M.testimony(mode, a, x);
  [t.finite, t.legs, t.kubo].forEach((value, lane) => {
    if (Math.abs(pens[lane] - (C.LANES[lane] + C.GAIN * value)) > 1e-9) throw new Error(`lane ${lane} off the model: ${mode} a=${a} x=${x} pen ${pens[lane]} model ${C.LANES[lane] + C.GAIN * value}`);
  });
}

// The first frame: the tour's last honest run (a = 1/8) has just finished, the previous
// (a = 1/4) is still on the paper.
function restingState() {
  const runs = [];
  let paper = 0;
  const record = (a, mode) => {
    const run = { a, mode, p0: paper, samples: [] };
    for (let i = 0; i <= 160; i++) {
      const x = (i / 160) * C.RUN;
      const t = M.testimony(mode, a, x);
      run.samples.push({ p: paper + x * C.PAPER_V, z: [C.LANES[0] + C.GAIN * t.finite, C.LANES[1] + C.GAIN * t.legs, C.LANES[2] + C.GAIN * t.kubo] });
    }
    paper += (C.RUN + C.GAP) * C.PAPER_V;
    runs.push(run);
  };
  record(1 / 2, "honest");
  record(1 / 4, "honest");
  record(1 / 8, "honest");
  paper -= C.GAP * C.PAPER_V * 0.5;
  return { a: 1 / 8, mode: "honest", x: C.RUN, mu: Math.PI, unhooked: 0, paper, discTurn: C.OMEGA_DISC * C.RUN, runs };
}

// --- static art ----------------------------------------------------------------------------

const at = (point) => k.iso(point, P);
const S = (paths, style) => k.solidSvg(paths, style);
const L = (d, style) => k.lineSvg(d, style);
const D = (points, style) => k.dotsSvg(points, style);
const seg = (a, b) => k.segment(a, b, P);
const loop = (points) => k.pathOf(points.map(at)) + "Z";

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
  // Front ruler in units of ωt: one major tick per π/2 at the paper's speed.
  const strip = { x: C.PLATE.x + 14, y: C.PLATE.y + C.PLATE.d - 13, w: 150, d: 6, r: 1 };
  out.push(S(k.slabOf(strip, 0, 0.6, P, 3), { tone: "lo", crease: "none" }));
  const ticks = k.topTicks(strip.x + 4, strip.x + strip.w - 4, (C.PAPER_V * Math.PI) / 8, 4, strip.y + 0.8, 0.6, [1.6, 3], P);
  out.push(L(ticks.minor, { tone: "lo" }), L(ticks.major, { tone: "mid" }));
  out.push(D([at([strip.x + 2, strip.y + 3, 0.6]), at([strip.x + strip.w - 2, strip.y + 3, 0.6])], { size: 0.45 }));
  // Label plate.
  const label = { x: -150 + 186, y: 24, w: 44, d: 12, r: 1.5 };
  out.push(S(k.slabOf(label, 0, 0.8, P, 3, 0.3), { tone: "lo", crease: "none" }));
  for (const [index, y] of [label.y + 4, label.y + 7.6].entries()) out.push(L(k.lineOnTop([label.x + 5, y], [label.x + (index ? 26 : 38), y], 0.8, P), { tone: "faint", free: true }));
  out.push(D([at([label.x + 2, label.y + 2.4, 0.8]), at([label.x + label.w - 2, label.y + label.d - 2.4, 0.8])], { size: 0.4 }));
  return out.join("");
}

function board() {
  const { BOARD, BOARD_H, PAPER_Z, Y_P } = C;
  const out = [`<path class="iso-halo" d="${k.haloOf(BOARD, 0, BOARD_H, P)}" style="filter:blur(6px)"/>`];
  // Two feet holding the board upright.
  for (const x of [BOARD.x + 18, BOARD.x + BOARD.w - 18]) out.push(S(k.slabOf({ x: x - 5, y: BOARD.y - 6, w: 10, d: 18, r: 1.5 }, 0, 4, P, 3, 0.4), { tone: "mid" }));
  out.push(S(k.slabOf(BOARD, 0, BOARD_H, P, 3, 0.6), { tone: "mid", inner: L(k.sideSeam(BOARD, 6, P, 3), { tone: "faint" }) }));
  // The paper on the face, its lanes ruled.
  const paper = [[BOARD.x + 1, Y_P, PAPER_Z[0]], [BOARD.x + BOARD.w - 1, Y_P, PAPER_Z[0]], [BOARD.x + BOARD.w - 1, Y_P, PAPER_Z[1]], [BOARD.x + 1, Y_P, PAPER_Z[1]]];
  out.push(`<path class="iso-fill" d="${loop(paper)}" style="fill:var(--anatomy-face)"/>`);
  out.push(L(loop(paper), { tone: "mid" }));
  const lines = [], faint = [];
  for (const base of C.LANES) {
    lines.push(seg([BOARD.x + 1, Y_P + 0.03, base], [BOARD.x + BOARD.w - 1, Y_P + 0.03, base]));
    lines.push(seg([BOARD.x + 1, Y_P + 0.03, base + 2 * C.GAIN], [BOARD.x + BOARD.w - 1, Y_P + 0.03, base + 2 * C.GAIN]));
    faint.push(seg([BOARD.x + 1, Y_P + 0.03, base + C.GAIN], [BOARD.x + BOARD.w - 1, Y_P + 0.03, base + C.GAIN]));
  }
  out.push(L(faint.join(""), { tone: "faint" }), L(lines.join(""), { tone: "lo" }));
  // Sprocket holes along both edges of the paper.
  const holes = [];
  for (let x = BOARD.x + 5; x < BOARD.x + BOARD.w - 3; x += 6) for (const z of [PAPER_Z[0] + 2.4, PAPER_Z[1] - 2.4]) holes.push(at([x, Y_P + 0.03, z]));
  out.push(D(holes, { size: 0.45, tone: "lo" }));
  // Top rail with screws.
  const rail = { x: BOARD.x - 2, y: BOARD.y - 1, w: BOARD.w + 4, d: BOARD.d + 2, r: 1 };
  out.push(S(k.slabOf(rail, BOARD_H, 3, P, 2, 0.4), { tone: "mid" }));
  out.push(D([BOARD.x + 6, BOARD.x + BOARD.w / 2, BOARD.x + BOARD.w - 6].map((x) => at([x, BOARD.y + BOARD.d / 2, BOARD_H + 3])), { size: 0.45 }));
  return out.join("");
}

function spool(x, kind) {
  const { SPOOL, Y_P, PAPER_Z } = C;
  // The paper leaves the roll tangent to the board's face.
  const wound = kind === "take" ? SPOOL.r + 1.2 : SPOOL.r + 2.4;
  const y = Y_P - wound;
  const out = [S(k.cylinder(x, y, SPOOL.flange + 1.5, 0, 3, P, 32, 0.4), { tone: "mid" })];
  out.push(S(k.cylinder(x, y, 2.2, 3, PAPER_Z[0] - 5, P, 16), { tone: "mid" }));
  out.push(S(k.cylinder(x, y, SPOOL.flange, PAPER_Z[0] - 2, 1.6, P, 40, 0.3), { tone: "mid" }));
  out.push(S(k.cylinder(x, y, wound, PAPER_Z[0] - 0.4, PAPER_Z[1] - PAPER_Z[0] + 0.8, P, 40), { tone: "hi", crease: "none" }));
  out.push(L([0.25, 0.5, 0.75].map((f) => k.sideArc(x, y, wound, PAPER_Z[0] + f * (PAPER_Z[1] - PAPER_Z[0]), P, 24)).join(""), { tone: "faint" }));
  out.push(S(k.cylinder(x, y, SPOOL.flange, PAPER_Z[1] + 0.4, 1.6, P, 40, 0.3), { tone: "mid" }));
  out.push(L(k.ring(x, y, 3.4, PAPER_Z[1] + 2, P, 24), { tone: "lo" }));
  out.push(S(k.cylinder(x, y, 2.2, PAPER_Z[1] + 2, 3, P, 16), { tone: "mid" }));
  return out.join("");
}

function column() {
  const [x, y] = C.COLUMN;
  const out = [S(k.cylinder(x, y, 6, 0, 3, P, 28, 0.4), { tone: "mid" })];
  out.push(S(k.slabOf({ x: x - 1.6, y: y - 1.6, w: 3.2, d: 3.2, r: 0.5 }, 3, C.LANES[0] + 2 * C.GAIN + 10 - 3, P, 2, 0.2), { tone: "mid" }));
  out.push(S(k.cylinder(x, y, 2.6, C.LANES[0] + 2 * C.GAIN + 10, 2, P, 18), { tone: "mid" }));
  // Stops at the top and bottom of each pen's travel.
  const stops = [];
  for (const base of C.LANES) for (const z of [base - 4.5, base + 2 * C.GAIN + 4.5]) stops.push(at([x, y + 1.6, z]));
  out.push(D(stops, { size: 0.55, tone: "mid" }));
  return out.join("");
}

function post([x, y], top) {
  const out = [S(k.slabOf({ x: x - 3, y: y - 3, w: 6, d: 6, r: 1 }, 0, top, P, 2, 0.3), { tone: "mid" })];
  out.push(D([12, top - 6].map((z) => at([x, y + 3, z])), { size: 0.45 }));
  return out.join("");
}

function tier({ z, h, plan }, index) {
  const out = [];
  if (index) out.push(`<path class="iso-halo" d="${k.haloOf(plan, z - 18, 18, P)}" style="filter:blur(10px);opacity:calc(var(--anatomy-halo-opacity) * .35)"/>`);
  out.push(S(k.slabOf(plan, z, h, P, 3, 0.5), { tone: "mid", inner: L(k.sideSeam(plan, z + h / 2, P, 3), { tone: "faint" }) }));
  out.push(D(C.POSTS.map(([x, y]) => at([x, y + 4.5, z + h])), { size: 0.5 }));
  return out.join("");
}

// Station 1 statics: forks, the feeler guide bridge, the slide stand, the idler post.
function station1Back() {
  const z0 = C.TIERS[2].z + C.TIERS[2].h;
  const out = [];
  // Slide stand behind the spheres, its guide rods and the cone pulley's bearing.
  const [sx, sy] = C.STAND;
  out.push(S(k.slabOf({ x: sx - 5, y: sy - 4, w: 10, d: 4, r: 0.6 }, z0, 4, P, 2, 0.3), { tone: "mid" }));
  for (const dx of [-3.6, 3.6]) out.push(S(k.cylinder(sx + dx, sy - 2, 0.9, z0 + 4, C.STAND_TOP - z0 - 4, P, 10), { tone: "mid", crease: "none" }));
  out.push(S(k.slabOf({ x: sx - 5, y: sy - 4, w: 10, d: 4, r: 0.6 }, C.STAND_TOP, 2.4, P, 2, 0.3), { tone: "mid" }));
  out.push(S(k.slabOf({ x: C.CONE.x - 3, y: sy - 6, w: 6, d: 3, r: 0.6 }, z0, C.CONE.z - z0 + 3, P, 2, 0.3), { tone: "mid" }));
  // Idler post at the lane-1 input and its pulley.
  out.push(S(k.slabOf({ x: C.X_IN - 1.6, y: C.Y_BAR - 4.6, w: 3.2, d: 3.2, r: 0.5 }, z0, C.IDLER.z - z0 + 3, P, 2), { tone: "mid" }));
  out.push(S(G.disc(-1.3, 1.3, C.IDLER.r, G.frameOf([C.X_IN + C.IDLER.r, C.Y_BAR, C.IDLER.z], [0, 1, 0], [1, 0, 0], [0, 0, 1]), P, { steps: 16 }), { tone: "mid" }));
  return out.join("");
}
// Each sphere hangs in a half ring on trunnions along x, so the block can be mounted either way up.
function fork(index) {
  const { c } = C.SPHERES[index];
  const R = C.R_SPHERE;
  const z0 = C.TIERS[2].z + C.TIERS[2].h;
  const ring = R + 2.2;
  const out = [S(k.cylinder(c[0], c[1], 6.5, z0, 2, P, 28, 0.4), { tone: "mid" })];
  out.push(S(k.cylinder(c[0], c[1], 1.8, z0 + 2, c[2] - ring - z0 - 2 + 0.6, P, 14), { tone: "mid" }));
  // The half ring: a flat band in the xz-plane from one trunnion under the sphere to the other.
  const band = (r) => Array.from({ length: 33 }, (_, i) => { const a = Math.PI + (i / 32) * Math.PI; return [c[0] + r * Math.cos(a), c[1], c[2] + r * Math.sin(a)]; });
  const inner = band(ring - 0.9), outer = band(ring + 0.9);
  const face = (dy) => [...outer, ...[...inner].reverse()].map(([x, , z]) => at([x, c[1] + dy, z]));
  const front = k.pathOf(face(1.1), true), back = k.pathOf(face(-1.1), true);
  out.push(`<path class="iso-fill" d="${back}"/><path class="iso-shade" data-shade="1" d="${back}"/>`);
  out.push(`<path class="iso-fill" d="${front}"/><path class="iso-top" d="${front}"/>`);
  out.push(L(front, { tone: "mid" }));
  for (const side of [-1, 1]) {
    const x = c[0] + side * ring;
    out.push(S(G.disc(-0.9, 0.9, 1.9, G.frameOf([x, c[1], c[2]], [side, 0, 0], [0, 1, 0], [0, 0, 1]), P, { steps: 16 }), { tone: "mid" }));
  }
  return out.join("");
}
// The feelers' guide: a bar across both spheres, carried on an arm from the slide stand.
function guideBridge() {
  const y = C.SPHERES[0].c[1];
  const x0 = C.SPHERES[0].c[0] + C.FEELER.dx - 4, x1 = C.SPHERES[1].c[0] + C.FEELER.dx + 4;
  const [sx, sy] = C.STAND;
  const out = [];
  out.push(S(k.slabOf({ x: sx - 1.4, y: sy, w: 2.8, d: y - sy, r: 0.4 }, C.GUIDE_Z - 0.2, 2, P, 2), { tone: "mid" }));
  out.push(S(k.slabOf({ x: x0, y: y - 2.2, w: x1 - x0, d: 4.4, r: 1.2 }, C.GUIDE_Z, 1.6, P, 2, 0.3), { tone: "mid" }));
  out.push(L(C.SPHERES.map(({ c }) => k.ring(c[0] + C.FEELER.dx, y, 1.5, C.GUIDE_Z + 1.6, P, 14)).join(""), { tone: "lo" }));
  out.push(D([at([x0 + 1.6, y, C.GUIDE_Z + 1.6]), at([x1 - 1.6, y, C.GUIDE_Z + 1.6])], { size: 0.45 }));
  return out.join("");
}
// The ε knob on the top shelf's front edge: three detents for ε/ω = 1/2, 1/4, 1/8.
function epsilonDial() {
  const [x, y] = C.DIAL;
  const z0 = C.TIERS[2].z + C.TIERS[2].h;
  const out = [S(k.cylinder(x, y, 7, z0, 1.6, P, 32, 0.3), { tone: "mid" })];
  const ticks = [];
  for (const [index] of M.AMPLITUDES.entries()) {
    const a = -0.9 + index * 0.9;
    ticks.push(k.lineOnTop([x + Math.sin(a) * 5, y - Math.cos(a) * 5], [x + Math.sin(a) * 6.6, y - Math.cos(a) * 6.6], z0 + 1.6, P));
  }
  out.push(L(ticks.join(""), { tone: "hi" }));
  out.push(k.faceTextSvg(k.topMatrix([x - 6.2, y + 6.4], z0 + 1.6, P), "ε", { size: 3.2, tone: "mid" }));
  return out.join("");
}
function switchPlate(index) {
  const { tier, plan, marks } = C.SWITCHES[index];
  const z0 = C.TIERS[tier].z + C.TIERS[tier].h;
  const out = [S(k.slabOf(plan, z0, 2.4, P, 3, 0.4), { tone: "mid" })];
  const slot = { x: plan.x + 3.2, y: plan.y + plan.d / 2 - 1, w: plan.w - 6.4, d: 2, r: 1 };
  out.push(L(k.planOutline(slot, z0 + 2.4, P, 4), { tone: "lo" }));
  marks.forEach((mark, i) => out.push(k.faceTextSvg(k.topMatrix([plan.x + 3.2 + i * (plan.w - 9.6), plan.y + plan.d - 0.8], z0 + 2.4, P), mark, { size: 3, tone: i ? "lo" : "mid" })));
  out.push(D([at([plan.x + 1.6, plan.y + 1.6, z0 + 2.4]), at([plan.x + plan.w - 1.6, plan.y + 1.6, z0 + 2.4])], { size: 0.4 }));
  return out.join("");
}

// Station 2 statics: the gear plate, the yoke guide bar, the bra/ket bearing bosses.
function station2Back() {
  const g = C.GEARS;
  const z0 = C.TIERS[1].z + C.TIERS[1].h;
  const out = [];
  const plate = { x: g.c[0][0] - g.tip - 3, y: g.c[0][1] - g.t / 2 - 3.4, w: g.c[1][0] - g.c[0][0] + 2 * g.tip + 6, d: 2.2, r: 0.6 };
  out.push(S(k.slabOf(plate, z0, g.c[0][2] + g.tip + 2 - z0, P, 2, 0.4), { tone: "mid" }));
  out.push(D(g.c.flatMap(([cx]) => [at([cx - g.tip - 1.2, plate.y + plate.d, z0 + 3]), at([cx + g.tip + 1.2, plate.y + plate.d, z0 + 3])]), { size: 0.45 }));
  return out.join("");
}
function station2Guide() {
  const g = C.GEARS;
  const z0 = C.TIERS[1].z + C.TIERS[1].h;
  const y = g.c[0][1] + g.t / 2 + 1.6;
  const x0 = g.c[0][0] - g.tip - 2, x1 = g.c[1][0] + g.tip + 2;
  const out = [];
  for (const x of [x0, x1]) out.push(S(k.slabOf({ x: x - 1.2, y: y - 0.4, w: 2.4, d: 2.4, r: 0.4 }, z0, g.guide + 2 - z0, P, 2), { tone: "mid" }));
  out.push(S(k.slabOf({ x: x0 - 1.6, y: y - 0.6, w: x1 - x0 + 3.2, d: 2.8, r: 0.5 }, g.guide, 2, P, 2, 0.3), { tone: "mid" }));
  return out.join("");
}
// The one-leg latch's bracket on the right.
function latchBracket() {
  const g = C.GEARS;
  const [cx, cy, cz] = g.c[1];
  return S(k.slabOf({ x: cx + g.pin + 2.4, y: cy + 3.6, w: 2.4, d: 2.4, r: 0.4 }, C.TIERS[1].z + C.TIERS[1].h, cz - g.pin + 2.6 - C.TIERS[1].z - C.TIERS[1].h, P, 2), { tone: "mid" });
}

// Station 3 statics: the disc and its spindle housing, the carriage rails, the yoke frame.
function station3Back() {
  const { c, r, z, h } = C.DISC;
  const out = [`<path class="iso-halo" d="${k.haloOf({ x: c[0] - r, y: c[1] - r, w: 2 * r, d: 2 * r, r }, 3, 4, P)}" style="filter:blur(5px)"/>`];
  out.push(S(k.cylinder(c[0], c[1], 7, 3, z - 3, P, 28), { tone: "mid" }));
  out.push(S(k.cylinder(c[0], c[1], r, z, h, P, 72, 0.6), { tone: "hi", crease: "lo" }));
  out.push(L(k.ring(c[0], c[1], r - 2, z + h, P, 64) + k.ring(c[0], c[1], 4.5, z + h, P, 24), { tone: "lo" }));
  out.push(L(k.knurl(c[0], c[1], r, z, z + h, 96, P, 0.6), { tone: "faint" }));
  // Rails above the disc for the wheel carriage, on four standards.
  for (const dy of [-9, 9]) {
    for (const x of [c[0] - r - 4, c[0] + r + 4]) out.push(S(k.slabOf({ x: x - 1.4, y: c[1] + dy - 1.4, w: 2.8, d: 2.8, r: 0.4 }, 3, 22 - 3, P, 2), { tone: "mid" }));
  }
  return out.join("");
}
function rails() {
  const { c } = C.DISC;
  const { r } = C.DISC;
  return [-9, 9].map((dy) => S(G.disc(0, 2 * r + 10, 0.9, G.frameOf([c[0] - r - 5, c[1] + dy, 22], [1, 0, 0], [0, 1, 0], [0, 0, 1]), P, { steps: 10 }), { tone: "mid" })).join("");
}
function yokeFrame() {
  const [x, y, z] = C.YOKE.c;
  const out = [];
  out.push(S(k.slabOf({ x: x - 3, y: y - 4, w: 6, d: 4, r: 0.6 }, 3, z - 3, P, 2, 0.3), { tone: "mid" }));
  const F = G.frameOf([x, y, z], [0, 1, 0], [1, 0, 0], [0, 0, 1]);
  out.push(S(G.disc(0, 2.4, C.YOKE.r + 1.8, F, P), { tone: "mid" }));
  out.push(L(G.circleOf(F, 2.45, C.YOKE.r + 0.4, P, 64), { tone: "lo" }));
  out.push(S(G.disc(2.4, 3.6, 2.4, F, P, { steps: 18 }), { tone: "mid" }));
  // Guides for the crosshead along x.
  for (const dz of [-C.YOKE.r - 4.2, C.YOKE.r + 4.2]) out.push(S(G.disc(-22, 8, 0.8, G.frameOf([x, y + 5.2, z + dz], [1, 0, 0], [0, 1, 0], [0, 0, 1]), P, { steps: 10 }), { tone: "mid" }));
  return out.join("");
}

// The time column: one shaft at the back drives the paper, the spheres' hubs, the gears and the disc.
function timeColumn() {
  const [x, y] = [176, -30];
  const top = C.TIERS[2].z + C.TIERS[2].h;
  const out = [];
  C.TIERS.forEach(({ z, h }, index) => {
    const next = index < 2 ? C.TIERS[index + 1].z : top + 7;
    out.push(S(k.slabOf({ x: x - 4.5, y: y - 4.5, w: 9, d: 9, r: 1 }, z + h, 7, P, 2, 0.4), { tone: "mid" }));
    if (index < 2) out.push(S(k.cylinder(x, y, 1.6, z + h + 7, next - z - h - 7, P, 14), { tone: "mid", crease: "none" }));
    out.push(D([at([x - 2.5, y + 4.5, z + h + 3.5]), at([x + 2.5, y + 4.5, z + h + 3.5])], { size: 0.4 }));
  });
  return out.join("");
}

const part = (name, inner) => `<g data-part="${name}">${inner}</g>`;
const REST = restingState();
function body(state) {
  const pens = LIVE.lanesOf(state);
  return [
    base(),
    board(),
    part("paper", LIVE.paper(state)),
    part("traces", LIVE.traces(state)),
    spool(C.SPOOL.take, "take"),
    spool(C.SPOOL.supply, "supply"),
    part("spools", LIVE.spoolMarks(state)),
    column(),
    ...C.POSTS.map((p) => post(p, C.TIERS[2].z + C.TIERS[2].h)),
    timeColumn(),
    // Bottom shelf: the integrator.
    tier(C.TIERS[0], 0),
    part("bar-2", LIVE.penBar(pens[2], 2)),
    part("rack", LIVE.rack(state)),
    station3Back(),
    part("disc", LIVE.integrator(state)),
    part("axle", LIVE.axle(state)),
    rails(),
    yokeFrame(),
    part("yoke", LIVE.yoke(state)),
    // Middle shelf: the two legs.
    tier(C.TIERS[1], 1),
    part("bar-1", LIVE.penBar(pens[1], 1)),
    station2Back(),
    part("gears", LIVE.gears(state)),
    station2Guide(),
    latchBracket(),
    part("yokes", LIVE.yokes(state)),
    switchPlate(1),
    part("switch-1", LIVE.switchKnob(1, state.unhooked)),
    // Top shelf: the finite evolution.
    tier(C.TIERS[2], 2),
    part("bar-0", LIVE.penBar(pens[0], 0)),
    station1Back(),
    part("pulley", LIVE.pulley(state)),
    part("cord", LIVE.penCord(state, pens[0])),
    part("beam", LIVE.beam(state)),
    fork(0),
    part("sphere-0", LIVE.sphere(state, 0)),
    fork(1),
    part("sphere-1", LIVE.sphere(state, 1)),
    guideBridge(),
    epsilonDial(),
    part("knob", LIVE.knob(state.a)),
    switchPlate(0),
    part("switch-0", LIVE.switchKnob(0, 1 - state.mu / Math.PI)),
  ].join("");
}

const svg = k.figureSvg({
  width: WIDTH,
  height: HEIGHT,
  className: "cw-svg",
  label:
    "A three-pen chart recorder. Paper runs across an upright board and three pens write on three lanes; each pen is driven by its own machine on a shelf of the rack beside it. Top shelf: two Bloch spheres, the window's two blocks, whose arrows precess about an axis tilted by the control ε; feelers resting on the arrow tips lift a beam, and a stepped pulley that changes step with ε divides the lift by ε. Middle shelf: two meshed gears turning opposite ways, the bra and ket legs of the state derivative, each read by a yoke into a balance bar. Bottom shelf: a disc-and-wheel integrator summing the Kubo kernel. All three pens write the curve 1 − cos 2ωt; the top one converges to it as ε shrinks. Unhooking one leg halves the middle trace; turning one sphere upright, which reads the force T instead of the current B, flattens the top trace.",
  body: body(REST),
});

const CSS = `
.iso-stage{outline:none;cursor:pointer;touch-action:pan-y}
.iso-stage:focus-visible{box-shadow:0 0 0 1px var(--anatomy-mid)}
@media (max-width:560px){.iso-plate:has(.cw-svg){overflow:hidden}.cw-svg.iso-svg{width:112%;max-width:none;margin:0 -6%}}
`;

const COPY = {
  en: {
    title: "One current, three testimonies",
    hint: "Click: alter · ← →: amplitude",
    keys: ["Traces: ωJ/(sε), the same current read three ways", "Shelves: finite evolution ÷ ε · two-leg derivative · Kubo integral", "Altered: one leg only, or the force T read for the current B"],
    refs: ["Section 1", "Theorems 8.1–8.2"],
    caption: [
      "Three machines share one clock and read the same occupied state: three testimonies to one current.",
      ["Top: ", "each block of the four-dimensional window is a Bloch sphere, and the control ε tilts the precession axis by atan(ε/ω). Feelers read the arrows’ heights; Q mounts the + block upside down, so the beam lifts by the current of B = −sQT, and the stepped pulley, one step per ε, writes ωJ_ε/(sε) = (1 − cos(2ωt√(1+ε²/ω²)))/(1+ε²/ω²)."],
      ["Middle: ", "the bra and ket legs of δu are two gears in mesh, turning opposite ways; the balance bar adds the legs and writes 1 − cos 2ωt."],
      ["Bottom: ", "a disc integrator sums the Kubo kernel 2s·sin 2ω(t−τ) and writes the same curve."],
      "As ε/ω steps from 1/2 to 1/8 the top trace closes onto the other two, the gap shrinking with ε as the remainder bound of Theorem 8.2 says.",
      "Altered testimony shows at once: drop one leg and the middle trace halves; turn the + sphere upright, which reads the force T in place of the current B, and the two blocks cancel to zero.",
    ],
    aria: "Chart recorder: arrow keys change ε/ω, click or Space alters the testimony",
    labels: { oneLeg: "one leg", readT: "read T" },
  },
  zh: {
    title: "同一电流的三份证词",
    hint: "点击：改口 · ← →：幅度",
    keys: ["迹线：ωJ/(sε)，同一电流的三种读法", "三层：有限发展 ÷ ε · 双侧求导 · Kubo 积分", "改口：只取一条腿，或用推力 T 代替电流 B 读数"],
    refs: ["§1", "定理 8.1–8.2"],
    caption: [
      "三台机器共用一个时钟，读同一个原占据态：同一电流的三份证词。",
      ["上层：", "四维窗口的两块各是一个 Bloch 球，控制 ε 把进动轴抬起 atan(ε/ω)。触杆读出箭头的高度；Q 把 + 块倒装，于是横梁的升高就是 B = −sQT 的电流，阶梯轮每个 ε 一档，笔写下 ωJ_ε/(sε) = (1 − cos(2ωt√(1+ε²/ω²)))/(1+ε²/ω²)。"],
      ["中层：", "δu 的 bra 腿与 ket 腿是两只反向啮合的齿轮，平衡杆把两腿相加，写下 1 − cos 2ωt。"],
      ["下层：", "圆盘积分器累加 Kubo 核 2s·sin 2ω(t−τ)，写下同一条曲线。"],
      "ε/ω 从 1/2 降到 1/8，上层迹线收拢到另外两条上，差距随 ε 缩小，正如定理 8.2 的余项界。",
      "改口当场露馅：只取一条腿，中层减半；把 + 块翻回正装，等于用推力 T 代替电流 B 读数，两块互相抵消，上层归零。",
    ],
    aria: "记录仪：方向键调 ε/ω，点击或空格键改口",
    labels: { oneLeg: "单腿", readT: "读 T" },
  },
};

const fmt = (x) => (Math.round(x * 1000) / 1000 || 0).toFixed(3);
function readoutOf(lang, state) {
  const labels = COPY[lang].labels;
  const pens = LIVE.lanesOf(state).map((z, lane) => (z - C.LANES[lane]) / C.GAIN);
  return `ε/ω 1/${Math.round(1 / state.a)} · ωt ${state.x.toFixed(2)} · ${fmt(pens[0])} · ${fmt(pens[1])} · ${fmt(pens[2])}${state.mode === "honest" ? "" : " · " + labels[state.mode]}`;
}

const bodyOf = (lang) => {
  const copy = COPY[lang];
  return `<div data-figure="current-witness" data-labels='${JSON.stringify(copy.labels)}'>${k.plateHtml({
    fig: "Fig 8.2",
    title: copy.title,
    hint: copy.hint,
    readout: readoutOf(lang, REST),
    keys: [
      { mark: "lit", label: copy.keys[0] },
      { mark: "raised", label: copy.keys[1] },
      { mark: "dim", label: copy.keys[2] },
    ],
    caption: copy.caption,
    refs: copy.refs,
    body: `<div class="iso-stage" tabindex="0" role="slider" aria-label="${copy.aria}" aria-valuemin="0" aria-valuemax="${M.AMPLITUDES.length - 1}" aria-valuenow="${M.AMPLITUDES.indexOf(REST.a)}">${svg}</div>`,
  })}</div>`;
};

const strip = (file) => readFileSync(join(HERE, file), "utf8").replace(/^export /gm, "");
const kitSource = strip("../kit/iso-kit.mjs");
// lathe.mjs and the model share helper names with the core, so each lives in its own scope.
const latheSource = `const LATHE = (() => {\n${strip("../kit/lathe.mjs").replace(/^import .*$/gm, "")}\nreturn { disc, frameOf, frameAlong, sphereOf, prismOf, spokesOf, circleOf };\n})();`;
const modelSource = `const MODEL = (() => {\n${strip("model.mjs")}\nreturn { bloch, testimony, AMPLITUDES, MODES };\n})();`;
const round = (x) => Math.round(x * 100) / 100;
const restJson = JSON.stringify({ ...REST, runs: REST.runs.map((run) => ({ ...run, p0: round(run.p0), samples: run.samples.map(({ p, z }) => ({ p: round(p), z: z.map(round) })) })) });
const live = `
const P = ${JSON.stringify(P)};
const C = ${JSON.stringify(C)};
const kit = { iso, depthOf, pathOf, solidSvg, lineSvg, dotsSvg, segment, slabOf, cylinder, lineOnTop, knurl };
const LIVE = (${makeLive.toString()})(kit, LATHE, P, C, MODEL);
const root = document.querySelector('[data-figure="current-witness"]');
const stage = root.querySelector(".iso-stage");
const readout = root.querySelector("[data-readout]");
const labels = JSON.parse(root.dataset.labels);
const parts = {};
for (const node of stage.querySelectorAll("[data-part]")) parts[node.dataset.part] = node;
const still = matchMedia("(prefers-reduced-motion: reduce)");
const A = MODEL.AMPLITUDES;
// The tour: ε/ω steps down, then the two altered testimonies.
const TOUR = [[A[0], "honest"], [A[1], "honest"], [A[2], "honest"], [A[2], "oneLeg"], [A[2], "readT"]];
const RATE = 1.05; // ωt per second
const ease = (f) => f * f * (3 - 2 * f);
let state = ${restJson};
state.reset = null;
let phase = "gap", gapT = 0, tourAt = 3, pending = { a: state.a, mode: "oneLeg" }, fromTilt = state.a, sampleX = 0;
let touring = !still.matches, visible = false, frame = 0, last = 0, idle = 0;
const fmt = (x) => (Math.round(x * 1000) / 1000 || 0).toFixed(3);
function say() {
  const pens = LIVE.lanesOf(state).map((z, lane) => (z - C.LANES[lane]) / C.GAIN);
  const text = "ε/ω 1/" + Math.round(1 / state.a) + " · ωt " + state.x.toFixed(2) + " · " + fmt(pens[0]) + " · " + fmt(pens[1]) + " · " + fmt(pens[2]) + (state.mode === "honest" ? "" : " · " + labels[state.mode]);
  if (readout.textContent !== text) readout.textContent = text;
  stage.setAttribute("aria-valuetext", text);
  stage.setAttribute("aria-valuenow", String(A.indexOf(state.a)));
}
function draw() {
  const pens = LIVE.lanesOf(state);
  const set = (name, html) => { parts[name].innerHTML = html; };
  set("paper", LIVE.paper(state));
  set("traces", LIVE.traces(state));
  set("spools", LIVE.spoolMarks(state));
  pens.forEach((z, lane) => set("bar-" + lane, LIVE.penBar(z, lane)));
  set("rack", LIVE.rack(state));
  set("disc", LIVE.integrator(state));
  set("axle", LIVE.axle(state));
  set("yoke", LIVE.yoke(state));
  set("gears", LIVE.gears(state));
  set("yokes", LIVE.yokes(state));
  set("pulley", LIVE.pulley(state));
  set("cord", LIVE.penCord(state, pens[0]));
  set("beam", LIVE.beam(state));
  set("sphere-0", LIVE.sphere(state, 0));
  set("sphere-1", LIVE.sphere(state, 1));
  set("knob", LIVE.knob(state.a));
  set("switch-0", LIVE.switchKnob(0, 1 - state.mu / Math.PI));
  set("switch-1", LIVE.switchKnob(1, state.unhooked));
  say();
}
function startRun() {
  phase = "run";
  state.x = 0;
  state.reset = null;
  state.tilt = state.a;
  state.mode = pending.mode;
  state.runs.push({ a: state.a, mode: state.mode, p0: state.paper, samples: [] });
  sampleX = -1;
}
function startGap(next) {
  phase = "gap";
  gapT = 0;
  state.reset = { a: state.a, f: 0 };
  fromTilt = state.a;
  pending = next;
}
function nextRun() {
  if (!touring) return { a: state.a, mode: state.mode };
  const [a, mode] = TOUR[tourAt++ % TOUR.length];
  return { a, mode };
}
function record() {
  const run = state.runs[state.runs.length - 1];
  if (!run || state.x - sampleX < 0.03) return;
  sampleX = state.x;
  run.samples.push({ p: state.paper, z: LIVE.lanesOf(state) });
}
function step(dt) {
  const dx = dt * RATE;
  state.paper += dx * C.PAPER_V;
  state.discTurn += dx * C.OMEGA_DISC;
  const want = { mu: state.mode === "readT" ? 0 : Math.PI, unhooked: state.mode === "oneLeg" ? 1 : 0 };
  state.mu += (want.mu - state.mu) * (1 - Math.exp(-dt / 0.22));
  state.unhooked += (want.unhooked - state.unhooked) * (1 - Math.exp(-dt / 0.06));
  if (phase === "run") {
    state.x = Math.min(C.RUN, state.x + dx);
    record();
    if (state.x >= C.RUN) startGap(nextRun());
  } else {
    gapT += dx;
    const f = Math.min(1, gapT / (C.GAP / 2));
    state.reset.f = ease(f);
    if (gapT >= C.GAP / 2) {
      state.a = pending.a;
      state.mode = pending.mode;
      const g = Math.min(1, (gapT - C.GAP / 2) / (C.GAP / 2));
      state.tilt = fromTilt + (pending.a - fromTilt) * ease(g);
    }
    if (gapT >= C.GAP) startRun();
  }
  // Runs that have left the board.
  const edge = state.paper - (C.X_PEN - C.BOARD.x);
  while (state.runs.length > 1 && state.runs[0].samples.length && state.runs[0].samples[state.runs[0].samples.length - 1].p < edge) state.runs.shift();
}
function tick(time) {
  const dt = last ? Math.min((time - last) / 1000, 1 / 30) : 1 / 60;
  last = time;
  step(dt);
  draw();
  frame = visible && !still.matches ? requestAnimationFrame(tick) : 0;
}
const run = () => { if (!frame && visible && !still.matches) { last = 0; frame = requestAnimationFrame(tick); } };
const hold = () => { touring = false; clearTimeout(idle); idle = setTimeout(() => { touring = !still.matches; }, 9000); };
// Under reduced motion every change writes a whole run at once.
function instant() {
  if (phase === "gap") { state.a = pending.a; state.mode = pending.mode; state.tilt = state.a; startRun(); }
  while (phase === "run") step(0.05);
  state.reset = null;
  state.x = C.RUN;
  state.mu = state.mode === "readT" ? 0 : Math.PI;
  state.unhooked = state.mode === "oneLeg" ? 1 : 0;
  draw();
}
const MODES = MODEL.MODES;
function alter() {
  hold();
  const mode = MODES[(MODES.indexOf(phase === "gap" ? pending.mode : state.mode) + 1) % MODES.length];
  if (phase === "gap") pending.mode = mode; else state.mode = mode;
  if (still.matches) { pending = { a: state.a, mode }; startGap(pending); instant(); }
  run();
}
function retune(direction) {
  hold();
  const index = Math.min(A.length - 1, Math.max(0, A.indexOf(phase === "gap" ? pending.a : state.a) + direction));
  const mode = phase === "gap" ? pending.mode : state.mode;
  if (phase === "run") startGap({ a: A[index], mode }); else pending.a = A[index];
  if (still.matches) instant();
  run();
}
stage.addEventListener("keydown", (event) => {
  if (event.key === "ArrowRight" || event.key === "ArrowDown") retune(1);
  else if (event.key === "ArrowLeft" || event.key === "ArrowUp") retune(-1);
  else if (event.key === " " || event.key === "Enter") alter();
  else return;
  event.preventDefault();
});
stage.addEventListener("click", alter);
new IntersectionObserver((entries) => { visible = entries[entries.length - 1].isIntersecting; if (visible) run(); }, { rootMargin: "120px 0px" }).observe(stage);
// Motion resumes the tour after the resting run; without motion the shown run stays the current one.
if (still.matches) pending = { a: state.a, mode: state.mode };
startGap(pending);
state.reset = { a: state.a, f: 0 };
say();
`;

const script = `{\n${kitSource}\n${latheSource}\n${modelSource}\n${live}\n}`.replace(/<\/(script)/gi, "<\\/$1");
if (fragment) {
  const outDir = join(HERE, "../../src/generated");
  mkdirSync(outDir, { recursive: true });
  writeFileSync(join(outDir, "current-witness.json"), JSON.stringify({ html: { zh: bodyOf("zh"), en: bodyOf("en") }, css: CSS, script }));
  console.log("wrote src/generated/current-witness.json");
} else {
  mkdirSync(join(HERE, "out"), { recursive: true });
  const name = theme === "light" ? "current-witness-light.html" : "current-witness.html";
  const lang = process.argv.includes("--zh") ? "zh" : "en";
  writeFileSync(join(HERE, "out", name), k.pageHtml({ title: COPY[lang].title, theme, body: `<style>${CSS}</style>${bodyOf(lang)}`, script, width: 760 }));
  console.log("wrote out/" + name);
}
