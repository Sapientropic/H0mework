// Fig: a cash register that admits one input, its crank, and a coin on the counter beside it
// (Proposition 2.3, Lemma 2.2 and Theorem 2.6 of "1 Bit Is All You Need").
//   bun build.mjs [--light] [--zh] → out/ghost-register[-light].html (standalone, for checks)
//   bun build.mjs --fragment       → ../../src/generated/ghost-register.json (for the site)
import { mkdirSync, readFileSync, writeFileSync } from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";
import * as k from "../kit/iso-kit.mjs";
import * as G from "../kit/lathe.mjs";
import * as M from "./model.mjs";
import { shipped, SWING_CSS, swingSource } from "../swing.mjs";

const HERE = dirname(fileURLToPath(import.meta.url));
const theme = process.argv.includes("--light") ? "light" : "dark";
const fragment = process.argv.includes("--fragment");

const WIDTH = 640;

// World: x along the counter, y toward the viewer, z up. The register's front faces +y, its crank +x.
const C = {
  PLATE: { x: -158, y: -82, w: 250, d: 166, r: 8 },
  PLATE_H: 10,
  FOOT_H: 5,
  PLINTH: { x: -134, y: -66, w: 128, d: 96, r: 3 },
  CAB: { x: -132, y: -64, w: 124, d: 92, r: 2.5 },
  UPPER: { x: -128, y: -62, w: 116, d: 76, r: 3 },
  CAP: { x: -130, y: -64, w: 120, d: 80, r: 3.5 },
  Z: { foot: 4.4, plinth: 9, cab: 43, upper: 100, cap: 104.5 },
  // The till: an opening in the cabinet front, a drawer front proud of it, a tray behind.
  DRAWER: { x0: -126, x1: -14, z0: 12, z1: 40, gap: 0.7, t: 2, wall: 1.2, tray: 17, open: 40, cups: 28 },
  JOURNAL: { x0: -120, x1: -92, z0: 50, z1: 92, r: 2.4, depth: 6, pitch: 5, print: 60 },
  COUNTER: { x0: -82, x1: -38, z0: 75.5, z1: 86.5, r: 1.8, depth: 3, drum: 9.5 },
  NAME: { x0: -80, x1: -40, z0: 58, z1: 65 },
  // The crank turns on the register's +x side; one turn is one step of the root.
  CRANK: { y: -24, z: 68, len: 23, teeth: 12 },
  // The marquee on top shows the admitted state on a pop-up tab behind glass.
  MARQUEE: { x0: -100, x1: -48, y0: -44, y1: -24, z0: 104.5, base: 3, z1: 128, cap: 3.2 },
  BELL: { x: -28, y: -4, r: 8.4 },
  MAT: { x: 14, y: 6, w: 64, d: 60, r: 7 },
  COIN: { x: 46, y: 36, r: 12, t: 2.4 },
};
C.FRONT = C.CAB.y + C.CAB.d; // 28: the cabinet front
C.UFRONT = C.UPPER.y + C.UPPER.d; // 14: the upper case front
C.SIDE = C.UPPER.x + C.UPPER.w; // -12: the upper case side, where the crank sits

const FIT = [
  ...k.boxCorners(C.PLATE, -C.PLATE_H - C.FOOT_H, 0),
  ...k.boxCorners(C.CAP, C.Z.cap, C.Z.cap),
  [C.BELL.x, C.BELL.y, C.Z.cap + 18],
  ...k.boxCorners({ x: C.MARQUEE.x0, y: C.MARQUEE.y0, w: C.MARQUEE.x1 - C.MARQUEE.x0, d: C.MARQUEE.y1 - C.MARQUEE.y0 }, C.MARQUEE.z1 + C.MARQUEE.cap, C.MARQUEE.z1 + C.MARQUEE.cap),
  [C.COIN.x, C.COIN.y, 50],
];
const VIEW = { pad: 16, azimuth: 58, elevation: 30 };
const HEIGHT = (() => {
  const wide = k.fitProjection(FIT, WIDTH, 10000, VIEW);
  const ys = FIT.map((point) => k.iso(point, wide)[1]);
  return Math.ceil(Math.max(...ys) - Math.min(...ys) + 2 * VIEW.pad);
})();
const P = k.fitProjection(FIT, WIDTH, HEIGHT, VIEW);
// The page swings the view (../swing.mjs), framed by the same fit, and redraws `composition` there.
const FRAME = { points: FIT, width: WIDTH, height: HEIGHT, pad: VIEW.pad };

// --- live drawing: one factory shared by the build (first frame) and the page --------------

function makeLive(k, G, P, C, M) {
  const at = (p) => k.iso(p, P);
  const S = (paths, style) => k.solidSvg(paths, style);
  const L = (d, style) => k.lineSvg(d, style);
  const D = (points, style) => k.dotsSvg(points, style);
  // Stone (kit iso.css, data-mat): a group remaps the tone ramp of what it holds.
  const stone = (material, ...svg) => `<g data-mat="${material}">${svg.join("")}</g>`;
  const V = G.viewOf(P);
  const X = [1, 0, 0], Y = [0, 1, 0], Z = [0, 0, 1];
  const TAU = Math.PI * 2;
  const dot = (a, b) => a[0] * b[0] + a[1] * b[1] + a[2] * b[2];
  const add = (a, b) => [a[0] + b[0], a[1] + b[1], a[2] + b[2]];
  const mul = (s, a) => [s * a[0], s * a[1], s * a[2]];
  const cross = (a, b) => [a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]];
  const unit = (v) => { const n = Math.hypot(v[0], v[1], v[2]) || 1; return [v[0] / n, v[1] / n, v[2] / n]; };
  const n2 = (v) => v.toFixed(2);
  // An affine map from a plane (origin o, unit axes u right and w down) onto the screen.
  const planeMatrix = (o, u, w) => {
    const O = at(o), U = at(add(o, u)), W = at(add(o, w));
    return `matrix(${n2(U[0] - O[0])} ${n2(U[1] - O[1])} ${n2(W[0] - O[0])} ${n2(W[1] - O[1])} ${n2(O[0])} ${n2(O[1])})`;
  };
  // The front planes: local (x, −z) on a face that looks along +y.
  const front = (y) => planeMatrix([0, y, 0], X, [0, 0, -1]);
  const box = (x0, y0, z0, x1, y1, z1, r = 0.4, steps = 3) => k.slabOf({ x: x0, y: y0, w: x1 - x0, d: y1 - y0, r }, z0, z1 - z0, P, steps);
  const rect = (u0, v0, u1, v1, r = 0, steps = 4) => k.pathOf(k.roundedPlan({ x: u0, y: v0, w: u1 - u0, d: v1 - v0, r }, steps), true);

  // Paints are inline so the drawing reads the same wherever its SVG is shown on its own (the home cards).
  const PAINT = {
    well: "fill:var(--anatomy-shade-1)",
    dark: "fill:var(--anatomy-shade-0)",
    paper: "fill:var(--anatomy-face)",
    drum: "fill:var(--anatomy-face)",
    "drum-shade": "fill:var(--anatomy-shade-1);opacity:.75",
    roller: "fill:var(--anatomy-shade-2)",
    ribbon: "fill:var(--anatomy-shade-0)",
    hole: "fill:var(--anatomy-mid)",
    digit: "fill:var(--anatomy-hi);font-family:ui-sans-serif,system-ui,-apple-system,sans-serif;font-variant-numeric:tabular-nums;font-weight:500",
    "digit-lit": "fill:var(--anatomy-lit);font-family:ui-sans-serif,system-ui,-apple-system,sans-serif;font-variant-numeric:tabular-nums;font-weight:500",
    print: "fill:var(--anatomy-mid);font-family:var(--anatomy-mono);letter-spacing:.02em",
    "print-lit": "fill:var(--anatomy-lit);font-family:var(--anatomy-mono);letter-spacing:.02em",
    numeral: "fill:none;stroke:var(--anatomy-hi);stroke-width:1.15px;stroke-linecap:round;stroke-linejoin:round",
    shadow: "fill:var(--anatomy-halo);filter:blur(2.5px)",
    tab: "fill:var(--anatomy-hi);font-family:var(--anatomy-mono);font-weight:500",
  };

  // --- the crank: ratchet, pawl, hub, arm and grip, all turning about +x at the boss -------
  const CR = C.CRANK;
  const HUB = [C.SIDE, CR.y, CR.z];
  // Angle 0 points up and angles grow toward +y: clockwise seen from the crank's side.
  const dirOf = (a) => [0, Math.sin(a), Math.cos(a)];
  const F0 = G.frameOf(HUB, X, Z, Y);
  // Along the shaft from the case side: boss 0–1.6, ratchet 1.6–3.4, spacer, cam 4.4–6, hub, arm, pin, grip.
  const R_ROOT = 5.3, R_TIP = 6.5, S_WHEEL = [1.6, 3.4], S_CAM = [4.4, 6], S_HUB = [6, 8.4], S_ARM = [8.4, 10.4];
  const PAWL = { a: -0.98, r: 10.6, tip: -0.34 };
  const pivot = G.pointOf(F0, 0, PAWL.r, PAWL.a);
  const PAWL_PIN = G.pointOf(F0, 0, 13.4, -0.62);
  function toothAt(a) {
    // Each tooth ramps up from root to tip as the wheel turns forward, then drops: a pawl rides it and falls.
    const span = TAU / CR.teeth;
    return ((a % span) + span) % span / span;
  }
  // The trip cam: a base circle and one lobe. The lobe reaches straight down near the end of the turn,
  // pushing the trip rod that tips the drawer's latch lever; at rest it is turned well clear.
  const CAM = { base: 4.2, lobe: 0.8, reach: 6.2, at: 1.36 * Math.PI };
  const camAngle = (theta) => CAM.at + theta;
  const camPolygon = (theta) => {
    const circle = (cx, cy, r, n) => Array.from({ length: n }, (_, i) => [cx + r * Math.cos((i / n) * TAU), cy + r * Math.sin((i / n) * TAU)]);
    const a = camAngle(theta);
    return G.hullOf([...circle(0, 0, CAM.base, 40), ...circle(CAM.reach * Math.cos(a), CAM.reach * Math.sin(a), CAM.lobe, 16)]);
  };
  // How far the cam pushes the rod down: its support below the shaft, less the base circle.
  const dropAt = (theta) => Math.max(0, -CAM.reach * Math.cos(camAngle(theta)) + CAM.lobe - CAM.base);
  function crankBack(theta) {
    const out = [];
    const span = TAU / CR.teeth;
    const teeth = [];
    for (let i = 0; i < CR.teeth; i++) {
      const a0 = theta + i * span;
      const poly = [
        [R_ROOT * Math.cos(a0), R_ROOT * Math.sin(a0)],
        [R_TIP * Math.cos(a0 - span * 0.82), R_TIP * Math.sin(a0 - span * 0.82)],
        [R_ROOT * Math.cos(a0 - span), R_ROOT * Math.sin(a0 - span)],
        [(R_ROOT - 0.6) * Math.cos(a0 - span * 0.5), (R_ROOT - 0.6) * Math.sin(a0 - span * 0.5)],
      ];
      const mid = a0 - span * 0.6;
      const facing = dot(G.radialOf(F0, mid), V);
      teeth.push({ facing, svg: stone("jade", S(G.prismOf(F0, poly, S_WHEEL[0], S_WHEEL[1], P), { tone: "mid" })) });
    }
    teeth.sort((a, b) => a.facing - b.facing);
    teeth.filter((t) => t.facing < 0).forEach((t) => out.push(t.svg));
    out.push(stone("jade", S(G.disc(S_WHEEL[0], S_WHEEL[1], R_ROOT, F0, P), { tone: "mid" })));
    teeth.filter((t) => t.facing >= 0).forEach((t) => out.push(t.svg));
    // The pawl rides the tooth under its tip; the wheel can only go forward.
    const ride = toothAt(PAWL.tip - theta + span * 0.18);
    const lift = 0.16 * Math.min(1, ride / 0.82);
    const tip = G.pointOf(F0, 0, R_TIP - 0.1, PAWL.tip);
    const base = Math.atan2(tip[1] - pivot[1], tip[2] - pivot[2]);
    const along = base - lift;
    const length = Math.hypot(tip[1] - pivot[1], tip[2] - pivot[2]);
    const FP = G.frameOf([C.SIDE, pivot[1], pivot[2]], X, [0, Math.sin(along), Math.cos(along)], [0, Math.cos(along), -Math.sin(along)]);
    out.push(stone("ink", S(G.prismOf(FP, G.stadium(1.7, 0.6, length, 20), S_WHEEL[0], S_WHEEL[1], P), { tone: "hi" })));
    out.push(S(G.disc(S_WHEEL[1], S_WHEEL[1] + 0.7, 1.1, G.frameOf([C.SIDE, pivot[1], pivot[2]], X, Z, Y), P), { tone: "mid" }));
    // The pawl's spring: from a pin on the case down to the pawl's back, holding its tip on the teeth.
    const sMid = (S_WHEEL[0] + S_WHEEL[1]) / 2;
    const hook = [C.SIDE + sMid, pivot[1] + 2.6 * Math.sin(along), pivot[2] + 2.6 * Math.cos(along) + 1.2];
    const pin = [C.SIDE + sMid, PAWL_PIN[1], PAWL_PIN[2]];
    const axis = unit([0, hook[1] - pin[1], hook[2] - pin[2]]);
    const side = cross(X, axis);
    const span3 = Math.hypot(hook[1] - pin[1], hook[2] - pin[2]);
    const coilPts = Array.from({ length: 73 }, (_, i) => {
      const t = i / 72, phi = t * 8 * TAU, end = t < 0.12 || t > 0.88 ? 0 : 0.75;
      return add(add(pin, mul(span3 * t, axis)), add(mul(end * Math.cos(phi), X), mul(end * Math.sin(phi), side)));
    });
    out.push(L(k.pathOf(coilPts.map(at)), { tone: "mid" }));
    return out.join("");
  }
  function crankFront(theta) {
    const out = [];
    out.push(S(G.disc(S_WHEEL[1], S_CAM[0], 2.6, F0, P), { tone: "mid" }));
    out.push(stone("ink", S(G.prismOf(F0, camPolygon(theta), S_CAM[0], S_CAM[1], P), { tone: "hi" })));
    // The hub, its set screw turning with it.
    out.push(stone("jade", S(G.disc(S_HUB[0], S_HUB[1], 3.5, F0, P), { tone: "mid", inner: L(G.arcOf(F0, S_HUB[0] + 1.2, 3.5, P), { tone: "faint" }) })));
    out.push(D([at(G.pointOf(F0, S_HUB[1], 2.1, theta + Math.PI))], { size: 0.45, tone: "mid" }));
    const d = dirOf(theta);
    const FA = G.frameOf(HUB, X, d, dirOf(theta + Math.PI / 2));
    out.push(stone("ink", S(G.prismOf(FA, G.stadium(3.3, 2.1, CR.len, 28), S_ARM[0], S_ARM[1], P), { tone: "mid" })));
    const end = add(HUB, mul(CR.len, d));
    const FE = G.frameOf(end, X, Z, Y);
    out.push(S(G.disc(S_ARM[1], S_ARM[1] + 1.2, 1.2, FE, P), { tone: "mid" }));
    // The grip: a turned handle, r(s) = 1.75 + 1.05·sin(π t) along its 11.4 units.
    const g0 = S_ARM[1] + 1.2, gl = 11.4;
    const radius = (s) => 1.75 + 1.05 * Math.sin((Math.PI * (s - g0)) / gl);
    const slope = (s) => ((1.05 * Math.PI) / gl) * Math.cos((Math.PI * (s - g0)) / gl);
    const profile = Array.from({ length: 13 }, (_, i) => { const s = g0 + (gl * i) / 12; return [s, radius(s), 1]; });
    profile[0][2] = 0;
    profile[12][2] = 0;
    out.push(stone("jade", S(G.solidOf(profile, FE, P, { smooth: { slope, radius } }), { tone: "hi" })));
    return out.join("");
  }

  // --- the trip: a rod riding the cam down to the latch lever on the cabinet side ------------
  const ROD = { x: C.SIDE + (S_CAM[0] + S_CAM[1]) / 2, y: CR.y, r: 0.7, roller: 1.3 };
  const LEVER = { y: CR.y + 10.5, z: 34.4, back: 10.5, front: 9.5, half: 1.4, s: [0.2, 1.4] };
  const BRACKET = { z0: 49.5, z1: 52.5 };
  const rollerZ = (drop) => CR.z - CAM.base - ROD.roller - drop;
  const ROD_LEN = rollerZ(0) - (LEVER.z + LEVER.half);
  const COLLAR = 57.5;
  const cabSide = C.CAB.x + C.CAB.w;
  function helix(z0, z1, r, turns) {
    // A coil round the rod, split into the halves behind and in front of it.
    const back = [], front = [];
    const n = Math.max(24, Math.round(turns * 20));
    let run = [], side = null;
    for (let i = 0; i <= n; i++) {
      const t = (i / n) * turns * TAU;
      const p = [ROD.x + r * Math.cos(t), ROD.y + r * Math.sin(t), z0 + ((z1 - z0) * i) / n];
      const now = Math.cos(t) * V[0] + Math.sin(t) * V[1] >= 0;
      if (side !== null && now !== side) { run.push(p); (side ? front : back).push(k.pathOf(run.map(at))); run = []; }
      run.push(p);
      side = now;
    }
    (side ? front : back).push(k.pathOf(run.map(at)));
    return { back: back.join(""), front: front.join("") };
  }
  const FROD = (z) => G.frameOf([ROD.x, ROD.y, z], Z, X, Y);
  function tripLow(theta) {
    // The lever, tipped by the rod's drop, and the rod from the lever up to the bracket.
    const drop = dropAt(theta);
    const psi = Math.asin(Math.min(1, drop / LEVER.back));
    const A = [cabSide, LEVER.y - LEVER.back * Math.cos(psi), LEVER.z - LEVER.back * Math.sin(psi)];
    const B = [cabSide, LEVER.y + LEVER.front * Math.cos(psi), LEVER.z + LEVER.front * Math.sin(psi)];
    const u = unit([0, B[1] - A[1], B[2] - A[2]]);
    const FL = G.frameOf(A, X, u, cross(X, u));
    const out = [];
    out.push(stone("jade", S(G.prismOf(FL, G.stadium(LEVER.half, LEVER.half, LEVER.back + LEVER.front, 20), LEVER.s[0], LEVER.s[1], P), { tone: "hi" })));
    const FP = G.frameOf([cabSide, LEVER.y, LEVER.z], X, Z, Y);
    out.push(S(G.disc(LEVER.s[1], LEVER.s[1] + 0.8, 0.95, FP, P), { tone: "mid" }));
    const bottom = rollerZ(drop) - ROD_LEN;
    out.push(S(G.disc(0, BRACKET.z0 - bottom, ROD.r, FROD(bottom), P), { tone: "mid" }));
    return out.join("");
  }
  function tripHigh(theta) {
    // Above the bracket: the return spring, the collar, the rod and the roller on the cam.
    const drop = dropAt(theta);
    const collar = COLLAR - drop;
    const coil = helix(BRACKET.z1, collar - 0.5, 1.55, 5);
    const out = [L(coil.back, { tone: "lo" })];
    out.push(S(G.disc(0, rollerZ(drop) - BRACKET.z1, ROD.r, FROD(BRACKET.z1), P), { tone: "mid" }));
    out.push(L(coil.front, { tone: "mid" }));
    out.push(stone("ink", S(G.disc(-0.5, 0.5, 1.9, FROD(collar), P), { tone: "mid" })));
    const FR = G.frameOf([C.SIDE, ROD.y, rollerZ(drop)], X, Z, Y);
    out.push(stone("jade", S(G.disc(S_CAM[0] + 0.1, S_CAM[1] - 0.1, ROD.roller, FR, P), { tone: "mid", inner: L(G.circleOf(FR, S_CAM[1] - 0.1, 0.5, P), { tone: "lo" }) })));
    return out.join("");
  }

  // --- the till: drawer front, pull and lock, and the tray behind them ----------------------
  const DR = C.DRAWER;
  function drawer(open) {
    const out = [];
    const y = C.FRONT + open;
    const x0 = DR.x0 + DR.gap, x1 = DR.x1 - DR.gap, z0 = DR.z0 + DR.gap, z1 = DR.z1 - DR.gap;
    if (open > 0.15) {
      const w0 = x0 + 1.2, w1 = x1 - 1.2, f0 = z0 + 0.8, f1 = f0 + DR.tray;
      out.push(S(box(w0, C.FRONT, f0, w1, y, f0 + 0.8), { tone: "lo", crease: "none" }));
      // Compartments: a cross wall, then cups for coin between it and the drawer front.
      const cross = y - DR.cups;
      const cups = 5;
      if (cross > C.FRONT) out.push(S(box(w0 + DR.wall, cross - 0.5, f0 + 0.8, w1 - DR.wall, cross + 0.5, f1 - 2.5), { tone: "lo" }));
      out.push(S(box(w0, C.FRONT, f0, w0 + DR.wall, y, f1), { tone: "mid" }));
      for (let i = 1; i < cups; i++) {
        const xi = w0 + DR.wall + ((w1 - w0 - 2 * DR.wall) * i) / cups;
        const yy = Math.max(C.FRONT, cross);
        if (y - yy > 0.6) out.push(S(box(xi - 0.45, yy, f0 + 0.8, xi + 0.45, y, f1 - 2.5), { tone: "lo" }));
      }
      out.push(S(box(w1 - DR.wall, C.FRONT, f0, w1, y, f1), { tone: "mid" }));
    }
    const panel = box(x0, y, z0, x1, y + DR.t, z1, 0.6);
    const face = y + DR.t;
    const mould = `<g transform="${front(face)}">${L(rect(x0 + 4, -(z1 - 4), x1 - 4, -(z0 + 4), 1.2), { tone: "faint" })}${L(rect(x0 + 5.4, -(z1 - 5.4), x1 - 5.4, -(z0 + 5.4), 0.8), { tone: "faint" })}</g>`;
    out.push(`<g data-part="drawer">${S(panel, { tone: "mid", inner: mould })}`);
    // The pull: two posts and a round bar.
    const pz = 28.5, px = [-88, -58];
    const bar = add([0, 0, 0], [0, face + 3.6, pz]);
    for (const x of px) out.push(stone("ink", S(G.disc(0, 3.6 - 0.62, 1.05, G.frameOf([x, face, pz], Y, Z, X), P), { tone: "mid" })));
    out.push(stone("jade", S(G.disc(px[0] - 3, px[1] + 3, 1.25, G.frameOf([0, bar[1], pz], X, Z, Y), P), { tone: "hi" })));
    // The lock: an escutcheon and its keyhole. The bolt behind it holds the drawer until the crank releases it.
    const lock = [-30, face, 28];
    out.push(stone("jade", S(G.disc(0, 0.7, 3.3, G.frameOf(lock, Y, Z, X), P), { tone: "mid", inner: L(G.circleOf(G.frameOf(lock, Y, Z, X), 0.7, 2.4, P), { tone: "faint" }) })));
    const hole = `M${-0.75} ${-1.6}A0.95 0.95 0 1 1 ${0.75} ${-1.6}L0.5 0.9H-0.5Z`;
    out.push(`<g transform="${planeMatrix([lock[0], face + 0.72, lock[2]], X, [0, 0, -1])}"><path style="${PAINT.hole}" d="${hole}"/></g>`);
    out.push(D([at([x0 + 2.4, face, z1 - 2.4]), at([x1 - 2.4, face, z1 - 2.4]), at([x0 + 2.4, face, z0 + 2.4]), at([x1 - 2.4, face, z0 + 2.4])], { size: 0.4 }));
    out.push(`</g>`);
    return out.join("");
  }

  // --- the coin: a disc with a reeded edge, a beaded border and a numeral on each face -------
  const CO = C.COIN;
  // pose: centre, unit axis a (the 0 face's normal), and u, a unit vector in the coin's plane.
  function coin(pose) {
    const { c, a, u } = pose;
    const v = cross(a, u);
    const F = G.frameOf(c, a, u, v);
    const out = [];
    const hT = CO.t / 2;
    // A soft shadow on the mat, fainter and wider the higher the coin is.
    const lift = Math.max(0, c[2] - 1.4 - hT);
    if (lift > 0.6) out.push(`<path style="${PAINT.shadow};opacity:${n2(0.5 / (1 + lift / 14))}" d="${k.pathOf(Array.from({ length: 40 }, (_, i) => at([c[0] + (CO.r + lift * 0.08) * Math.cos((i / 40) * TAU), c[1] + (CO.r + lift * 0.08) * Math.sin((i / 40) * TAU), 1.45])), true)}"/>`);
    const ribs = G.ribsOf(F, -hT, hT, CO.r, 64, P, { fade: [0.1, 0.55] });
    out.push(stone("jade", S(G.disc(-hT, hT, CO.r, F, P), { tone: "hi", inner: k.fadedSvg(ribs, { tone: "lo" }) })));
    const facing = dot(a, V);
    if (Math.abs(facing) > 0.04) {
      const sgn = facing > 0 ? 1 : -1;
      const s = sgn * hT;
      out.push(L(G.circleOf(F, s, CO.r - 1.15, P), { tone: "lo" }));
      out.push(D(G.dotsOf(F, s, CO.r - 2, 40, P, { all: true }), { size: 0.32, tone: "mid" }));
      const o = add(c, mul(s, a));
      // The kit's view is mirrored (x × y points away from the viewer), so a face reads right way round
      // with right = u and down = v on the 0 face, down = −v on the 1 face.
      const m = planeMatrix(o, u, sgn > 0 ? v : mul(-1, v));
      // Engraved numerals, drawn as strokes: 0 on one face, 1 on the other.
      const glyph = sgn > 0 ? "M0 -4.4C2.5 -4.4 3 -2.2 3 0S2.5 4.4 0 4.4-3 2.2-3 0-2.5-4.4 0-4.4Z" : "M-1.6 -2.6L0.6 -4.4V4.4M-2 4.4H2.6";
      out.push(`<g transform="${m}"><path style="${PAINT.numeral}" d="${glyph}"/></g>`);
    }
    return `<g data-part="coin">${out.join("")}</g>`;
  }

  // --- the bell striker: an arm on a post that swings into the bell's skirt -----------------
  const BE = C.BELL;
  // The striker's post stands BEAT_R from the bell's axis, behind it; its arm touches the skirt when aimed at the axis.
  const BEAT = 0.25, BEAT_R = 15.1;
  const POST = [BE.x + BEAT_R * Math.cos(BEAT), BE.y + BEAT_R * Math.sin(BEAT), C.Z.cap];
  const ARM_Z = C.Z.cap + 9.4;
  function striker(swing) {
    // swing 0 at rest, 1 at the bell.
    const a = BEAT + 0.36 * (1 - swing);
    const d = [-Math.cos(a), -Math.sin(a), 0];
    const from = [POST[0], POST[1], ARM_Z];
    const ball = add(from, mul(6.4, d));
    const out = [];
    out.push(S(G.disc(0, 6.4 - 1.25, 0.45, G.frameAlong(from, d), P), { tone: "mid" }));
    out.push(stone("jade", S(G.sphereOf(ball, 1.5, P), { tone: "hi" })));
    out.push(stone("ink", S(k.cylinder(POST[0], POST[1], 1.25, ARM_Z - 0.9, 1.8, P, 16), { tone: "mid" })));
    return out.join("");
  }

  // --- the counter: four number wheels behind a window, rolling like an odometer ------------
  const CN = C.COUNTER;
  const cells = M.DIGITS;
  function counter(value) {
    const cellW = (CN.x1 - CN.x0) / cells;
    const zc = (CN.z0 + CN.z1) / 2;
    const whole = Math.floor(value + 1e-9);
    const frac = value - whole;
    const out = [];
    for (let i = 0; i < cells; i++) {
      const place = 10 ** (cells - 1 - i);
      const lower = whole % place;
      const carrying = place === 1 || lower === place - 1;
      const p = (Math.floor(whole / place) % 10) + (carrying ? frac : 0);
      const xc = CN.x0 + cellW * (i + 0.5);
      for (let j = Math.floor(p) - 1; j <= Math.floor(p) + 2; j++) {
        const phi = (p - j) * (TAU / 10);
        if (Math.abs(phi) > 1.25) continue;
        const zz = zc + CN.drum * Math.sin(phi);
        const scale = Math.cos(phi);
        const digit = ((j % 10) + 10) % 10;
        const centred = Math.abs(phi) < 0.3;
        out.push(`<text style="${PAINT[centred ? "digit-lit" : "digit"]}" transform="translate(${n2(xc)} ${n2(-zz)}) scale(1 ${n2(scale)})" font-size="8.2" text-anchor="middle" dominant-baseline="central" fill-opacity="${n2(scale ** 4)}">${digit}</text>`);
      }
    }
    return out.join("");
  }

  // --- the journal: the audit strip behind the left window, one printed line per visit ------
  const JO = C.JOURNAL;
  function journal({ lines, scroll, ink }) {
    // lines: newest first; scroll: how far the strip has moved up for the next line; ink: the newest line's ink.
    const out = [];
    lines.forEach((text, j) => {
      const z = JO.print + (j + scroll) * JO.pitch;
      if (z > JO.z1 + 2) return;
      const opacity = j === 0 ? ink : 1;
      if (opacity <= 0.01) return;
      out.push(`<text style="${PAINT[j === 0 && scroll < 0.01 ? "print-lit" : "print"]}" x="${JO.x0 + 3}" y="${n2(-z)}" font-size="3.15" fill-opacity="${n2(opacity)}">${text}</text>`);
    });
    return out.join("");
  }

  // --- the marquee tab: a card with the admitted state's name that pops up behind the glass ---
  const MQ = C.MARQUEE;
  const TAB = { x0: MQ.x0 + 9, x1: MQ.x1 - 9, z0: MQ.z0 + MQ.base + 1.5, z1: MQ.z1 - 2.2, y: (MQ.y0 + MQ.y1) / 2 };
  function tabCard(index, drop) {
    const h = TAB.z1 - TAB.z0;
    const z0 = TAB.z0 - drop * (h + 2), z1 = TAB.z1 - drop * (h + 2);
    const card = box(TAB.x0, TAB.y - 0.4, z0, TAB.x1, TAB.y + 0.4, z1, 0.3, 2);
    const label = `<g transform="${front(TAB.y + 0.4)}"><text style="${PAINT.tab}" x="${(TAB.x0 + TAB.x1) / 2}" y="${n2(-(z0 + z1) / 2)}" font-size="11" text-anchor="middle" dominant-baseline="central">w${M.sub(index)}</text></g>`;
    return S(card, { tone: "mid", crease: "none", inner: label });
  }
  function marquee({ index, pop }) {
    // pop: 0 at rest; on a turn the old tab falls (0 → 1) and the new one rises with a spring.
    if (!pop) return tabCard(index, 0);
    const out = [];
    if (pop.old < 1) out.push(tabCard(index - 1, pop.old));
    if (pop.rise > -1) out.push(tabCard(index, pop.rise));
    return out.join("");
  }

  return { PAINT, PAWL_PIN, crankBack, crankFront, tripLow, tripHigh, dropAt, ROD, LEVER, BRACKET, drawer, coin, striker, counter, journal, marquee, TAB, POST, planeMatrix, front, rect };
}

const LIVE = makeLive(k, G, P, C, M);

// --- static drawing ---------------------------------------------------------------------------

const at = (point) => k.iso(point, P);
const S = (paths, style) => k.solidSvg(paths, style);
const L = (d, style) => k.lineSvg(d, style);
const D = (points, style) => k.dotsSvg(points, style);
const X = [1, 0, 0], Y = [0, 1, 0], Z = [0, 0, 1];
const byDepth = (points) => [...points].sort((a, b) => k.depthOf([a[0], a[1], 0], P) - k.depthOf([b[0], b[1], 0], P));
// Stone (kit iso.css, data-mat): a group remaps the tone ramp of what it holds.
const stone = (material, ...svg) => `<g data-mat="${material}">${svg.join("")}</g>`;
const { front, rect, planeMatrix, PAINT } = LIVE;
const side = (x) => planeMatrix([x, 0, 0], [0, -1, 0], [0, 0, -1]); // local (−y, −z) on a face that looks along +x
const faceRect = (x0, z0, x1, z1, r) => rect(x0, -z1, x1, -z0, r);

// A window recessed into a front face at y: inner walls shaded by facing, a back plane with its content.
let clips = 0;
function recess({ x0, x1, z0, z1, r, depth }, y, back = "", backPaint = PAINT.well, over = "") {
  const id = `gr-clip-${clips++}`;
  const ring = k.roundedPlan({ x: x0, y: z0, w: x1 - x0, d: z1 - z0, r }, 6);
  const cx = (x0 + x1) / 2;
  const cz = (z0 + z1) / 2;
  const tops = [];
  const sides = [[], [], [], []];
  const light = G.lightOf(P);
  ring.forEach(([ax, az], index) => {
    const [bx, bz] = ring[(index + 1) % ring.length];
    const length = Math.hypot(bx - ax, bz - az) || 1;
    let [nx, nz] = [(bz - az) / length, -(bx - ax) / length];
    if (nx * (cx - (ax + bx) / 2) + nz * (cz - (az + bz) / 2) < 0) [nx, nz] = [-nx, -nz];
    // The wall's normal points into the window; it is seen when it faces the viewer.
    if (nx * G.viewOf(P)[0] + nz * G.viewOf(P)[2] <= 0) return;
    const quad = k.pathOf([at([ax, y, az]), at([bx, y, bz]), at([bx, y - depth, bz]), at([ax, y - depth, az])], true);
    // The lightest band is the kit's top tone, as on a turned part: a wall turned full to the light (which a
    // swung view can do) shades like a top.
    const band = nz > 0.7 ? 4 : G.bandOf(nx * light[0] + nz * light[2]);
    (band === 4 ? tops : sides[band]).push(quad);
  });
  const shape = faceRect(x0, z0, x1, z1, r);
  return [
    `<clipPath id="${id}"><path transform="${front(y)}" d="${shape}"/></clipPath>`,
    `<g clip-path="url(#${id})">`,
    `<g transform="${front(y - depth)}"><path style="${backPaint}" d="${shape}"/></g>`,
    back,
    `<path class="iso-top" d="${tops.join("")}"/>`,
    ...sides.map((d, shade) => (d.length ? `<path class="iso-shade" data-shade="${shade}" d="${d.join("")}"/>` : "")),
    over,
    `</g>`,
    `<g transform="${front(y)}"><path class="iso-line" data-tone="lo" d="${shape}"/></g>`,
  ].join("");
}

function bench() {
  const { PLATE, PLATE_H, FOOT_H } = C;
  const out = [`<path class="iso-halo" d="${k.haloOf(PLATE, -PLATE_H - FOOT_H, PLATE_H, P)}"/>`];
  for (const [x, y] of byDepth(k.corners(PLATE, 22))) {
    out.push(stone("ink", S(k.cylinder(x, y, 7, -PLATE_H - FOOT_H, 1.6, P, 28), { tone: "lo" }), S(k.cylinder(x, y, 5.4, -PLATE_H - FOOT_H + 1.6, FOOT_H - 1.6, P, 28), { tone: "mid" })));
  }
  out.push(stone("marble", S(k.slabOf(PLATE, -PLATE_H, PLATE_H, P, 8, 1.6), { tone: "mid" })));
  out.push(L(k.planOutline(k.insetPlan(PLATE, 5), 0, P), { tone: "lo" }));
  const screws = k.corners(PLATE, 10);
  out.push(L(screws.map(([x, y]) => k.ring(x, y, 2.2, 0, P, 16)).join(""), { tone: "lo" }));
  out.push(D(screws.map(([x, y]) => at([x, y, 0])), { size: 0.5 }));
  // The label plate, back right.
  const label = { x: 36, y: -66, w: 42, d: 13, r: 1.4 };
  out.push(stone("ink", S(k.slabOf(label, 0, 0.8, P, 3), { tone: "lo", crease: "none" }), L(k.planOutline(k.insetPlan(label, 1.6), 0.8, P, 3), { tone: "faint" }),
    L([30, 22, 26].map((w, i) => k.lineOnTop([label.x + 4.5, label.y + 3.8 + i * 2.7], [label.x + 4.5 + w, label.y + 3.8 + i * 2.7], 0.8, P)).join(""), { tone: "faint", free: true }),
    D([at([label.x + label.w - 3.4, label.y + 3.4, 0.8]), at([label.x + label.w - 3.4, label.y + label.d - 3.4, 0.8])], { size: 0.45 })));
  return out.join("");
}

// The change mat: a rubber pad with a lip and a field of raised dots, where the coin lies.
function mat() {
  const { MAT } = C;
  const out = [];
  out.push(S(k.slabOf(MAT, 0, 1.4, P, 8, 0.6), { tone: "lo" }));
  out.push(L(k.planOutline(k.insetPlan(MAT, 3), 1.4, P, 8), { tone: "faint" }));
  const field = k.insetPlan(MAT, 6.5);
  const gap = 4.2;
  const cols = Math.floor(field.w / gap) + 1;
  const rows = Math.floor(field.d / gap) + 1;
  const ox = field.x + (field.w - (cols - 1) * gap) / 2;
  const oy = field.y + (field.d - (rows - 1) * gap) / 2;
  const pts = [];
  for (let i = 0; i < cols; i++) for (let j = 0; j < rows; j++) {
    const x = ox + i * gap, y = oy + j * gap;
    // Leave the dots under the coin's seat.
    if (Math.hypot(x - C.COIN.x, y - C.COIN.y) < C.COIN.r + 1.6) continue;
    pts.push(at([x, y, 1.4]));
  }
  out.push(D(pts, { size: 0.42, tone: "lo" }));
  out.push(L(k.ring(C.COIN.x, C.COIN.y, C.COIN.r + 1.2, 1.4, P, 48), { tone: "faint" }));
  return stone("ink", ...out);
}

function cashRegister() {
  const { PLINTH, CAB, UPPER, CAP, Z: H, DRAWER: DR, JOURNAL: JO, COUNTER: CN, NAME } = C;
  const out = [`<path class="iso-halo" d="${k.haloOf(PLINTH, 0, 10, P)}"/>`];
  // Bun feet under the plinth.
  for (const [x, y] of byDepth(k.corners(PLINTH, 9))) {
    const F = G.frameOf([x, y, 0], Z, X, Y);
    out.push(stone("ink", S(G.solidOf([[0, 4.2], [0.6, 5, 1], [2.2, 5.3, 1], [3.8, 4.7, 1], [H.foot, 3.6]], F, P), { tone: "mid" })));
  }
  out.push(stone("ink", S(k.slabOf(PLINTH, H.foot, H.plinth - H.foot, P, 4, 0.6), { tone: "lo" })));
  // The cabinet, with a base band and its side panel.
  out.push(stone("marble", S(k.slabOf(CAB, H.plinth, H.cab - H.plinth, P, 4, 0.8), { tone: "mid", inner: L(k.sideSeam(CAB, H.plinth + 2.4, P, 4), { tone: "faint" }) })));
  const cabSide = CAB.x + CAB.w;
  const sidePanel = (x, y0, y1, z0, z1, screws = true) => {
    const panel = rect(-y1, -z1, -y0, -z0, 1.6);
    const inner = rect(-y1 + 1.6, -z1 + 1.6, -y0 - 1.6, -z0 - 1.6, 1);
    const pts = screws ? [[y0 + 3.4, z0 + 3.4], [y1 - 3.4, z0 + 3.4], [y0 + 3.4, z1 - 3.4], [y1 - 3.4, z1 - 3.4]].map(([y, z]) => at([x, y, z])) : [];
    return `<g transform="${side(x)}">${L(panel, { tone: "lo" })}${L(inner, { tone: "faint" })}</g>${D(pts, { size: 0.42 })}`;
  };
  out.push(sidePanel(cabSide, CAB.y + 6, CAB.y + 34, H.plinth + 6, H.cab - 5));
  // The latch lever's slot, its stop pin under the rod end, a boss under its pivot.
  const LV = LIVE.LEVER;
  out.push(`<g transform="${side(cabSide)}"><path style="${PAINT["dark"]}" d="${rect(-(LV.y + LV.front + 2), -(LV.z + 4.6), -(LV.y + LV.front - 2), -(LV.z - 3.4), 1.6)}"/>${L(rect(-(LV.y + LV.front + 2), -(LV.z + 4.6), -(LV.y + LV.front - 2), -(LV.z - 3.4), 1.6), { tone: "lo" })}</g>`);
  const stopF = G.frameOf([cabSide, LV.y - LV.back + 1.5, LV.z - LV.half - 3.2], X, Z, Y);
  out.push(stone("ink", S(G.disc(0, 1.8, 0.8, stopF, P), { tone: "mid" })));
  const bossF = G.frameOf([cabSide, LV.y, LV.z], X, Z, Y);
  out.push(S(G.disc(0, 0.2, 2.4, bossF, P), { tone: "lo" }));
  // The till opening; the drawer front covers it until the crank lets the drawer out.
  const opening = { x0: DR.x0, x1: DR.x1, z0: DR.z0, z1: DR.z1, r: 0.8, depth: 4 };
  out.push(recess(opening, C.FRONT, "", PAINT.dark));
  out.push(`<g data-part="till">${rest(() => LIVE.drawer(0))}</g>`);
  // The ledge in front of the upper case.
  out.push(L(k.planOutline({ x: CAB.x + 4, y: C.UFRONT + 3, w: CAB.w - 8, d: C.FRONT - C.UFRONT - 6, r: 1.5 }, H.cab, P, 4), { tone: "faint" }));
  // The upper case, with bands at its foot and under its cap.
  const bands = L(k.sideSeam(UPPER, H.cab + 3.2, P, 4) + k.sideSeam(UPPER, H.upper - 3.2, P, 4), { tone: "faint" });
  out.push(stone("marble", S(k.slabOf(UPPER, H.cab, H.upper - H.cab, P, 4, 0.8), { tone: "mid", inner: bands })));
  out.push(sidePanel(C.SIDE, UPPER.y + 6, C.UFRONT - 6, H.cab + 13, H.upper - 7));
  // The journal window: the strip between two rollers, the ribbon bar under its print line.
  const jBack = C.UFRONT - JO.depth;
  const paper = jBack + 0.6;
  const roller = (z) => `<g transform="${front(paper + 1.4)}"><path style="${PAINT["roller"]}" d="${rect(JO.x0 - 2, -(z + 2.2), JO.x1 + 2, -(z - 2.2), 0)}"/>${L(`M${JO.x0 - 2} ${-(z + 1.1)}H${JO.x1 + 2}M${JO.x0 - 2} ${-(z - 1.3)}H${JO.x1 + 2}`, { tone: "faint" })}${L(`M${JO.x0 - 2} ${-(z + 2.2)}H${JO.x1 + 2}M${JO.x0 - 2} ${-(z - 2.2)}H${JO.x1 + 2}`, { tone: "lo" })}</g>`;
  const ribbon = `<g transform="${front(paper + 1)}"><path style="${PAINT["ribbon"]}" d="${rect(JO.x0 - 2, -(JO.print - 2.2), JO.x1 + 2, -(JO.print - 4.2), 0)}"/>${L(`M${JO.x0 - 2} ${-(JO.print - 2.2)}H${JO.x1 + 2}M${JO.x0 - 2} ${-(JO.print - 4.2)}H${JO.x1 + 2}`, { tone: "lo" })}</g>`;
  const strip = `<g transform="${front(paper)}"><path style="${PAINT["paper"]}" d="${rect(JO.x0 + 1.4, -(JO.z1 + 2), JO.x1 - 1.4, -(JO.z0 - 2), 0)}"/>${L(`M${JO.x0 + 1.4} ${-(JO.z1 + 2)}V${-(JO.z0 - 2)}M${JO.x1 - 1.4} ${-(JO.z1 + 2)}V${-(JO.z0 - 2)}`, { tone: "faint" })}<g data-part="journal">${rest(() => LIVE.journal({ lines: [M.journalOf(M.stateAt(1))], scroll: 0, ink: 1 }))}</g></g>`;
  const glare = `<g transform="${front(C.UFRONT - 0.3)}">${L(`M${JO.x0 + 4} ${-(JO.z1 + 1)}L${JO.x0 - 2} ${-(JO.z1 - 14)}M${JO.x1 + 1} ${-(JO.z0 + 30)}L${JO.x0 + 9} ${-(JO.z0 - 1)}`, { tone: "faint" })}</g>`;
  out.push(recess(JO, C.UFRONT, strip + roller(JO.z1 - 1) + roller(JO.z0 + 1) + ribbon, PAINT.well, glare));
  // A bezel round the journal window, with four screws.
  const bez = (w) => L(faceRect(w.x0 - 2.4, w.z0 - 2.4, w.x1 + 2.4, w.z1 + 2.4, w.r + 2), { tone: "lo" });
  const bezScrews = (w) => D([[w.x0 - 1.2, w.z0 - 1.2], [w.x1 + 1.2, w.z0 - 1.2], [w.x0 - 1.2, w.z1 + 1.2], [w.x1 + 1.2, w.z1 + 1.2]].map(([x, z]) => at([x, C.UFRONT, z])), { size: 0.42 });
  out.push(`<g transform="${front(C.UFRONT)}">${bez(JO)}${bez(CN)}</g>${bezScrews(JO)}${bezScrews(CN)}`);
  // The counter window: four wheels on one shaft, with a fence between them.
  const cellW = (CN.x1 - CN.x0) / M.DIGITS;
  const fences = Array.from({ length: M.DIGITS - 1 }, (_, i) => `M${CN.x0 + cellW * (i + 1)} ${-(CN.z1 + 1)}V${-(CN.z0 - 1)}`).join("");
  const wheels = `<g transform="${front(C.UFRONT - CN.depth + 0.4)}"><path style="${PAINT["drum"]}" d="${faceRect(CN.x0, CN.z0, CN.x1, CN.z1, 0)}"/><g data-part="counter">${rest(() => LIVE.counter(1))}</g>${L(fences, { tone: "lo" })}<path style="${PAINT["drum-shade"]}" d="${faceRect(CN.x0, CN.z1 - 2.2, CN.x1, CN.z1 + 1, 0)}${faceRect(CN.x0, CN.z0 - 1, CN.x1, CN.z0 + 2.2, 0)}"/><path style="${PAINT["drum-shade"]}" d="${faceRect(CN.x0, CN.z1 - 1, CN.x1, CN.z1 + 1, 0)}${faceRect(CN.x0, CN.z0 - 1, CN.x1, CN.z0 + 1, 0)}"/></g>`;
  out.push(recess(CN, C.UFRONT, wheels, PAINT.well));
  // The nameplate, proud of the face.
  out.push(stone("jade", S(k.slabOf({ x: NAME.x0, y: C.UFRONT, w: NAME.x1 - NAME.x0, d: 0.8, r: 0.3 }, NAME.z0, NAME.z1 - NAME.z0, P, 2), { tone: "lo", crease: "none" })));
  out.push(`<g transform="${front(C.UFRONT + 0.8)}">${k.faceTextSvg("translate(" + ((NAME.x0 + NAME.x1) / 2) + " " + -(NAME.z0 + 1.9) + ")", "H0MEWORK", { size: 4.1, tone: "hi", anchor: "middle" })}</g>`);
  out.push(D([at([NAME.x0 + 1.8, C.UFRONT + 0.8, (NAME.z0 + NAME.z1) / 2]), at([NAME.x1 - 1.8, C.UFRONT + 0.8, (NAME.z0 + NAME.z1) / 2])], { size: 0.4 }));
  // The crank's boss and the pawl's stud, fixed to the case side.
  const F0 = G.frameOf([C.SIDE, C.CRANK.y, C.CRANK.z], X, Z, Y);
  out.push(stone("jade", S(G.disc(0, 1.6, 7.8, F0, P), { tone: "mid", inner: L(G.circleOf(F0, 1.6, 6.8, P), { tone: "faint" }) }), D(G.dotsOf(F0, 1.6, 7.3, 6, P, { all: true, phase: 0.5 }), { size: 0.38 })));
  const pinF = G.frameOf(LIVE.PAWL_PIN, X, Z, Y);
  out.push(stone("ink", S(G.disc(0, 3.2, 0.7, pinF, P), { tone: "mid" })));
  // An oil cup on the bearing, its cap on a short stem.
  const cup = [C.SIDE + 0.8, C.CRANK.y, C.CRANK.z + 7.4];
  out.push(S(k.cylinder(cup[0], cup[1], 1.3, cup[2], 2.4, P, 18), { tone: "mid" }));
  out.push(stone("jade", S(k.cylinder(cup[0], cup[1], 1.7, cup[2] + 2.4, 0.9, P, 18, 0.3), { tone: "hi" })));
  out.push(`<g data-part="crank-back">${rest(() => LIVE.crankBack(0))}</g>`);
  out.push(`<g data-part="trip-low">${rest(() => LIVE.tripLow(0))}</g>`);
  // The rod's guide bracket, standing off the case side.
  const RD = LIVE.ROD, BR = LIVE.BRACKET;
  out.push(stone("ink", S(k.slabOf({ x: C.SIDE, y: RD.y - 3, w: RD.x - C.SIDE + 2.4, d: 6, r: 0.8 }, BR.z0, BR.z1 - BR.z0, P, 3, 0.4), { tone: "mid", inner: "" })));
  out.push(L(k.ring(RD.x, RD.y, RD.r + 0.4, BR.z1, P, 20), { tone: "lo" }));
  out.push(D([at([C.SIDE + 1.6, RD.y - 1.8, BR.z1]), at([C.SIDE + 1.6, RD.y + 1.8, BR.z1])], { size: 0.38 }));
  out.push(`<g data-part="trip-high">${rest(() => LIVE.tripHigh(0))}</g>`);
  out.push(`<g data-part="crank">${rest(() => LIVE.crankFront(0))}</g>`);
  // An invisible target over the crank's whole sweep, so the crank is easy to hit.
  const sweep = Array.from({ length: 36 }, (_, i) => at(G.pointOf(F0, 6, C.CRANK.len + 4, (i / 36) * Math.PI * 2)));
  out.push(`<path data-part="crank-hit" fill="transparent" d="${k.pathOf(sweep, true)}"/>`);
  // The cap, then the marquee on it: a glazed box whose tab shows the admitted state.
  out.push(stone("ink", S(k.slabOf(CAP, H.upper, H.cap - H.upper, P, 4, 1), { tone: "mid" })));
  // The lid over the journal roll, hinged at the back, with a finger notch at the front.
  const lid = { x: CAP.x + 5, y: CAP.y + 6, w: 22, d: 54, r: 1.6 };
  out.push(L(k.planOutline(lid, H.cap, P, 4), { tone: "lo" }));
  out.push(L(k.planOutline(k.insetPlan(lid, 1.4), H.cap, P, 4), { tone: "faint" }));
  for (const hx of [lid.x + 6, lid.x + lid.w - 6]) {
    // A hinge: two leaves either side of the lid's back edge, a knuckle line between them.
    const leaf = { x: hx - 3, y: lid.y - 2.4, w: 6, d: 4.8, r: 0.5 };
    out.push(S(k.slabOf(leaf, H.cap, 0.3, P, 2), { tone: "mid", crease: "none", inner: L(k.lineOnTop([leaf.x, lid.y], [leaf.x + leaf.w, lid.y], H.cap + 0.3, P), { tone: "lo" }) }));
    out.push(D([at([hx - 1.6, lid.y - 1.2, H.cap + 0.3]), at([hx + 1.6, lid.y - 1.2, H.cap + 0.3]), at([hx - 1.6, lid.y + 1.2, H.cap + 0.3]), at([hx + 1.6, lid.y + 1.2, H.cap + 0.3])], { size: 0.32 }));
  }
  out.push(L(k.planOutline({ x: lid.x + lid.w / 2 - 4, y: lid.y + lid.d - 3.4, w: 8, d: 1.8, r: 0.9 }, H.cap, P, 3), { tone: "lo" }));
  const MQ = C.MARQUEE;
  const mqPlan = { x: MQ.x0, y: MQ.y0, w: MQ.x1 - MQ.x0, d: MQ.y1 - MQ.y0, r: 1.2 };
  const baseTop = MQ.z0 + MQ.base;
  out.push(stone("jade", S(k.slabOf(mqPlan, MQ.z0, MQ.base, P, 3, 0.6), { tone: "mid" })));
  const TAB = LIVE.TAB;
  out.push(L(k.planOutline({ x: TAB.x0 - 1.2, y: TAB.y - 1.1, w: TAB.x1 - TAB.x0 + 2.4, d: 2.2, r: 0.8 }, baseTop, P, 3), { tone: "lo" }));
  out.push(S(k.slabOf({ x: MQ.x0 + 1.5, y: MQ.y0, w: MQ.x1 - MQ.x0 - 3, d: 1.4, r: 0.2 }, baseTop, MQ.z1 - baseTop, P, 2), { tone: "lo", crease: "none" }));
  const post = (x, y) => S(k.slabOf({ x: x - 1.2, y: y - 1.2, w: 2.4, d: 2.4, r: 0.5 }, baseTop, MQ.z1 - baseTop, P, 2), { tone: "mid" });
  out.push(post(MQ.x0 + 1.2, MQ.y0 + 1.2), post(MQ.x1 - 1.2, MQ.y0 + 1.2));
  const tabClip = k.pathOf([[TAB.x0 - 2, baseTop], [TAB.x1 + 2, baseTop], [TAB.x1 + 2, MQ.z1], [TAB.x0 - 2, MQ.z1]].map(([x, z]) => at([x, TAB.y, z])), true);
  out.push(`<clipPath id="gr-tab-clip"><path d="${tabClip}"/></clipPath><g clip-path="url(#gr-tab-clip)" data-part="marquee">${rest(() => LIVE.marquee({ index: 1, pop: null }))}</g>`);
  out.push(post(MQ.x0 + 1.2, MQ.y1 - 1.2), post(MQ.x1 - 1.2, MQ.y1 - 1.2));
  // Glare on the front and side panes, running up under the cap.
  const pane = (a, b) => L(k.pathOf([at(a), at(b)]), { tone: "faint" });
  out.push(pane([MQ.x0 + 5, MQ.y1, MQ.z1 + 1.5], [MQ.x0 + 15, MQ.y1, baseTop]), pane([MQ.x0 + 10, MQ.y1, MQ.z1 + 1.5], [MQ.x0 + 20, MQ.y1, baseTop]));
  out.push(pane([MQ.x1, MQ.y0 + 4, MQ.z1 + 1.5], [MQ.x1, MQ.y0 + 13, baseTop]));
  out.push(stone("jade", S(k.slabOf(k.insetPlan(mqPlan, -0.8), MQ.z1, MQ.cap, P, 3, 0.7), { tone: "mid" })));
  out.push(stone("ink", S(k.slabOf({ x: (MQ.x0 + MQ.x1) / 2 - 9, y: MQ.y0 + 6, w: 18, d: MQ.y1 - MQ.y0 - 12, r: 1 }, MQ.z1 + MQ.cap, 1.4, P, 3, 0.4), { tone: "lo" })));
  const BE = C.BELL;
  const FB = G.frameOf([BE.x, BE.y, H.cap], Z, X, Y);
  out.push(stone("ink", S(G.disc(0, 1.4, 5.6, FB, P), { tone: "mid" }), S(G.disc(1.4, 4.6, 1.3, FB, P), { tone: "mid" })));
  const bell = (s) => BE.r * Math.sqrt(Math.max(0, 1 - ((s - 4.6) / 9.6) ** 2));
  const bellSlope = (s) => { const t = (s - 4.6) / 9.6; return t >= 0.999 ? -40 : (-BE.r * t) / (9.6 * Math.sqrt(1 - t * t)); };
  const dome = Array.from({ length: 22 }, (_, i) => { const s = 4.6 + 0.2 + (9.3 * i) / 21; return [s, bell(s), 1]; });
  dome[0][2] = 0;
  out.push(stone("jade", S(G.solidOf([[4.6, BE.r], ...dome], FB, P, { smooth: { slope: bellSlope, radius: (s) => (s <= 4.8 ? BE.r : bell(s)) } }), { tone: "hi" })));
  out.push(stone("ink", S(G.sphereOf(G.pointOf(FB, 14.6, 0, 0), 1.3, P), { tone: "mid" })));
  out.push(stone("ink", S(k.cylinder(LIVE.POST[0], LIVE.POST[1], 2.2, H.cap, 0.8, P, 20), { tone: "mid" }), S(k.cylinder(LIVE.POST[0], LIVE.POST[1], 0.9, H.cap + 0.8, 7.7, P, 14), { tone: "mid" })));
  out.push(`<g data-part="striker">${rest(() => LIVE.striker(0))}</g>`);
  return out.join("");
}

const REST = M.stateAt(1);
// The moving parts at rest; a swing leaves them hollow (`composition(true)`) and paints them where they are.
let hollow = false;
const rest = (draw) => (hollow ? "" : draw());
// The coin lies with its face across the front of the counter (the design view's screen), not the
// swung one's.
function composition(empty = false) {
  hollow = empty;
  clips = 0;
  return [
    bench(),
    cashRegister(),
    mat(),
    `<g data-part="coin-slot">${rest(() => LIVE.coin({ c: [C.COIN.x, C.COIN.y, 1.4 + C.COIN.t / 2], a: [0, 0, 1], u: [Math.sin((VIEW.azimuth * Math.PI) / 180), -Math.cos((VIEW.azimuth * Math.PI) / 180), 0] }))}</g>`,
    `<path data-part="coin-hit" fill="transparent" d="${k.pathOf(k.circleRing(C.COIN.x, C.COIN.y, C.COIN.r + 7, 32).map(([x, y]) => at([x, y, 1.4])), true)}"/>`,
  ].join("");
}
const svg = k.figureSvg({
  width: WIDTH,
  height: HEIGHT,
  className: "gr-svg",
  label:
    "A cash register on a counter, with a coin on a change mat beside it. The register has one input, a crank on its side; each turn steps the root once, pops up the new state on the tab on top, rolls the counter on, prints the visit on the audit strip, and near its end a cam pushes a trip rod that lifts the drawer's bolt, so the bell rings and the drawer springs out. The coin flips between its 0 and 1 faces when clicked, and nothing in the register moves: there is no slot for it.",
  body: composition(),
});

const CSS = `
.iso-stage{outline:none;touch-action:pan-y}
${SWING_CSS}
.iso-stage:focus-visible{box-shadow:0 0 0 1px var(--anatomy-mid)}
.gr-svg [data-part="coin-slot"],.gr-svg [data-part="coin-hit"],.gr-svg [data-part="crank"],.gr-svg [data-part="crank-back"],.gr-svg [data-part="crank-hit"],.gr-svg [data-part="till"]{cursor:pointer}
@media (max-width:560px){.gr-svg.iso-svg{width:106%;max-width:none;margin:0 -3%}}
`;

const COPY = {
  en: {
    title: "Two Booleans, one world",
    hint: "Drag: look round · click: coin, crank, drawer",
    keys: ["Counter and audit strip: the registered occurrence of each visit", "The coin: a Boolean set beside the world", "Crank and ratchet: the root's one step, next"],
    refs: ["Proposition 2.3", "Lemma 2.2", "Theorem 2.6"],
    caption: [
      "A cash register that takes one input: each turn of the crank steps the root once along next.",
      "The tab on top shows the new state, the counter rolls on, and the audit strip prints the visit’s registered occurrence. A lawful world state is that registered visit; there is no second register.",
      "The coin on the mat is a Boolean set beside the world. g₀ = (w₁, false) and g₁ = (w₁, true) really are different pairs, and a click really flips it. Admission keeps only the first component, though: the state, the occurrence and the authoritative evolution stay where they were, and the register has no slot a Boolean could go into.",
      "The drawer opens only on a registered turn: at the end of the stroke the cam on the crank pushes the trip rod down and the lever lifts the bolt. Pulled by hand, it holds. The real difference w₁ ≠ w₂ comes from two different visits of the root, which is why their occurrences differ.",
      "One more bit of raw data is not one more world.",
    ],
    aria: "Cash register and coin: Space flips the coin, the right arrow turns the crank, the down arrow tries the drawer",
  },
  zh: {
    title: "两枚布尔值，一个世界",
    hint: "拖动侧看 · 点击硬币、摇柄、钱屉",
    keys: ["计数窗与流水纸带：每次访问的登记发生", "硬币：贴在世界旁边的布尔值", "摇柄与棘轮：根唯一的一步 next"],
    refs: ["命题 2.3", "引理 2.2", "定理 2.6"],
    caption: [
      "一台只收一种输入的收银机：摇柄每转一圈，根沿 next 推进一步。",
      "顶上的标牌换成新状态，计数窗进一位，流水纸带印下这次访问的登记发生。合法世界状态就是这次登记访问，没有第二份登记表。",
      "垫上的硬币是贴在世界旁边的布尔值。g₀ = (w₁, false) 与 g₁ = (w₁, true) 确实是两个不同的二元组，点一下，它真的翻面。可准入只取第一分量：状态、登记发生与权威演化纹丝不动，机器上也没有能塞进布尔值的槽。",
      "钱屉只随一次登记弹开：摇柄转到底，凸轮压下顶杆，杠杆抬起锁舌；徒手去拉，它不动。真正的差异 w₁ ≠ w₂ 来自根的两次不同访问，所以它们的登记发生也不同。",
      "原始数据多一位，世界并不多一个。",
    ],
    aria: "收银机与硬币：空格翻硬币，右方向键转摇柄，下方向键试拉钱屉",
  },
};

const readoutOf = (index, bit, counterOf, sub) => `(w${sub(index)}, ${bit ? "true" : "false"}) ↦ w${sub(index)} · №${counterOf(index)}`;
const counterDigits = (index) => String(index % 10 ** M.DIGITS).padStart(M.DIGITS, "0");

const bodyOf = (lang) => {
  const copy = COPY[lang];
  return `<div data-figure="ghost-register">${k.plateHtml({
    fig: "Fig 2.3",
    title: copy.title,
    hint: copy.hint,
    readout: readoutOf(1, false, counterDigits, M.sub),
    keys: [
      { mark: "lit", label: copy.keys[0] },
      { mark: "raised", label: copy.keys[1] },
      { mark: "edge", label: copy.keys[2] },
    ],
    caption: copy.caption,
    refs: copy.refs,
    body: `<div class="iso-stage" tabindex="0" role="group" aria-label="${copy.aria}">${svg}</div>`,
  })}</div>`;
};

const strip = (file) => readFileSync(join(HERE, file), "utf8").replace(/^export /gm, "");
const kitSource = strip("../kit/iso-kit.mjs");
const latheSource = `const LATHE = (() => {\n${strip("../kit/lathe.mjs").replace(/^import .*$/gm, "")}\nreturn { ${Object.keys(G).join(", ")} };\n})();`;
const modelSource = `const MODEL = (() => {\n${strip("model.mjs")}\nreturn { DIGITS, stateAt, journalOf, counterOf, indexOf, sub };\n})();`;

const live = `
const P0 = ${JSON.stringify(P)};
let P = P0;
${shipped({ C, VIEW, FRAME })}
const kit = { ${Object.keys(k).join(", ")} };
const k = kit, G = LATHE, M = MODEL;
const makeLive = ${makeLive.toString()};
// The factory reads P when it is made, so a swing makes it again, and the static art takes its helpers anew.
let LIVE, front, rect, planeMatrix, PAINT;
const relive = () => { LIVE = makeLive(kit, LATHE, P, C, MODEL); ({ front, rect, planeMatrix, PAINT } = LIVE); };
relive();
const at = (point) => k.iso(point, P);
const S = (paths, style) => k.solidSvg(paths, style);
const L = (d, style) => k.lineSvg(d, style);
const D = (points, style) => k.dotsSvg(points, style);
const X = [1, 0, 0], Y = [0, 1, 0], Z = [0, 0, 1];
let clips = 0, hollow = false;
const rest = (draw) => (hollow ? "" : draw());
const stone = ${stone.toString()};
${shipped({ byDepth, side, faceRect, recess, bench, mat, cashRegister, composition })}
${swingSource}
const readoutOf = ${readoutOf.toString()};
const counterDigits = (index) => String(index % 10 ** MODEL.DIGITS).padStart(MODEL.DIGITS, "0");
const root = document.querySelector('[data-figure="ghost-register"]');
const stage = root.querySelector(".iso-stage");
const readout = root.querySelector("[data-readout]");
const parts = {};
const bindParts = () => { for (const node of stage.querySelectorAll("[data-part]")) parts[node.dataset.part] = node; };
bindParts();
const still = matchMedia("(prefers-reduced-motion: reduce)");
const TAU = Math.PI * 2;
const RAD = Math.PI / 180;
const smooth = (f) => { const t = Math.min(1, Math.max(0, f)); return t * t * (3 - 2 * t); };
const easeInOut = (f) => { const t = Math.min(1, Math.max(0, f)); return t < 0.5 ? 4 * t * t * t : 1 - Math.pow(-2 * t + 2, 3) / 2; };

// The coin's motion runs at a quarter of real time, so a flip and its wobble can be followed.
const SLOW = 0.25;
const G_REAL = 7360; // 9.81 m/s² in world units (a 9-unit radius is a 12 mm coin)
const g = G_REAL * SLOW * SLOW;
const REST_Z = 1.4 + C.COIN.t / 2;
const H = [Math.sin(P.azimuth * RAD), -Math.cos(P.azimuth * RAD), 0]; // across the screen
const rot = (axis, angle, v) => {
  const c = Math.cos(angle), s = Math.sin(angle), d = axis[0] * v[0] + axis[1] * v[1] + axis[2] * v[2];
  const cr = [axis[1] * v[2] - axis[2] * v[1], axis[2] * v[0] - axis[0] * v[2], axis[0] * v[1] - axis[1] * v[0]];
  return [0, 1, 2].map((i) => v[i] * c + cr[i] * s + axis[i] * d * (1 - c));
};

const state = {
  index: 1, bit: false,
  lines: [MODEL.journalOf(MODEL.stateAt(1))], scroll: 0, ink: 1,
  value: 1, theta: 0, swing: 0,
  open: 0, openV: 0,
  coin: { c: [C.COIN.x, C.COIN.y, REST_Z], a: [0, 0, 1] },
};
let turn = null, toss = null, till = { mode: "shut", t: 0 }, chime = null, pop = null;
let touring = !still.matches, visible = false, frame = 0, last = 0, idle = 0, tourAt = 0, tourWait = 1.6;
const TOUR = [["toss", 2.6], ["toss", 2.6], ["tug", 1.8], ["crank", 4.6], ["toss", 2.6], ["crank", 4.6]];

function say() {
  const text = readoutOf(state.index, state.bit, counterDigits, MODEL.sub);
  if (readout.textContent !== text) readout.textContent = text;
}
function coinPose() {
  const a = state.coin.a;
  const d = H[0] * a[0] + H[1] * a[1] + H[2] * a[2];
  const u = [H[0] - d * a[0], H[1] - d * a[1], H[2] - d * a[2]];
  const n = Math.hypot(u[0], u[1], u[2]) || 1;
  return { c: state.coin.c, a, u: [u[0] / n, u[1] / n, u[2] / n] };
}
function draw(what) {
  if (what.crank) {
    parts["crank-back"].innerHTML = LIVE.crankBack(state.theta);
    parts["trip-low"].innerHTML = LIVE.tripLow(state.theta);
    parts["trip-high"].innerHTML = LIVE.tripHigh(state.theta);
    parts.crank.innerHTML = LIVE.crankFront(state.theta);
  }
  if (what.till) parts.till.innerHTML = LIVE.drawer(state.open);
  if (what.coin) parts["coin-slot"].innerHTML = LIVE.coin(coinPose());
  if (what.striker) parts.striker.innerHTML = LIVE.striker(state.swing);
  if (what.counter) parts.counter.innerHTML = LIVE.counter(state.value);
  if (what.journal) parts.journal.innerHTML = LIVE.journal(state);
  if (what.marquee) parts.marquee.innerHTML = LIVE.marquee({ index: state.index, pop: pop && { old: pop.old, rise: pop.rise } });
  say();
}
const ALL = { crank: 1, till: 1, coin: 1, striker: 1, counter: 1, journal: 1, marquee: 1 };

// --- actions ---
function crankTurn() {
  if (turn) return;
  if (still.matches) {
    register();
    state.lines.unshift(MODEL.journalOf(MODEL.stateAt(state.index)));
    state.lines.length = Math.min(state.lines.length, 12);
    state.value = state.index;
    draw(ALL);
    return;
  }
  turn = { t: 0, printed: false, counted: false, rang: false };
  run();
}
function register() { state.index += 1; }
function tossCoin() {
  if (toss) return;
  if (still.matches) {
    state.bit = !state.bit;
    state.coin.a = [0, 0, state.bit ? -1 : 1];
    draw({ coin: 1 });
    return;
  }
  // Three half-turns about the screen-wide axis, landing with a tilt it then loses in a short wobble.
  const T = 0.18 / SLOW;
  const tilt = 0.32;
  const sign = state.bit ? -1 : 1;
  toss = { t: 0, T, from: state.coin.a.slice(), sign, spin: 3 * Math.PI + tilt, tilt, wobble: null, z0: REST_Z, z1: REST_Z + C.COIN.r * Math.sin(tilt) };
  run();
}
function tugDrawer() {
  if (till.mode !== "shut") return;
  till = { mode: "tug", t: 0 };
  run();
}

// --- stepping ---
function stepTurn(dt) {
  const T = 1.3;
  turn.t += dt;
  const f = Math.min(1, turn.t / T);
  state.theta = TAU * easeInOut(f);
  const phase = state.theta / TAU;
  // Feed the strip up a line, print, roll the counter, then ring and release the drawer.
  state.scroll = smooth((phase - 0.12) / 0.3);
  if (phase >= 0.5 && !turn.printed) {
    turn.printed = true;
    register();
    state.lines.unshift(MODEL.journalOf(MODEL.stateAt(state.index)));
    state.lines.length = Math.min(state.lines.length, 12);
    state.scroll = 0;
    turn.inkAt = turn.t;
  }
  if (turn.printed) state.ink = smooth((turn.t - turn.inkAt) / 0.08);
  else state.ink = 1;
  if (turn.printed) state.value = state.index - 1 + smooth((phase - 0.55) / 0.33);
  if (turn.printed && !pop && phase >= 0.6 && !turn.popped) { turn.popped = true; pop = { t: 0, old: 0, rise: -1 }; }
  // The cam's lobe pushes the trip rod down; once the lever has lifted the bolt, the drawer goes and the bell rings.
  if (!turn.released && LIVE.dropAt(state.theta) > 1.8) {
    turn.released = true;
    chime = { t: 0 };
    if (till.mode === "shut" || till.mode === "closing") till = { mode: "out", t: 0 };
  }
  if (f >= 1) {
    state.value = state.index;
    state.theta = 0;
    turn = null;
  }
}
// The marquee: the old tab drops under gravity, the new one is sprung up past its rest and settles.
function stepPop(dt) {
  pop.t += dt;
  const t = pop.t;
  pop.old = Math.min(1, (t / 0.2) ** 2);
  const u = t - 0.1;
  pop.rise = u <= 0 ? -1 : -Math.exp(-7 * u) * Math.cos(15 * u);
  if (t > 0.9) pop = null;
}
function stepRing(dt) {
  chime.t += dt;
  const t = chime.t;
  state.swing = t < 0.05 ? smooth(t / 0.05) : Math.max(0, 1 - smooth((t - 0.05) / 0.3));
  if (t > 0.4) { state.swing = 0; chime = null; }
}
function stepTill(dt) {
  till.t += dt;
  if (till.mode === "out") {
    // The drawer's spring is preloaded past its stop; it hits the stop and bounces back a little.
    const K = 95, Cd = 7, OPEN = C.DRAWER.open;
    const steps = 4;
    for (let i = 0; i < steps; i++) {
      const h = dt / steps;
      state.openV += (K * (OPEN + 10 - state.open) - Cd * state.openV) * h;
      state.open += state.openV * h;
      if (state.open > OPEN) { state.open = OPEN; state.openV = -0.3 * state.openV; }
    }
    if (till.t > 2.4) till = { mode: "closing", t: 0, from: state.open };
  } else if (till.mode === "closing") {
    state.open = till.from * (1 - easeInOut(till.t / 0.9));
    state.openV = 0;
    if (till.t >= 0.9) { state.open = 0; till = { mode: "shut", t: 0 }; }
  } else if (till.mode === "tug") {
    // Pulled by hand, the drawer moves to its bolt and stops, twice.
    const t = till.t;
    state.open = t < 0.5 ? 0.9 * Math.abs(Math.sin((t / 0.25) * Math.PI)) * (1 - t) : 0;
    if (t >= 0.5) { state.open = 0; till = { mode: "shut", t: 0 }; }
  }
}
function stepToss(dt) {
  toss.t += dt;
  const { T, from, sign } = toss;
  if (!toss.wobble) {
    const f = Math.min(1, toss.t / T);
    // A parabola from the mat to the height at which the tilted coin first touches down.
    const v0 = (toss.z1 - toss.z0) / T + 0.5 * g * T;
    state.coin.c = [C.COIN.x, C.COIN.y, toss.z0 + v0 * toss.t - 0.5 * g * toss.t * toss.t];
    state.coin.a = rot(H, toss.spin * f, from);
    if (f >= 1) {
      state.bit = !state.bit;
      toss.wobble = { t: 0, phi: 0 };
    }
    return;
  }
  // Euler's disk: the tilt falls as (1 − t/Ts)^(1/3) while the precession speeds up as tilt^(−1/2).
  const w = toss.wobble;
  w.t += dt;
  const Ts = 1.1;
  const alpha = toss.tilt * Math.pow(Math.max(0, 1 - w.t / Ts), 1 / 3);
  const rate = Math.min(26, 2 * Math.sqrt(g / (C.COIN.r * Math.max(alpha, 0.02))));
  w.phi += rate * dt;
  const down = [0, 0, state.bit ? -1 : 1];
  const k0 = H;
  const kAxis = rot([0, 0, 1], w.phi, k0);
  state.coin.a = rot(kAxis, alpha * (state.bit ? -1 : 1), down);
  state.coin.c = [C.COIN.x, C.COIN.y, 1.4 + C.COIN.r * Math.sin(alpha) + (C.COIN.t / 2) * Math.cos(alpha)];
  if (w.t >= Ts) {
    state.coin.a = down;
    state.coin.c = [C.COIN.x, C.COIN.y, REST_Z];
    toss = null;
  }
}
function stepTour(dt) {
  tourWait -= dt;
  if (tourWait > 0) return;
  const [kind, wait] = TOUR[tourAt++ % TOUR.length];
  tourWait = wait;
  if (kind === "toss") tossCoin();
  else if (kind === "crank") crankTurn();
  else if (kind === "tug") tugDrawer();
}
function tick(time) {
  const dt = last ? Math.min((time - last) / 1000, 1 / 30) : 1 / 60;
  last = time;
  const what = {};
  if (touring) stepTour(dt);
  if (turn) { stepTurn(dt); what.crank = what.counter = what.journal = 1; }
  if (chime) { stepRing(dt); what.striker = 1; }
  if (pop) { stepPop(dt); what.marquee = 1; } else if (what.counter) what.marquee = 1;
  if (till.mode !== "shut") { stepTill(dt); what.till = 1; }
  if (toss) { stepToss(dt); what.coin = 1; }
  draw(what);
  const busy = touring || turn || chime || pop || toss || till.mode !== "shut";
  frame = visible && busy ? requestAnimationFrame(tick) : 0;
}
const run = () => { if (!frame && visible && !still.matches) { last = 0; frame = requestAnimationFrame(tick); } };
const hold = () => { touring = false; clearTimeout(idle); idle = setTimeout(() => { touring = !still.matches; tourWait = 0.8; run(); }, 9000); };
stage.addEventListener("click", (event) => {
  const part = event.target.closest("[data-part]");
  const name = part && part.closest('[data-part="coin-slot"],[data-part="coin-hit"],[data-part="crank"],[data-part="crank-back"],[data-part="crank-hit"],[data-part="till"]')?.dataset.part;
  if (!name) return;
  hold();
  if (name.startsWith("coin")) tossCoin();
  else if (name.startsWith("crank")) crankTurn();
  else tugDrawer();
});
stage.addEventListener("keydown", (event) => {
  if (event.key === " ") tossCoin();
  else if (event.key === "ArrowRight" || event.key === "Enter") crankTurn();
  else if (event.key === "ArrowDown") tugDrawer();
  else return;
  event.preventDefault();
  hold();
});
new IntersectionObserver((entries) => { visible = entries[entries.length - 1].isIntersecting; if (visible) run(); }, { rootMargin: "120px 0px" }).observe(stage);
say();
// A sideways drag swings the view (../swing.mjs): the counter and register are redrawn from there, then
// every moving part where it is.
const svg = stage.querySelector("svg");
mountSwing(stage, { onHold: hold, onSwing: (angle) => { P = swingOf(iso, P0, FRAME, angle); relive(); svg.innerHTML = composition(true); bindParts(); draw(ALL); } });
`;

const script = `{\n${kitSource}\n${latheSource}\n${modelSource}\n${live}\n}`.replace(/<\/(script)/gi, "<\\/$1");
if (fragment) {
  const outDir = join(HERE, "../../src/generated");
  mkdirSync(outDir, { recursive: true });
  writeFileSync(join(outDir, "ghost-register.json"), JSON.stringify({ html: { zh: bodyOf("zh"), en: bodyOf("en") }, css: CSS, script }));
  console.log("wrote src/generated/ghost-register.json");
} else {
  mkdirSync(join(HERE, "out"), { recursive: true });
  const name = theme === "light" ? "ghost-register-light.html" : "ghost-register.html";
  const lang = process.argv.includes("--zh") ? "zh" : "en";
  writeFileSync(join(HERE, "out", name), k.pageHtml({ title: COPY[lang].title, theme, body: `<style>${CSS}</style>${bodyOf(lang)}`, script, width: 760 }));
  console.log("wrote out/" + name);
}
