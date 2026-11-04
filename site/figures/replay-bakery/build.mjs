// Fig: a replay bakery for the structural theorem. Two identical bread lines run in from either end of a
// bench, each from a glass dough tube through a gate and a vaulted oven, to two rows of baskets standing side
// by side on a stand in the middle. The left line's gate carries a private
// lock with two keys: the controller 丙's key turns, the affected's key can be refused, and a red flag stands
// for a capital core. One order tape runs high over both lines from reel to reel: the left reader stamps
// each request with what actually happened, and the tape is wound across to the right line, whose lock has
// been taken off, to be replayed entry by entry (Theorems 2, 3 and 8 of "The Structural Theorem of
// Capitalism").
//   bun build.mjs [--light]   → out/replay-bakery[-light].html (standalone, for checks)
//   bun build.mjs --fragment  → ../../src/generated/replay-bakery.json (for the site)
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
const HEIGHT = 440;

// World: x across the bench, the private line on the left (σ = −1) and its public replay on the right
// (σ = +1), mirror images of each other; y toward the viewer, z up; the deck's top is z = 0. Each line runs
// from its outer end toward the middle, where the two rows of baskets stand side by side. Positions along
// a line are given as |x|.
const C = {
  BASE: { x: -72, y: -31, w: 144, d: 55, r: 5 },
  BASE_Z: [-16, 0],
  FOOT: { r: 6, h: 4, inset: 16 },
  FACE: 24,
  // The belt runs from its outer roller (x1) in to its inner roller (x0).
  BELT: { x0: 16.6, x1: 56, half: 4.2, z: 9 },
  // The dough tube stands over the belt's outer end.
  // Its collar clears a ball resting on the belt; its bin clears the reader on the gate.
  TUBE: { x: 54.6, r: 2.1, z0: 14.2, collar: 1.3 },
  DOUGH: 1.6,
  LOAF: 1.9,
  LOAF_LEN: 5.8,
  GATE: 44,
  // The oven's vault: walls from `base` to `wall`, a half-round crown above them.
  OVEN: { x0: 21, x1: 37, y: 7, base: 4.2, wall: 10.4, crown: 17.4 },
  MOUTH: { half: 5.2, z0: 6.6, z1: 15.2, spring: 12.2, hinge: 13.4, hem: 9.8 },
  PIVOT: [14.15, 0, 8.4],
  CHUTE: { reach: 7.6, drop: 0.85, half: 2.12, wall: 0.28, floor: 0.5, lip: 1.1, taper: 1.6, runout: 2.4 },
  // The stand in the middle and the baskets on it.
  STAND: { w: 11.4, d: 15, top: 3.4 },
  BASKET: { x: 6, r: 4.7, h: 3.4, floor: 0.45, foot: 3.95, wall: 0.2 },
  SLOTS: { 丙: -9.6, 甲: 0, 乙: 9.6 },
  REEL: { x: 58, y: -17, z: 33.8, r: 6.6 },
  TAPE: { y: -4.6, z0: 35, z1: 39, frame: 8 },
  READER: { x: 44 },
  COUNT: [-7, 7],
};
const PITCH = 2 * C.DOUGH + 0.1; // the dough stack's pitch in its tube
const TUBE_TOP = C.TUBE.z0 + MD.S0.dough * PITCH;
// Where the tube's k-th ball rests (0 at the escapement), `drop` pitches above its seat.
const tubeSeat = (side, k, drop = 0) => [side * C.TUBE.x, 0, C.TUBE.z0 + C.DOUGH + 0.05 + (k + drop) * PITCH];
const SPEED = 18; // the belts' speed, units a second
const LAG = (2 * C.READER.x) / C.TAPE.frame; // frames from the private reader to the public one
const STEPS = MD.W.length + LAG;
const ROWS = { 甲: C.TAPE.z0 + 3, 乙: C.TAPE.z0 + 2, 丙: C.TAPE.z0 + 1 }; // the tape's hole rows

const FIT = [
  ...k.boxCorners(C.BASE, C.BASE_Z[0] - C.FOOT.h, 0),
  [C.REEL.x, C.REEL.y - C.REEL.r, C.TAPE.z1 + 1],
  [-C.REEL.x, C.REEL.y - C.REEL.r, C.TAPE.z1 + 1],
  [0, C.TAPE.y, C.TAPE.z1 + 5],
];
const VIEW = { pad: 20, azimuth: 62, elevation: 31 };
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
const n3 = (v) => (Math.round(v * 1000) / 1000).toString();
const faceY = (y) => k.sideMatrix([0, y], 0, P, "left");
const rectD = (u0, v0, u1, v1, r = 0) => k.pathOf(k.roundedPlan({ x: u0, y: v0, w: u1 - u0, d: v1 - v0, r }, 4), true);
const box = (plan, z, h, style, steps = 3, bevel = 0) => S(k.slabOf(plan, z, h, P, steps, bevel), style);
const cyl = (x, y, r, z, h, style, steps = 20, bevel = 0) => S(k.cylinder(x, y, r, z, h, P, steps, bevel), style);
const FV = (x, y, z) => G.frameOf([x, y, z], Z3, X3, Y3);
const unit = (v) => { const n = Math.hypot(...v) || 1; return v.map((c) => c / n); };
// A plan box from two x bounds in either order.
const span = (xa, xb, y0, y1, r = 0.3) => ({ x: Math.min(xa, xb), y: Math.min(y0, y1), w: Math.abs(xb - xa), d: Math.abs(y1 - y0), r });
// An SVG matrix drawing (u, v) at o + u·U − v·Z: the vertical plane through o along the level direction U.
const planeOf = (o, U) => {
  const p = at(o), a = at([o[0] + U[0], o[1] + U[1], o[2] + U[2]]), b = at([o[0], o[1], o[2] - 1]);
  return `matrix(${n3(a[0] - p[0])} ${n3(a[1] - p[1])} ${n3(b[0] - p[0])} ${n3(b[1] - p[1])} ${n2(p[0])} ${n2(p[1])})`;
};
const rod = (a, b, r, style, steps) => {
  const d = [b[0] - a[0], b[1] - a[1], b[2] - a[2]];
  const length = Math.hypot(...d);
  return length < 0.05 ? "" : S(G.disc(0, length, r, G.frameAlong(a, d), P, steps ? { steps } : {}), style);
};
const smooth = (value) => { const t = Math.max(0, Math.min(1, value)); return t * t * (3 - 2 * t); };

// --- light: highlights and shadows from the kit's own light, so they turn with the view -------------

const halfway = () => { const V = G.viewOf(P), Lt = G.lightOf(P); return unit([V[0] + Lt[0], V[1] + Lt[1], V[2] + Lt[2]]); };
const litAngle = (F) => {
  const h = halfway();
  const ha = h[0] * F.a[0] + h[1] * F.a[1] + h[2] * F.a[2];
  const n = [0, 1, 2].map((i) => h[i] - ha * F.a[i]);
  return Math.atan2(n[0] * F.v[0] + n[1] * F.v[1] + n[2] * F.v[2], n[0] * F.u[0] + n[1] * F.u[1] + n[2] * F.u[2]);
};
const shine = (F, s0, s1, r, r1 = r, fade = 1.5) => { const t = litAngle(F); return k.fadeLineSvg([at(G.pointOf(F, s0, r, t)), at(G.pointOf(F, s1, r1, t))], { fade: [fade, fade], tone: "spec", className: "spec" }); };
const edgeShine = (a, b, fade = 4) => k.fadeLineSvg([at(a), at(b)], { fade: [fade, fade], tone: "spec", className: "spec" });
const glintAt = (p, size = 1.3) => {
  const V = G.viewOf(P), u = unit([-V[1], V[0], 0]);
  const v = [V[1] * u[2] - V[2] * u[1], V[2] * u[0] - V[0] * u[2], V[0] * u[1] - V[1] * u[0]];
  return `<path class="glint" d="${G.circleOf(G.frameOf(p, V, u, v), 0, size, P, 18)}"/>`;
};
const glint = (F, s, r, size = 1.3) => glintAt(G.pointOf(F, s, r, litAngle(F)), size);
const ballGlint = (c, r, size = r * 0.28) => { const h = halfway(); return glintAt(c.map((v, i) => v + h[i] * r * 0.72), size); };
const brightRod = (a, b, r, style, steps, fade = 2) => {
  const d = [b[0] - a[0], b[1] - a[1], b[2] - a[2]];
  const length = Math.hypot(...d);
  if (length < 0.05) return "";
  const F = G.frameAlong(a, d);
  return S(G.disc(0, length, r, F, P, steps ? { steps } : {}), { ...style, inner: shine(F, 0.3, length - 0.3, r * 1.01, r * 1.01, Math.min(fade, length / 3)) });
};
const fadeFill = (a, b, hold = 0) => {
  const id = `rb-sh-${Math.round(a[0] * 10)}-${Math.round(a[1] * 10)}-${Math.round(b[0] * 10)}-${Math.round(b[1] * 10)}`;
  const stop = (where, alpha) => `<stop offset="${where}" stop-opacity="${alpha}" style="stop-color:var(--anatomy-halo)"/>`;
  return [`fill:url(#${id})`, `<defs><linearGradient id="${id}" gradientUnits="userSpaceOnUse" x1="${n2(a[0])}" y1="${n2(a[1])}" x2="${n2(b[0])}" y2="${n2(b[1])}">${stop(0, 1)}${stop(n2(hold), 1)}${stop(n2((1 + hold) / 2), 0.5)}${stop(1, 0)}</linearGradient></defs>`];
};
function boxCast(plan, z, h, o = 1) {
  const Lt = G.lightOf(P);
  const flat = Math.hypot(Lt[0], Lt[1]) || 1;
  const reach = Math.min(h * (flat / Lt[2]) * 0.42, 30);
  const [dx, dy] = [(-Lt[0] / flat) * reach, (-Lt[1] / flat) * reach];
  const foot = k.corners(plan);
  const pts = [...foot, ...foot.map(([x, y]) => [x + dx, y + dy])].map(([x, y]) => at([x, y, z]));
  const c = [plan.x + plan.w / 2, plan.y + plan.d / 2];
  const [fill, defs] = fadeFill(at([c[0], c[1], z]), at([c[0] + dx * 1.2, c[1] + dy * 1.2, z]), 0.75);
  return defs + `<path class="iso-halo" d="${k.pathOf(G.hullOf(pts), true)}" style="${fill};filter:blur(3px);transform:none;opacity:calc(var(--fig-shadow) * ${n2(1.15 * o)})"/>`;
}
function grounded(x, y, r, { z = 0, h = 0, w = r * 0.85, o = 1 } = {}) {
  const core = r <= 0 ? "" : `<path class="iso-halo" d="${k.haloOf({ x: x - r, y: y - r, w: 2 * r, d: 2 * r, r }, z, 0.1, P)}" style="filter:blur(1.2px);transform:none;opacity:calc(var(--fig-shadow) * ${n2(1.1 * o)})"/>`;
  if (h <= 0) return core;
  const Lt = G.lightOf(P);
  const flat = Math.hypot(Lt[0], Lt[1]) || 1;
  const dir = [-Lt[0] / flat, -Lt[1] / flat], n = [-dir[1], dir[0]];
  const reach = Math.min(h * (flat / Lt[2]) * 0.42, 30);
  const end = [x + dir[0] * reach, y + dir[1] * reach];
  const cap = (c, rr, from) => Array.from({ length: 11 }, (_, i) => { const a = from + (i / 10) * Math.PI; return [c[0] + rr * (Math.cos(a) * dir[0] + Math.sin(a) * n[0]), c[1] + rr * (Math.cos(a) * dir[1] + Math.sin(a) * n[1])]; });
  const outline = [...cap([x, y], w, Math.PI / 2), ...cap(end, w * 1.25, -Math.PI / 2)];
  const [fill, defs] = fadeFill(at([x, y, z]), at([end[0], end[1], z]), Math.min(0.6, Math.max(r, w) / (reach + w)));
  return defs + `<path class="iso-halo" d="${k.pathOf(outline.map(([px, py]) => at([px, py, z])), true)}" style="${fill};filter:blur(2.4px);transform:none;opacity:calc(var(--fig-shadow) * ${n2(1.3 * o)})"/>` + core;
}
const shadow = (x, y, r, o = 0.35, { z = 0, h = 0, w = r * 0.8 } = {}) => `<path class="iso-halo" d="${k.haloOf({ x: x - r, y: y - r, w: 2 * r, d: 2 * r, r }, z, 0.1, P)}" style="filter:blur(2.5px);opacity:calc(var(--anatomy-halo-opacity) * ${o})"/>` + grounded(x, y, r * 0.86, { z, h, w, o: o / 0.35 * 0.8 });
const halfRing = (x, y, r, z, far = false) => {
  const [vx, vy] = G.viewOf(P);
  const f = Math.atan2(vy, vx) + (far ? Math.PI : 0);
  return Array.from({ length: 25 }, (_, i) => {
    const t = f + (i / 24 - 0.5) * Math.PI;
    return at([x + r * Math.cos(t), y + r * Math.sin(t), z]);
  });
};
const bandD = (x, y, r, z0, z1, far = false) =>
  k.pathOf([...halfRing(x, y, r, z0, far), ...halfRing(x, y, r, z1, far).reverse()], true);
const lipD = (x, y, inner, outer, z, far) =>
  k.pathOf([...halfRing(x, y, outer, z, far), ...halfRing(x, y, inner, z, far).reverse()], true);
// A lens on a plane facing +y at (x, y, z).
const lensY = (x, y, z, r, className) => `<path class="${className}" d="${G.circleOf(G.frameOf([x, y, z], Y3, X3, Z3), 0, r, P, 20)}"/>`;
// The clip for what lies inside an open container: its opening's outline and everything above it, so a part
// below the near rim is hidden by the container's wall and one rising out of it is not.
// A piece is hidden only where the container's own walls stand in front of it: everything shows except the
// container's outline, and inside that outline its opening shows again (even-odd).
const insideClip = (id, opening, body) => {
  const all = "M-2000 -2000H4000V4000H-2000Z";
  return `<clipPath id="${id}"><path clip-rule="evenodd" d="${all}${k.pathOf(G.hullOf(body.map(at)), true)}${k.pathOf(G.hullOf(opening.map(at)), true)}"/></clipPath>`;
};

// --- the base and its face ----------------------------------------------------------------------

function base() {
  const { BASE, BASE_Z, FOOT } = C;
  const out = [`<path class="iso-halo" d="${k.haloOf(BASE, BASE_Z[0] - FOOT.h, BASE_Z[1] - BASE_Z[0], P)}"/>`];
  const feet = k.corners(BASE, FOOT.inset).sort((a, b) => k.depthOf([...a, 0], P) - k.depthOf([...b, 0], P));
  for (const [x, y] of feet) out.push(cyl(x, y, FOOT.r, BASE_Z[0] - FOOT.h, FOOT.h, { tone: "mid" }, 28, 0.4));
  out.push(box(BASE, BASE_Z[0], -BASE_Z[0] - 3, { tone: "hi", inner: L(k.sideSeam(BASE, BASE_Z[0] + 3, P, 6), { tone: "faint" }) + edgeShine([BASE.x + 8, BASE.y + BASE.d, -3.9], [BASE.x + BASE.w - 8, BASE.y + BASE.d, -3.9], 30) }, 6, 1));
  const deck = k.insetPlan(BASE, 1.5);
  return M("ink", ...out, face()) + M("marble", box(deck, -3, 3, { tone: "mid" }, 6, 0.8),
    L(k.planOutline(k.insetPlan(deck, 3.5), 0, P), { tone: "faint" }),
    D(k.corners(deck, 6).map(([x, y]) => at([x, y, 0])), { size: 0.5 }),
    L(k.corners(deck, 6).map(([x, y]) => k.ring(x, y, 1.6, 0, P, 14)).join(""), { tone: "faint" }));
}
// The base's face: a window for each line's count of tape positions, an equals sign between them, a closed
// lock engraved over the private count and an open one over the replay's; a label plate at each end.
function face() {
  const [a, b] = C.COUNT;
  const lock = (u, open) => `M${u - 1.6} 9.8h3.2v2.6h-3.2ZM${u - 1} 9.8v-1.2a1 1 0 0 1 2 0${open ? "v-0.6" : "v1.2"}`;
  const plate = (u0, u1) => L(rectD(u0, 5, u1, 15, 1.2), { tone: "faint" }) + L(`M${u0 + 5} 8H${u1 - 7}M${u0 + 5} 10H${u1 - 11}M${u0 + 5} 12H${u1 - 15}`, { tone: "faint", free: true });
  const bezel = (u) => L(rectD(u - 9, 4.4, u + 9, 15.6, 1.6), { tone: "faint" });
  const screws = [[a - 7, -5.4], [b + 7, -5.4], [a - 7, -14.6], [b + 7, -14.6], ...[-1, 1].flatMap((s) => [[s * 50 - 7.8, -5.6], [s * 50 + 7.8, -5.6], [s * 50 - 7.8, -14.4], [s * 50 + 7.8, -14.4]])];
  return `<g transform="${faceY(C.FACE + 0.02)}">${[a, b].map((u) => `<path class="rb-window" d="${rectD(u - 4, 5.6, u + 4, 14, 1)}"/>`).join("")}${L([a, b].map((u) => rectD(u - 4, 5.6, u + 4, 14, 1)).join("") + rectD(a - 8.4, 4, b + 8.4, 15.6, 1.6), { tone: "faint" })}${L(lock(a - 6.4, false) + lock(b + 6.4, true), { tone: "faint", free: true })}${bezel(-LAMP_U)}${bezel(LAMP_U)}${plate(-34, -18)}${plate(18, 34)}</g>`
    + D(screws.map(([u, z]) => at([u, C.FACE, z])), { size: 0.45 });
}
// The maintenance lamps on the face, two a line, for 甲 and 乙: lit when that member's loaf has landed.
const LAMP_U = 50;
function faceLamp(u, lit) {
  const F = G.frameOf([u, C.FACE, -10], Y3, X3, Z3);
  return M("ink", S(G.disc(0, 0.7, 2.4, F, P), { tone: "mid", inner: L(G.circleOf(F, 0.7, 2.05, P, 28), { tone: "faint" }) })) + `<path class="rb-lens${lit ? " rb-paid" : ""}" d="${G.circleOf(F, 0.72, 1.7, P, 22)}"/>` + `<path class="rb-glint" d="${G.circleOf(G.frameOf(G.pointOf(F, 0.73, 0.75, 2.3), Y3, X3, Z3), 0, 0.42, P, 10)}"/>`;
}
const faceLamps = (side, bread) => MD.MEMBERS.map((who, i) => faceLamp(side * LAMP_U + (i ? 4 : -4), bread[who] >= 1)).join("");
function counter(state) {
  const digit = (u, n, lit) => `<text class="rb-digit${lit ? " rb-same" : ""}" transform="${faceY(C.FACE + 0.05)} translate(${u} 12.6)" font-size="7.2" text-anchor="middle">${n}</text>`;
  const done = state.counts[0] === MD.W.length && state.counts[1] === MD.W.length;
  // Between the counts: an arrow while the replay follows the given run, an equals sign once both are through.
  const sign = done ? `${rectD(-1.8, 8.3, 1.8, 9.1, 0.2)}${rectD(-1.8, 10.5, 1.8, 11.3, 0.2)}` : "M-1.9 9.4H0.6V8.3L2.1 9.8L0.6 11.3V10.2H-1.9Z";
  const bars = `<path class="rb-eq${done ? " rb-same" : ""}" transform="${faceY(C.FACE + 0.03)}" d="${sign}"/>`;
  return digit(C.COUNT[0], state.counts[0], done) + bars + digit(C.COUNT[1], state.counts[1], done);
}

// --- the tape: two flat reels on marble pillars, the tape between them and its two readers -------------

// Tape wound on each reel: the supply reel thins as the tape runs, the take-up reel fills.
const packOf = (q) => [Math.sqrt(6.3 ** 2 - 0.17 * C.TAPE.frame * q), Math.sqrt(3.8 ** 2 + 0.17 * C.TAPE.frame * q)];
// The point where a tape leaving the reel at c (radius r) toward the guide g touches the reel, on its front.
function tangentPoint(c, r, g, sense) {
  const dx = g[0] - c[0], dy = g[1] - c[1], d = Math.hypot(dx, dy);
  const a = Math.atan2(dy, dx) + sense * Math.acos(Math.min(1, r / d));
  return [c[0] + r * Math.cos(a), c[1] + r * Math.sin(a)];
}
// The tape runs from the supply reel through the private reader, straight across to the public reader and on
// to the take-up reel; each reader holds it on its line.
function tapePath(q) {
  const { REEL, TAPE } = C;
  const [rL, rR] = packOf(q);
  const gL = [-C.READER.x - READ_HALF, TAPE.y], gR = [C.READER.x + READ_HALF, TAPE.y];
  return { rL, rR, pts: [tangentPoint([-REEL.x, REEL.y], rL, gL, 1), gL, gR, tangentPoint([REEL.x, REEL.y], rR, gR, -1)] };
}
// The tape runs straight through each reader and turns off toward its reel only past the reader's outer cheek.
const READ_HALF = 4.9;
// Where the tape's frame j stands along the tape (0 where it leaves the supply side) after q steps: frame j is
// under the private reader after j + 1 steps.
const frameAt = (j, q) => READ_HALF + C.TAPE.frame * (q - j - 1);
// A reel on its pillar: the pillar, a collar and the flange (drawn once), then what turns: the flange's three
// windows, the wound tape and the hub.
function reelBase(side) {
  const { REEL } = C;
  const x = side * REEL.x, y = REEL.y, z = REEL.z;
  const F = FV(x, y, z);
  const pillar = span(x - 1.5, x + 1.5, y - 1.5, y + 1.5, 0.3);
  return boxCast(pillar, 0, z, 0.55) + M("marble", box(k.insetPlan(pillar, -0.9), 0, 1.2, { tone: "mid" }, 2, 0.3), box(pillar, 1.2, z - 3.2, { tone: "mid", inner: edgeShine([pillar.x + pillar.w, pillar.y + pillar.d, 3], [pillar.x + pillar.w, pillar.y + pillar.d, z - 3], 6) }, 2, 0.2), box(k.insetPlan(pillar, -0.6), z - 2, 1, { tone: "mid" }, 2, 0.25))
    + M("ink", cyl(x, y, 1.4, z - 1, 1, { tone: "mid" }, 20, 0.15))
    + M("marble", S(G.disc(0, 0.45, REEL.r, F, P, { bevel: 0.15 }), { tone: "mid", inner: L(G.circleOf(F, 0.45, REEL.r - 0.6, P, 64), { tone: "faint" }) }));
}
function reel(side, q) {
  const { REEL } = C;
  const x = side * REEL.x, y = REEL.y, z = REEL.z;
  const [rL, rR] = packOf(q);
  const pack = side < 0 ? rL : rR;
  // Both reels turn the same way as the tape runs from left to right.
  const turn = -(C.TAPE.frame * q) / pack;
  const F = FV(x, y, z);
  const out = [];
  // The flange's three windows, turning with it; the tape covers their inner ends.
  const windows = [];
  for (let i = 0; i < 3; i++) {
    const a0 = turn + (i * 2 * Math.PI) / 3, a1 = a0 + 0.8;
    const arc = (r, from, to) => Array.from({ length: 9 }, (_, j) => at(G.pointOf(F, 0.47, r, from + ((to - from) * j) / 8)));
    windows.push(k.pathOf([...arc(REEL.r - 1.3, a0, a1), ...arc(2.6, a1, a0)], true));
  }
  out.push(`<path class="rb-slot" d="${windows.join("")}"/>`);
  out.push(M("marble", S(k.cylinder(x, y, pack, C.TAPE.z0, C.TAPE.z1 - C.TAPE.z0, P, 48), { tone: "hi", inner: L([pack - 0.9, pack - 1.9].filter((r) => r > 2.2).map((r) => k.ring(x, y, r, C.TAPE.z1, P, 40)).join(""), { tone: "faint" }) })));
  const hub = FV(x, y, C.TAPE.z1);
  out.push(M("ink", cyl(x, y, 1.5, z + 0.45, C.TAPE.z1 - z - 0.05, { tone: "mid" }, 20), S(G.disc(0.4, 1, 1.7, hub, P, { bevel: 0.2 }), { tone: "mid" }), D(G.dotsOf(hub, 1, 1, 3, P, { all: true, phase: turn }), { size: 0.3 })));
  return out.join("");
}
// The tape: a paper ribbon on edge from reel to reel, in frames; each frame holds a request (a hole for its
// signer, a hole for whose loaf it is) and, once read by the private line, its stamp.
function tape(q, stamps, fade = 1) {
  const { TAPE } = C;
  const { pts } = tapePath(q);
  const segs = [[pts[0], pts[1]], [pts[1], pts[2]], [pts[2], pts[3]]];
  const lens = segs.map(([a, b]) => Math.hypot(b[0] - a[0], b[1] - a[1]));
  const starts = [-lens[0], 0, lens[1]];
  const out = [];
  segs.forEach(([a, b], i) => {
    const U = [(b[0] - a[0]) / lens[i], (b[1] - a[1]) / lens[i], 0];
    const id = `rb-tape-${i}`;
    const frames = [];
    MD.W.forEach((entry, j) => {
      const u = frameAt(j, q) - starts[i];
      if (u + 4 < 0 || u - 4 > lens[i]) return;
      const hole = (du, who) => `<circle class="rb-hole" cx="${n2(u + du)}" cy="${-ROWS[who]}" r=".4"/>`;
      frames.push(`<path class="rb-frame" d="${rectD(u - 3.6, -TAPE.z1 + 0.35, u + 3.6, -TAPE.z0 - 0.35, 0.3)}"/>`, hole(-2.2, entry.by), hole(-0.6, entry.to));
      const mark = stamps[j];
      if (mark) frames.push(`<g style="opacity:${n2(fade)}">${mark === "ok" ? `<circle class="rb-stamp-ok" cx="${n2(u + 1.9)}" cy="${-TAPE.z0 - 2}" r=".8"/>` : `<path class="rb-stamp-no" d="M${n2(u + 1.9)} ${-TAPE.z0 - 3}l1 1l-1 1l-1 -1Z"/>`}</g>`);
    });
    out.push(`<g transform="${planeOf([a[0], a[1], 0], U)}"><clipPath id="${id}"><rect x="0" y="${-TAPE.z1 - 1}" width="${n2(lens[i])}" height="${TAPE.z1 - TAPE.z0 + 2}"/></clipPath><rect class="rb-tape" x="0" y="${-TAPE.z1}" width="${n2(lens[i])}" height="${TAPE.z1 - TAPE.z0}"/><g clip-path="url(#${id})">${frames.join("")}</g></g>`);
  });
  return out.join("");
}
// The tape's one support between the readers: a slender post in the middle with a sleeve the tape bears on.
// Its shadow and its sleeve go behind everything; its shaft stands in front of the private line's crate.
const GUIDE = [0, C.TAPE.y - 1];
const guideShadow = () => "";
// Above everything in the middle the post rises on behind the tape: its upper shaft and jade capital go into the
// back row with the sleeve, so the tape passes in front of them.
const GUIDE_SPLIT = 24;
function guideSleeve() {
  const F = FV(GUIDE[0], GUIDE[1], 0);
  const [x, y] = GUIDE;
  return M("marble", cyl(x, y, 0.55, GUIDE_SPLIT, C.TAPE.z0 - GUIDE_SPLIT - 1.2, { tone: "mid", crease: "none" }, 12)) + M("jade", cyl(x, y, 0.9, C.TAPE.z0 - 1.2, 0.6, { tone: "mid" }, 14, 0.15)) + M("jade", S(G.disc(C.TAPE.z0 - 0.5, C.TAPE.z1 + 0.5, 1, F, P, { bevel: 0.15 }), { tone: "mid", inner: shine(F, C.TAPE.z0, C.TAPE.z1, 1.01, 1.01, 0.8) }), S(G.disc(C.TAPE.z1 + 0.5, C.TAPE.z1 + 1, 1.4, F, P, { bevel: 0.15 }), { tone: "mid" }));
}
function guideShaft() {
  const [x, y] = GUIDE;
  const z = C.STAND.top;
  // A collar marks where the post's two lengths join.
  return M("marble", cyl(x, y, 1.5, z, 0.7, { tone: "mid" }, 18, 0.2), cyl(x, y, 0.55, z + 0.7, GUIDE_SPLIT - z - 0.7, { tone: "mid", crease: "none" }, 12), cyl(x, y, 0.85, GUIDE_SPLIT - 0.35, 0.7, { tone: "mid" }, 14, 0.15));
}
// A reader astride the tape, the capital of its gate's back post: a back plate behind the tape, two front
// cheeks with the read window between them, a bridge with its lamp, and the punch (private) or feeler
// (public) that dips to read.
const READ_Z = [C.TAPE.z0 - 1.4, C.TAPE.z1 + 0.9, C.TAPE.z1 + 2.5];
const READ_BACK = [-7.1, C.TAPE.y - 0.45];
const READ_FRONT = [C.TAPE.y + 0.45, C.TAPE.y + 1.5];
function readerBack(side) {
  const x = side * C.READER.x;
  const [z0, z1] = READ_Z;
  return M("marble", box(span(x - 4.6, x + 4.6, READ_BACK[0], READ_BACK[1], 0.3), z0, z1 - z0, { tone: "mid" }, 2, 0.2));
}
function readerFront(side) {
  const x = side * C.READER.x;
  const [z0, z1, z2] = READ_Z;
  const [f0, f1] = READ_FRONT;
  const bridge = span(x - 4.8, x + 4.8, READ_BACK[0], f1, 0.4);
  return M("marble",
    box(span(x - 4.6, x - 3.75, f0, f1, 0.2), z0, z1 - z0, { tone: "mid" }, 1, 0.1),
    box(span(x + 3.75, x + 4.6, f0, f1, 0.2), z0, z1 - z0, { tone: "mid" }, 1, 0.1),
    box(bridge, z1, z2 - z1, { tone: "mid", inner: edgeShine([bridge.x + 0.8, f1, z2 - 0.15], [bridge.x + bridge.w - 0.8, f1, z2 - 0.15], 1.5) }, 2, 0.25),
    D([at([x - 4.1, f1, (z1 + z2) / 2]), at([x + 4.1, f1, (z1 + z2) / 2])], { size: 0.3 }))
    + M("ink", S(G.disc(0, 0.2, 0.72, G.frameOf([x, f1, (z1 + z2) / 2], Y3, X3, Z3), P), { tone: "mid" }));
}
// The reader's lamp, and its punch or feeler: a rod through the bridge with a knob that dips onto the frame.
function readerMoving(side, lamp, dip) {
  const x = side * C.READER.x;
  const [, z1, z2] = READ_Z;
  const out = [lensY(x, READ_FRONT[1] + 0.22, (z1 + z2) / 2, 0.52, `rb-lens${lamp ? " rb-" + lamp : ""}`)];
  const y = (READ_BACK[0] + READ_FRONT[1]) / 2;
  const top = z2 + 1.4 - 0.8 * dip;
  out.push(M("ink", cyl(x, y, 0.3, z2, top - z2, { tone: "mid", crease: "none" }, 8), S(G.sphereOf([x, y, top + 0.35], 0.55, P), { tone: "mid" })));
  return out.join("");
}

// --- one line: dough tube, gate, belt, oven, chute and baskets ------------------------------------------

// The dough tube over each belt's outer end: a glass tube on a post, the stock stacked in it, an escapement at
// its foot and a covered bin over it. `stock` is how many balls are in the tube, `drop` how many pitches the
// stack still has to fall after a ball has gone, `refill` the balls still falling in from the bin (each its
// seat and its height above it), `falling` the ball on its way out, drawn behind the collar.
const CLAMPS = () => [C.TUBE.z0 + 4, TUBE_TOP - 4.6];
function tubePost(side) {
  const { TUBE } = C;
  const x = side * TUBE.x, y = -6.8;
  const top = TUBE_TOP - 4;
  return grounded(x, y, 1.6, { h: top, w: 0.9, o: 0.6 }) + M("marble", box(span(x - 1.4, x + 1.4, y - 1.4, y + 1.4, 0.3), 0, 0.8, { tone: "mid" }, 2, 0.2), box(span(x - 0.65, x + 0.65, y - 0.65, y + 0.65, 0.15), 0.8, top - 0.8, { tone: "mid", inner: edgeShine([x + 0.65, y + 0.65, 2], [x + 0.65, y + 0.65, top - 1], 4) }, 1, 0.1))
    + M("ink", ...CLAMPS().map((z) => brightRod([x, y + 0.65, z], [x, -TUBE.r - 0.3, z], 0.28, { tone: "mid" }, 8, 0.6)));
}
function tube(side, stock, drop, refill, fall, falling = "") {
  const { TUBE } = C;
  const x = side * TUBE.x, r = TUBE.r, z0 = TUBE.z0;
  const inner = r - 0.2, outer = r + 0.65, bottom = z0 - TUBE.collar;
  const collar = (d) => M("jade", S({ fill: d, outline: d }, { tone: "mid", flat: true }));
  const glass = k.cylinder(x, 0, r, z0, TUBE_TOP - z0, P, 28);
  const out = [`<path class="rb-glass-back" d="${glass.fill}"/>`,
    collar(bandD(x, 0, inner, bottom, z0, true)), collar(lipD(x, 0, inner, outer, z0, true))];
  // Each clamp is a whole ring: its back half, where the post's arm takes hold, shows through the glass.
  for (const z of CLAMPS()) { const d = bandD(x, 0, r + 0.3, z - 0.45, z + 0.45, true); out.push(M("ink", S({ fill: d, outline: d }, { tone: "mid", flat: true }))); }
  const ball = (c) => placed(c, "dough", () => doughSvg([0, 0, 0]));
  out.push(falling);
  for (let i = 0; i < stock - refill.length; i++) out.push(ball(tubeSeat(side, i, drop)));
  for (const [i, lift] of refill) if (tubeSeat(side, i)[2] + lift < TUBE_TOP + 1) out.push(ball(tubeSeat(side, i, lift / PITCH)));
  out.push(`<path class="rb-glass" d="${glass.fill}"/>`, L(glass.outline, { tone: "mid" }), k.fadeLineSvg([at([x - r * 0.42, r * 0.82, z0 + 2.5]), at([x - r * 0.42, r * 0.82, TUBE_TOP - 2.5])], { fade: [2.4, 2.4], tone: "hi", className: "rb-glass-shine" }));
  for (const z of CLAMPS()) { const d = bandD(x, 0, r + 0.3, z - 0.45, z + 0.45); out.push(M("ink", S({ fill: d, outline: d }, { tone: "mid", flat: true }))); }
  // The escapement: a jade collar round the tube's foot, and the tab that swings out to let one ball go.
  out.push(collar(bandD(x, 0, outer, bottom, z0)), collar(lipD(x, 0, inner, outer, z0, false)),
    D(G.dotsOf(FV(x, 0, bottom), TUBE.collar / 2, outer + 0.02, 6, P, { phase: 0.4 }), { size: 0.3 }));
  const swing = fall > 0 && fall < 1 ? Math.sin(Math.PI * Math.min(1, fall * 2.4)) : 0;
  out.push(M("ink", brightRod([x + side * 0.4, r + 0.55, z0 - 0.65], [x + side * (1.5 + 1.1 * swing), r + 2.3, z0 - 1 - 0.5 * swing], 0.28, { tone: "mid" }, 8, 0.6)));
  // The bin over the tube, its jade lid and knob.
  const B = FV(x, 0, TUBE_TOP);
  out.push(M("ink", cyl(x, 0, r + 0.5, TUBE_TOP - 0.2, 0.6, { tone: "mid" }, 24, 0.15)), M("marble", S(G.solidOf([[0.4, r + 0.4], [0.9, r + 0.75, 1], [2.1, 3.4, 1], [2.6, 3.6]], B, P, { smooth: true }), { tone: "mid", inner: shine(B, 1, 2.3, r + 0.9, 3.4, 0.8) }), L(G.arcOf(B, 2.3, 3.5, P), { tone: "lo" })),
    M("jade", S(G.disc(2.6, 3.2, 3.3, B, P, { bevel: 0.25 }), { tone: "mid" }), S(G.sphereOf([x, 0, TUBE_TOP + 3.75], 0.6, P), { tone: "mid" })));
  return out.join("");
}
// The belt: two side rails, the rubber band between them, a roller at each end and two pairs of legs.
const beltZ = C.BELT.z;
// The belt is drawn in three lengths: the one beyond the oven's hidden end, the one inside it (seen only through
// its mouth) and the one in front of its open end, each in its own place among the oven's parts.
function beltSpans(side) {
  const { BELT, OVEN } = C;
  const inner = [BELT.x0, OVEN.x0], middle = [OVEN.x0, OVEN.x1], outer = [OVEN.x1, BELT.x1];
  const innerSeen = endFaces(side).some((x) => Math.abs(x) === OVEN.x0);
  return { far: innerSeen ? outer : inner, middle, near: innerSeen ? inner : outer };
}
function belt(side, [u0, u1]) {
  const { BELT } = C;
  const xa = side * u0, xb = side * u1;
  const out = [];
  const railDepth = 1.8;
  for (const u of [19.4, 52.2].filter((u) => u > u0 && u < u1)) {
    const x = side * u;
    const leg = (s) => box(span(x - 0.6, x + 0.6, s * (BELT.half + 0.4) - 0.6, s * (BELT.half + 0.4) + 0.6, 0.15), 0, beltZ - railDepth, { tone: "mid" }, 1);
    out.push(M("ink", leg(-1), box(span(x - 0.5, x + 0.5, -BELT.half + 0.2, BELT.half - 0.2, 0.1), 2.6, 0.9, { tone: "mid" }, 1), leg(1)));
  }
  // The rails overrun the band at the belt's two real ends, where its rollers turn.
  const ra = u0 === BELT.x0 ? -0.6 : 0, rb = u1 === BELT.x1 ? 0.6 : 0;
  const band = span(xa, xb, -BELT.half, BELT.half, u0 === BELT.x0 || u1 === BELT.x1 ? 0.2 : 0);
  const sideRail = (s) => {
    const rail = span(xa + side * ra, xb + side * rb, s * BELT.half + (s < 0 ? -0.9 : 0), s * BELT.half + (s < 0 ? 0 : 0.9), 0.2);
    return box(rail, beltZ - railDepth, 2.4, { tone: "mid", inner: s > 0 ? edgeShine([xa, rail.y + rail.d, beltZ + 0.55], [xb, rail.y + rail.d, beltZ + 0.55], 3) : "" }, 2, 0.15);
  };
  out.push(M("ink", sideRail(-1), box(band, beltZ - 0.9, 0.9, { tone: "lo" }, 2, 0.1), sideRail(1)));
  // The rollers' axle caps on the near rail, at the belt's real ends.
  out.push(D([[u0, BELT.x0], [u1, BELT.x1]].filter(([u, end]) => u === end).map(([u]) => at([side * u, BELT.half + 0.9, beltZ - 0.6])), { size: 0.45 }));
  return out.join("");
}
// The cleats across the band, carried along as the belt runs.
function cleats(side, travel, [u0, u1]) {
  const { BELT } = C;
  const lines = [];
  const step = 3;
  const off = ((travel % step) + step) % step;
  for (let u = BELT.x0 + 0.6 + off; u < BELT.x1 - 0.4; u += step) if (u > u0 + 0.2 && u < u1 - 0.2) lines.push(k.pathOf([at([side * u, -BELT.half, beltZ]), at([side * u, BELT.half, beltZ])]));
  return L(lines.join(""), { tone: "faint" });
}
// The gate across the belt: a plate that slides up between two grooved posts under a crossbar; the back post
// takes the reader's link. The private gate carries a lock on its front post; the public one only the plate
// the lock was screwed to.
const GATE_POST = 6.2;
function gateBack(side) {
  const x = side * C.GATE;
  // The back post rises on past the crossbar to carry the line's reader.
  const top = READ_Z[0];
  return grounded(x, -GATE_POST, 1.4, { h: top, w: 0.8, o: 0.5 }) + M("marble", box(span(x - 1.2, x + 1.2, -GATE_POST - 1.2, -GATE_POST + 1.2, 0.3), 0, 0.7, { tone: "mid" }, 2, 0.2), box(span(x - 0.7, x + 0.7, -GATE_POST - 0.7, -GATE_POST + 0.7, 0.15), 0.7, top - 0.7, { tone: "mid", inner: edgeShine([x + 0.7, -GATE_POST + 0.7, 2], [x + 0.7, -GATE_POST + 0.7, top - 1], 5) }, 1, 0.1));
}
function gatePlate(side, lift) {
  const x = side * C.GATE;
  // The plate rides in the posts' grooves above the side rails; a tongue below it closes the gap between them.
  // Raised, its top stops just under the crossbar.
  const z = beltZ + 0.3 + 4.4 * lift;
  const plan = span(x - 0.4, x + 0.4, -GATE_POST + 0.5, GATE_POST - 0.5, 0.1);
  const tongue = span(x - 0.35, x + 0.35, -C.BELT.half + 0.15, C.BELT.half - 0.15, 0.1);
  return M("marble", box(tongue, z, 1, { tone: "mid" }, 1, 0.1), box(plan, z + 0.9, 5.4, { tone: "mid", inner: edgeShine([x + side * 0.4, plan.y + 0.6, z + 6], [x + side * 0.4, plan.y + plan.d - 0.6, z + 6], 2) }, 1, 0.15), D([at([x + 0.4, 0, z + 4.9])], { size: 0.42 }));
}
function gateFront(side) {
  const x = side * C.GATE;
  const out = [grounded(x, GATE_POST, 1.4, { h: 21, w: 0.8, o: 0.5 }), M("marble", box(span(x - 1.2, x + 1.2, GATE_POST - 1.2, GATE_POST + 1.2, 0.3), 0, 0.7, { tone: "mid" }, 2, 0.2), box(span(x - 0.7, x + 0.7, GATE_POST - 0.7, GATE_POST + 0.7, 0.15), 0.7, 19.3, { tone: "mid" }, 1, 0.1)),
    M("marble", box(span(x - 0.9, x + 0.9, -GATE_POST - 0.9, GATE_POST + 0.9, 0.3), 20, 1.4, { tone: "mid", inner: edgeShine([x - 0.9, -GATE_POST + 0.4, 21.3], [x - 0.9, GATE_POST - 0.4, 21.3], 2) }, 2, 0.2), D([at([x, GATE_POST + 0.9, 20.7])], { size: 0.34 }))];
  if (side > 0) {
    // Where the lock was: its plate, four screw holes and the two bores the cylinders left.
    const u = x - LOCK.u;
    const plate = span(u - 2.4, u + 2.4, GATE_POST + 0.7, GATE_POST + 1.1, 0.2);
    out.push(M("marble", box(plate, 10.8, 7.4, { tone: "mid" }, 1, 0.1)));
    const fy = GATE_POST + 1.12;
    out.push(`<g transform="${faceY(fy)}">${L(rectD(u - 2.1, -18, u + 2.1, -11.1, 0.5), { tone: "faint" })}</g>`, D([[u - 1.7, 17.4], [u + 1.7, 17.4], [u - 1.7, 11.4], [u + 1.7, 11.4]].map(([v, z]) => at([v, fy, z])), { size: 0.36, tone: "lo" }),
      lensY(u, fy, LOCK.keys.c, 0.62, "rb-bore"), lensY(u, fy, LOCK.keys.i, 0.62, "rb-bore"));
  }
  return out.join("");
}
// The private lock on the left gate's front post: two key cylinders, the controller's above, the affected's
// below. A green bezel admits its key; a red one refuses it. Each key's bow turns a quarter when it opens the
// gate and shakes when it is refused. The red flag on its mast stands for a capital core.
// The lock sits on the post's front, toward the oven, so the dough tube beyond it stays in view.
const LOCK = { u: 2.3, y: GATE_POST + 0.7, d: 3.2, z: 10.8, h: 7.4, keys: { c: 16.2, i: 12.9 } };
function lockBox() {
  const x = -C.GATE + LOCK.u;
  const plan = span(x - 2.6, x + 2.6, LOCK.y, LOCK.y + LOCK.d, 0.5);
  return boxCast(plan, LOCK.z, LOCK.h, 0.25) + M("ink", box(plan, LOCK.z, LOCK.h, { tone: "mid", inner: L(k.sideSeam(plan, LOCK.z + LOCK.h - 1.1, P, 3), { tone: "faint" }) }, 3, 0.35), D([[x - 2, LOCK.z + 0.8], [x + 2, LOCK.z + 0.8]].map(([u, z]) => at([u, LOCK.y + LOCK.d, z])), { size: 0.32 }));
}
function lock(state) {
  const x = -C.GATE + LOCK.u, fy = LOCK.y + LOCK.d;
  const out = [];
  for (const who of ["c", "i"]) {
    const z = LOCK.keys[who];
    const F = G.frameOf([x, fy, z], Y3, X3, Z3);
    out.push(M("ink", S(G.disc(0, 0.45, 1.3, F, P, { bevel: 0.12 }), { tone: "mid" })), `<path class="rb-bezel ${state.bezel[who] ? "rb-admit" : "rb-refuse"}" d="${G.circleOf(F, 0.47, 1.08, P, 24)}"/>`, `<path class="rb-keyway" d="${G.circleOf(F, 0.48, 0.62, P, 16)}"/>`);
    // The key: a shank out of the cylinder and a bow, turned by `angle` in the face's plane.
    const a = state.keys[who];
    const K = G.frameOf([x, fy + 0.45, z], Y3, [Math.cos(a), 0, Math.sin(a)], [-Math.sin(a), 0, Math.cos(a)]);
    out.push(M("ink", S(G.prismOf(K, [[-0.26, -0.12], [0.26, -0.12], [0.26, 0.12], [-0.26, 0.12]], 0, 1.1, P), { tone: "mid" })));
    // The bow: a rounded plate, longer than it is tall, with a hole for the ring at its end.
    const bow = Array.from({ length: 20 }, (_, j) => { const t = (j / 20) * Math.PI * 2; return [1.05 * Math.cos(t) * (Math.abs(Math.cos(t)) ** -0.25 || 1) * 0.92, 0.62 * Math.sin(t)]; });
    out.push(M("marble", S(G.prismOf(K, bow, 1.1, 1.45, P), { tone: "mid" })), `<path class="rb-keyhole" d="${G.circleOf(G.frameOf(G.pointOf(K, 1.46, 0.55, 0), Y3, [Math.cos(a), 0, Math.sin(a)], [-Math.sin(a), 0, Math.cos(a)]), 0, 0.2, P, 10)}"/>`);
  }
  return out.join("");
}
// The flag: up the mast and spread out when raised, hanging limp at the foot when lowered.
function flag(up) {
  const x = -C.GATE + LOCK.u + 1.7, y = LOCK.y + 1, z0 = LOCK.z + LOCK.h;
  const top = z0 + 9.4;
  const out = [M("ink", cyl(x, y, 0.55, z0, 0.5, { tone: "mid" }, 12, 0.1), brightRod([x, y, z0 + 0.5], [x, y, top], 0.22, { tone: "mid" }, 8, 1.2)), M("ink", S(G.sphereOf([x, y, top + 0.45], 0.5, P), { tone: "mid" }))];
  // Lowered, the flag hangs limp just clear of the lock's top; raised, it flies at the mast's head.
  const zt = z0 + 4.3 + 4.6 * up;
  const width = 1 + 3.4 * up, drop = 2.6 + (1 - up) * 1.2;
  const n = 10;
  const edge = (zz, sag) => Array.from({ length: n + 1 }, (_, i) => {
    const t = i / n;
    const wave = 0.32 * up * Math.sin(t * Math.PI * 1.6 + 0.4) * t;
    return at([x + t * width, y + wave, zz - sag * t * t * (1 - up)]);
  });
  const topEdge = edge(zt, 0.6), bottom = edge(zt - drop, 0.2).reverse();
  out.push(`<path class="rb-flag" d="${k.pathOf([...topEdge, ...bottom], true)}"/>`);
  return out.join("");
}
// The oven: a vaulted tunnel of marble on a plinth with a jade cornice, banded with jade ribs; a porthole
// and a dial on its front wall, and a mouth in each end where the belt runs through behind a curtain.
const ovenPlan = (side) => span(side * C.OVEN.x0, side * C.OVEN.x1, -C.OVEN.y, C.OVEN.y, 1.2);
const ovenCenter = (side) => side * (C.OVEN.x0 + C.OVEN.x1) / 2;
// The vault's section (u across, v up): straight walls, then a half-round crown.
const VAULT = (() => {
  const { y, base, wall } = C.OVEN;
  const arc = Array.from({ length: 17 }, (_, i) => { const a = Math.PI - (i / 16) * Math.PI; return [y * Math.cos(a), wall + y * Math.sin(a)]; });
  return [[-y, base], ...arc, [y, base]];
})();
const vaultFrame = (side) => G.frameOf([Math.min(side * C.OVEN.x0, side * C.OVEN.x1), 0, 0], X3, Y3, Z3);
const PORT = { r: 1.9, z: 7.6, at: -3.2 };
const DIAL_AT = 4;
function ovenBody(side) {
  const { OVEN } = C;
  const plan = ovenPlan(side);
  const cx = ovenCenter(side);
  const len = OVEN.x1 - OVEN.x0;
  const F = vaultFrame(side);
  const plinth = k.insetPlan(plan, -0.9);
  const out = [boxCast(plinth, 0, OVEN.crown, 0.7), `<path class="iso-halo" d="${k.haloOf(k.insetPlan(plinth, -0.8), 0, 0.1, P)}" style="filter:blur(2.4px);opacity:calc(var(--anatomy-halo-opacity) * .5)"/>`];
  out.push(M("marble", box(plinth, 0, OVEN.base - 0.6, { tone: "mid", inner: L(k.sideSeam(plinth, 1.4, P, 4), { tone: "faint" }) }, 4, 0.4)), M("jade", box(k.insetPlan(plan, -0.4), OVEN.base - 0.6, 0.6, { tone: "mid" }, 4, 0.25)));
  // The vault, its highlight running along where it faces the light, and three jade ribs round it.
  const V = G.viewOf(P), h = halfway();
  let best = 0, bestScore = -2;
  VAULT.forEach(([u, v], i) => { if (i === 0 || i === VAULT.length - 1) return; const n = unit([0, u, v - OVEN.wall > 0 ? v - OVEN.wall : 0]); const score = n[1] * h[1] + n[2] * h[2]; if (score > bestScore) { bestScore = score; best = i; } });
  const [su, sv] = VAULT[best];
  const ribs = [];
  for (const s of [1.6, len / 2 - 0.45, len - 2.5]) {
    const run = VAULT.slice(1, -1).filter(([u, v]) => { const n = unit([0, u, v - OVEN.wall > 0 ? v - OVEN.wall : 0]); return n[1] * V[1] + n[2] * V[2] > 0.02; });
    const at3 = (sx, [u, v]) => at([F.o[0] + sx, u * 1.012, v + (v > OVEN.wall ? (v - OVEN.wall) * 0.012 : 0)]);
    if (run.length > 1) ribs.push(k.pathOf([...run.map((p) => at3(s, p)), ...run.slice().reverse().map((p) => at3(s + 0.9, p))], true));
  }
  // The front wall's porthole and dial, drawn in the wall's own plane.
  const front = OVEN.y;
  const port = G.frameOf([cx + side * PORT.at, front, PORT.z], Y3, X3, Z3);
  const dial = G.frameOf([cx - side * DIAL_AT, front, PORT.z], Y3, X3, Z3);
  out.push(M("marble", S(G.prismOf(F, VAULT, 0, len, P), { tone: "mid", inner: edgeShine([F.o[0] + 1.5, su, sv], [F.o[0] + len - 1.5, su, sv], 4) + (ribs.length ? `<path class="rb-rib" d="${ribs.join("")}"/>` : "") })));
  out.push(M("ink", S(G.disc(0, 0.45, PORT.r + 0.55, port, P, { bevel: 0.15 }), { tone: "mid" }), S(G.disc(0, 0.45, 1.7, dial, P, { bevel: 0.15 }), { tone: "mid" })), `<path class="rb-dial" d="${G.circleOf(dial, 0.47, 1.32, P, 28)}"/>`);
  const ticks = [];
  for (let i = 0; i <= 6; i++) { const a = -2.3 + (4.6 * i) / 6; ticks.push(k.pathOf([at([cx - side * DIAL_AT + 1.32 * Math.sin(a), front + 0.48, PORT.z + 1.32 * Math.cos(a)]), at([cx - side * DIAL_AT + 1.02 * Math.sin(a), front + 0.48, PORT.z + 1.02 * Math.cos(a)])])); }
  out.push(L(ticks.join(""), { tone: "lo" }));
  return out.join("");
}
// The mouth on an end face of the oven (outline in the face's own plane: u across, v down).
const mouthD = (u0) => {
  const { half, z0, z1, spring } = C.MOUTH;
  const arch = Array.from({ length: 13 }, (_, i) => { const a = Math.PI - (i / 12) * Math.PI; return `${n2(u0 + half * Math.cos(a))} ${n2(-(spring + (z1 - spring) * Math.sin(a)))}`; });
  return `M${n2(u0 - half)} ${-z0}L${arch.join("L")}L${n2(u0 + half)} ${-z0}Z`;
};
// Which of the oven's two ends the viewer sees (the one facing +x or −x).
const endFaces = (side) => {
  const V = G.viewOf(P);
  return [C.OVEN.x0, C.OVEN.x1].map((u) => side * u).filter((x) => Math.sign(x - ovenCenter(side)) * V[0] > 0);
};
const portD = (side) => G.circleOf(G.frameOf([ovenCenter(side) + side * PORT.at, C.OVEN.y + 0.47, PORT.z], Y3, X3, Z3), 0, PORT.r, P, 28);
// The oven's dark: each visible mouth and the porthole, glowing with the fire (`heat` 0–1).
function ovenDark(side, heat) {
  const out = [];
  for (const xe of endFaces(side)) {
    const m = planeOf([xe, 0, 0], Y3);
    out.push(`<path class="rb-mouth" transform="${m}" d="${mouthD(0)}"/>`, `<path class="rb-heat" transform="${m}" d="${mouthD(0)}" style="opacity:${n2(heat * 0.5)}"/>`);
    out.push(`<path class="rb-mouth-frame" transform="${m}" d="${mouthD(0)}"/>`);
  }
  out.push(`<path class="rb-mouth" d="${portD(side)}"/>`, `<path class="rb-heat" d="${portD(side)}" style="opacity:${n2(heat)}"/>`);
  return out.join("");
}
// Whatever is inside the oven is seen only through its mouths.
function ovenClip(side) {
  const holes = endFaces(side).map((xe) => `<path transform="${planeOf([xe, 0, 0], Y3)}" d="${mouthD(0)}"/>`);
  return `<clipPath id="rb-oven-${side < 0 ? "a" : "b"}">${holes.join("")}</clipPath>`;
}
// Over it: the porthole's glass, the curtains swinging as a piece pushes through, the dial's needle.
function ovenFront(side, heat, flaps) {
  const { OVEN, MOUTH } = C;
  const out = [`<path class="rb-pane" d="${portD(side)}"/>`, glintAt([ovenCenter(side) + side * PORT.at - 0.7, OVEN.y + 0.5, PORT.z + 0.8], 0.5)];
  // The curtain at each visible mouth: six strips hung from a bar; a strip swings out as a piece pushes by.
  for (const xe of endFaces(side)) {
    const out_ = Math.sign(xe - ovenCenter(side));
    const outlet = xe === side * OVEN.x0;
    const swing = flaps[outlet ? 0 : 1];
    const strips = [];
    for (let i = 0; i < 6; i++) {
      const y0 = -MOUTH.half + 0.35 + i * ((2 * MOUTH.half - 0.7) / 6), y1 = y0 + (2 * MOUTH.half - 0.7) / 6 - 0.22;
      const top = MOUTH.hinge, length = top - MOUTH.hem;
      const pinX = xe + out_ * 0.05;
      const lowZ = top - length * Math.cos(swing), lowX = pinX - side * length * Math.sin(swing);
      strips.push(k.pathOf([at([pinX, y0, top]), at([pinX, y1, top]), at([lowX, y1, lowZ]), at([lowX, y0, lowZ])], true));
    }
    const curtain = `<path class="rb-strip" d="${strips.join("")}"/>`;
    out.push(outlet ? curtain : `<g clip-path="url(#rb-oven-${side < 0 ? "a" : "b"})">${curtain}</g>`);
    out.push(M("ink", box(span(xe, xe + out_ * 0.5, -MOUTH.half - 0.4, MOUTH.half + 0.4, 0.15), MOUTH.spring + 1, 0.6, { tone: "mid" }, 1)));
  }
  // The dial's needle swings over its scale with the fire.
  const dx = ovenCenter(side) - side * DIAL_AT;
  const a = -2.1 + heat * 3.6;
  out.push(L(k.pathOf([at([dx, OVEN.y + 0.5, PORT.z]), at([dx + 1.1 * Math.sin(a), OVEN.y + 0.5, PORT.z + 1.1 * Math.cos(a)])]), { tone: "hi", free: true }), D([at([dx, OVEN.y + 0.52, PORT.z])], { size: 0.3, tone: "hi" }));
  return out.join("");
}
// The chute at the belt's end: a trough on a post, swung to whose basket the next loaf is for.
const chuteDir = (side, angle) => [-side * Math.cos(angle), Math.sin(angle), 0];
const BASKET_ANGLE = (who) => Math.atan2(C.SLOTS[who] - C.PIVOT[1], C.PIVOT[0] - C.BASKET.x);
function chuteFrame(side, angle) {
  const [px, py, pz] = C.PIVOT;
  const [dx, dy] = chuteDir(side, angle);
  return G.frameAlong([side * px, py, pz], [dx * C.CHUTE.reach, dy * C.CHUTE.reach, -C.CHUTE.drop]);
}
const CHUTE_LEN = Math.hypot(C.CHUTE.reach, C.CHUTE.drop);
function chute(side, angle, front) {
  const F = chuteFrame(side, angle);
  const { half, wall: thick, floor, lip, taper, runout } = C.CHUTE;
  const outer = half + thick;
  const V = G.viewOf(P);
  const near = Math.sign(G.dot3(F.u, V)) || 1;
  // The side walls taper into the tip so the tail of a loaf clears them as it turns into the basket.
  const wallEnd = CHUTE_LEN - runout;
  const wallFrame = G.frameOf(F.o, F.u, F.a, F.v);
  const wallShape = [[0, 0], [wallEnd, 0], [wallEnd - taper, lip], [0, lip]];
  const wall = (s) => S(G.prismOf(wallFrame, wallShape, s < 0 ? -outer : half, s < 0 ? -half : outer, P), { tone: "mid" });
  if (front) return M("jade", wall(near));
  const deck = [[-0.45, -outer], [wallEnd, -outer], [CHUTE_LEN, -half], [CHUTE_LEN, half], [wallEnd, outer], [-0.45, outer]];
  return M("jade", S(G.prismOf(G.frameOf(F.o, F.v, F.a, F.u), deck, -floor, 0, P), { tone: "mid" }), wall(-near));
}
// The chute's post and swivel, drawn apart from its trough: the post stands behind the baskets the trough
// reaches over.
function chutePost(side) {
  const [px, py, pz] = C.PIVOT;
  const x = side * px;
  const bearing = pz - C.CHUTE.floor - 0.42;
  return shadow(x, py, 1.3, 0.3, { h: pz, w: 0.9 }) + M("marble", cyl(x, py, 1.25, 0, 0.7, { tone: "mid" }, 18, 0.2), cyl(x, py, 0.55, 0.7, bearing - 1.6, { tone: "mid", crease: "none" }, 10))
    + M("jade", cyl(x, py, 0.8, bearing - 0.9, 0.55, { tone: "mid" }, 14, 0.1), S(G.sphereOf([x, py, bearing], 0.42, P), { tone: "mid" }));
}
// The stand in the middle: two marble steps with a jade nosing, the baskets on its top.
function stand() {
  const { STAND } = C;
  const lower = span(-STAND.w - 1.4, STAND.w + 1.4, -STAND.d - 1.4, STAND.d + 1.4, 1.6);
  const upper = span(-STAND.w, STAND.w, -STAND.d, STAND.d, 1.2);
  const h1 = 1.4, h2 = STAND.top - 0.5;
  const front = `<g transform="${faceY(lower.y + lower.d)}">${L([-1, 1].map((s) => `M${s * STAND.w * 0.5} ${-0.15}V${-(h1 - 0.15)}`).join(""), { tone: "faint" })}</g>`;
  return boxCast(lower, 0, STAND.top, 0.5) + `<path class="iso-halo" d="${k.haloOf(k.insetPlan(lower, -0.8), 0, 0.1, P)}" style="filter:blur(2.4px);opacity:calc(var(--anatomy-halo-opacity) * .5)"/>`
    + M("marble", box(lower, 0, h1, { tone: "mid", inner: front + edgeShine([lower.x + 2, lower.y + lower.d, h1 - 0.15], [lower.x + lower.w - 2, lower.y + lower.d, h1 - 0.15], 6) }, 4, 0.35), box(upper, h1, h2 - h1, { tone: "mid" }, 4, 0.3))
    // The top: a jade nosing round a marble field.
    + M("jade", box(k.insetPlan(upper, -0.35), h2, STAND.top - h2 - 0.12, { tone: "mid", inner: edgeShine([upper.x + 2, upper.y + upper.d + 0.35, STAND.top - 0.2], [upper.x + upper.w - 2, upper.y + upper.d + 0.35, STAND.top - 0.2], 6) }, 4, 0.2))
    + M("marble", box(k.insetPlan(upper, 0.9), STAND.top - 0.12, 0.12, { tone: "mid", flat: true }, 4))
    + D(k.corners(upper, 1.6).map(([px, py]) => at([px, py, STAND.top])), { size: 0.4 })
    // Every basket's and crate's shadow lies on the stand's top before any of them is drawn.
    + [-1, 1].flatMap((side) => WHO.map((who) => {
      const x = side * C.BASKET.x, y = C.SLOTS[who];
      return who === MD.CONTROLLER ? boxCast(span(x - CRATE[0], x + CRATE[0], y - CRATE[1], y + CRATE[1], 0.5), STAND.top, 3.5, 0.5) : shadow(x, y, C.BASKET.r + 0.6, 0.32, { z: STAND.top, h: C.BASKET.h, w: C.BASKET.r * 0.9 });
    })).join("");
}
// A basket of woven rushes for 甲 and for 乙, a crate for 丙, standing on the stand; their loaves are drawn
// inside after them.
const CRATE = [4.7, 3.9, 0.7, 3.5];
const basketFloor = (who) => C.STAND.top + (who === MD.CONTROLLER ? CRATE[2] : C.BASKET.floor);
const basketTop = (who) => C.STAND.top + (who === MD.CONTROLLER ? CRATE[3] : C.BASKET.h);
function basket(side, who) {
  const { BASKET, SLOTS } = C;
  const x = side * BASKET.x, y = SLOTS[who], z0 = C.STAND.top;
  if (who === MD.CONTROLLER) {
    // 丙's crate: a floor and four slatted walls, the far ones first.
    const [hx, hy, floor, top] = CRATE;
    const plan = span(x - hx, x + hx, y - hy, y + hy, 0.5);
    const wall = (p, inner = "") => box(p, basketFloor(who), top - floor, { tone: "mid", inner }, 1, 0.1);
    const slats = `<g transform="${faceY(y + hy)}">${L(`M${x - hx} ${-(z0 + 1.7)}H${x + hx}M${x - hx} ${-(z0 + 2.7)}H${x + hx}`, { tone: "faint" })}</g>`;
    const walls = [span(x - hx, x + hx, y - hy, y - hy + 0.6, 0.1), span(x - hx, x - hx + 0.6, y - hy + 0.6, y + hy - 0.6, 0.1), span(x + hx - 0.6, x + hx, y - hy + 0.6, y + hy - 0.6, 0.1)].sort((a, b) => k.depthOf([a.x, a.y, 0], P) - k.depthOf([b.x, b.y, 0], P));
    return M("marble", box(plan, z0, floor, { tone: "mid" }, 3, 0.2), ...walls.map((plan) => wall(plan)), wall(span(x - hx, x + hx, y + hy - 0.6, y + hy, 0.1), slats));
  }
  const F = FV(x, y, z0);
  const profile = [[0, BASKET.foot], [0.6, BASKET.r - 0.65, 1], [BASKET.h - 0.6, BASKET.r - 0.1, 1], [BASKET.h, BASKET.r]];
  const inner = BASKET.r - BASKET.wall;
  const opening = k.pathOf(basketOpening(side, who).map(at), true);
  const cavity = G.lathe([[BASKET.h, inner], [BASKET.floor, BASKET.foot - BASKET.wall], [BASKET.floor, 0]], F, P, { fill: "faces" });
  const id = `rb-bowl-${side}-${who}`;
  return M("marble", S(G.lathe(profile, F, P, { fill: "surface" }), { tone: "mid", inner: k.fadedSvg(G.ribsOf(F, 0.6, BASKET.h - 0.6, BASKET.r - 0.65, 28, P, { r1: BASKET.r - 0.1, fade: [0.15, 0.6] }), { tone: "faint" }) + L(G.arcOf(F, 0.6, BASKET.r - 0.65, P) + G.arcOf(F, 1.5, BASKET.r - 0.44, P) + G.arcOf(F, 2.3, BASKET.r - 0.22, P) + G.arcOf(F, BASKET.h - 0.6, BASKET.r - 0.1, P), { tone: "lo" }) }), glint(F, 1.8, BASKET.r - 0.35, 0.8),
    `<clipPath id="${id}"><path d="${opening}"/></clipPath><g clip-path="url(#${id})">${S({ ...cavity, fill: opening, outline: "" }, { tone: "lo" })}</g>`,
    L(opening, { tone: "lo" }));
}
// The outline a basket or crate stands in: its foot and its rim.
const basketBody = (side, who) => {
  const { BASKET, SLOTS, STAND } = C;
  const x = side * BASKET.x, y = SLOTS[who];
  if (who === MD.CONTROLLER) return k.boxCorners(span(x - CRATE[0], x + CRATE[0], y - CRATE[1], y + CRATE[1]), STAND.top, basketTop(who));
  const ring = (r, z) => Array.from({ length: 32 }, (_, i) => { const a = (i / 32) * Math.PI * 2; return [x + r * Math.cos(a), y + r * Math.sin(a), z]; });
  return [...ring(BASKET.foot, STAND.top), ...ring(BASKET.r, basketTop(who))];
};
const basketOpening = (side, who) => {
  const { BASKET, SLOTS } = C;
  const x = side * BASKET.x, y = SLOTS[who];
  const z = basketTop(who), r = BASKET.r - BASKET.wall;
  if (who === MD.CONTROLLER) return k.corners(span(x - CRATE[0] + 0.6, x + CRATE[0] - 0.6, y - CRATE[1] + 0.6, y + CRATE[1] - 0.6)).map(([px, py]) => [px, py, z]);
  return Array.from({ length: 48 }, (_, i) => { const a = (i / 48) * Math.PI * 2; return [x + r * Math.cos(a), y + r * Math.sin(a), z]; });
};

// --- the pieces: a ball of dough, and the loaf it bakes into -------------------------------------------

const LOAF_PROFILE = [[0, 0.5], [0.4, 1.25, 1], [1.35, 1.75, 1], [2.9, C.LOAF, 1], [4.45, 1.75, 1], [5.4, 1.25, 1], [5.8, 0.5]];
const MERIDIAN_INSET = 0.02;
function doughSvg(c) {
  return M("dough", S(G.sphereOf(c, C.DOUGH, P), { tone: "mid" }), ballGlint(c, C.DOUGH, 0.42));
}
// The loaf's meridian at t (0–1 along it): its station from the middle and its radius.
const loafAt = (t) => {
  const s = t * C.LOAF_LEN;
  for (let j = 1; j < LOAF_PROFILE.length; j++) {
    const [s0, r0] = LOAF_PROFILE[j - 1], [s1, r1] = LOAF_PROFILE[j];
    if (s <= s1) { const u = (s - s0) / (s1 - s0), e = (1 - Math.cos(u * Math.PI)) / 2; return [s - C.LOAF_LEN / 2, r0 + (r1 - r0) * e]; }
  }
  return [C.LOAF_LEN / 2, LOAF_PROFILE.at(-1)[1]];
};
function loafMeridian(bake) {
  return Array.from({ length: 13 }, (_, j) => {
    const t = MERIDIAN_INSET + ((1 - 2 * MERIDIAN_INSET) * j) / 12;
    const a = Math.PI * t, ball = [-C.DOUGH * Math.cos(a), C.DOUGH * Math.sin(a)];
    const [ls, lr] = loafAt(t);
    return [ball[0] + (ls - ball[0]) * bake, ball[1] + (lr - ball[1]) * bake, j && j < 12 ? 1 : 0];
  });
}
// A piece baking: the ball's meridian draws out into the loaf's and its skin browns.
function loafSvg(c, dir, bake = 1) {
  const d = unit(dir);
  const F = G.frameAlong(c, d);
  const profile = loafMeridian(bake);
  const up = unit([-d[2] * d[0], -d[2] * d[1], 1 - d[2] * d[2]]);
  const side = unit(G.cross3(up, d));
  const scores = [-1.5, 0, 1.5].map((s) => {
    const o = c.map((v, i) => v + d[i] * s + up[i] * ((C.DOUGH + (C.LOAF - C.DOUGH) * bake) * 0.97 - (s ? 0.12 : 0)));
    const a = o.map((v, i) => v + d[i] * 0.6 + side[i] * 0.85), b = o.map((v, i) => v - d[i] * 0.6 - side[i] * 0.85);
    const m = o.map((v, i) => v + up[i] * 0.05);
    return k.pathOf([at(a), at(m.map((v, i) => v + d[i] * 0.18 - side[i] * 0.05)), at(b), at(m.map((v, i) => v - d[i] * 0.12 + side[i] * 0.12))], true);
  });
  const body = S(G.solidOf(profile, F, P, { smooth: true }), { tone: "mid" });
  const top = C.DOUGH + (C.LOAF - C.DOUGH) * bake;
  const skin = bake >= 0.999 ? M("crust", body) : M("dough", body) + `<g style="opacity:${n2(bake)}">${M("crust", body)}</g>`;
  return skin + (bake > 0.4 ? `<g style="opacity:${n2(Math.min(1, (bake - 0.4) / 0.5))}">${M("crust", `<path class="rb-score" d="${scores.join("")}"/>`)}</g>` : "") + glintAt(c.map((v, i) => v + up[i] * top * 0.8 + halfway()[i] * 0.4), 0.42 + 0.13 * bake);
}
// A piece's look depends on how far it has baked and which way it points, not on where it is: each look is
// drawn once at the origin and moved into place, until the view turns.
const LOOKS = new Map();
let looksFor = null;
function placed(c, key, make) {
  if (looksFor !== P) { LOOKS.clear(); looksFor = P; }
  if (!LOOKS.has(key)) { if (LOOKS.size > 600) LOOKS.clear(); LOOKS.set(key, make()); }
  const o = at([0, 0, 0]), p = at(c);
  return `<g transform="translate(${n2(p[0] - o[0])} ${n2(p[1] - o[1])})">${LOOKS.get(key)}</g>`;
}
const bakedShape = (piece) => Math.round((piece.bake ?? 0) * 30) / 30;
const pieceSvg = (piece) => {
  const bake = bakedShape(piece);
  const dir = (piece.dir ?? X3).map((v) => Math.round(v * 200) / 200);
  const svg = bake > 0.001 ? placed(piece.c, `${bake}|${dir}`, () => loafSvg([0, 0, 0], dir, bake)) : placed(piece.c, "dough", () => doughSvg([0, 0, 0]));
  return piece.fade !== undefined && piece.fade < 1 ? `<g style="opacity:${n2(Math.max(0, piece.fade))}">${svg}</g>` : svg;
};

// --- the slots a moving piece is drawn in -----------------------------------------------------------------

const axialReach = (piece) => {
  const bake = bakedShape(piece);
  return bake ? C.DOUGH * Math.cos(Math.PI * MERIDIAN_INSET) * (1 - bake) + C.LOAF_LEN * (0.5 - MERIDIAN_INSET) * bake : C.DOUGH;
};
function piecesIn(wing, slot) {
  return wing.pieces.filter((piece) => {
    if (piece.at === "basket") return slot === "basket-" + piece.to;
    if (piece.at !== "belt") return slot === piece.at;
    const u = Math.abs(piece.c[0]), reach = axialReach(piece);
    if (slot === "near") return u > C.GATE;
    if (slot === "between") return u <= C.GATE && u + reach > C.OVEN.x1;
    if (slot === "inside") return u - reach < C.OVEN.x1 && u + reach > C.OVEN.x0;
    return slot === "beyond" && u - reach < C.OVEN.x0;
  });
}
// At the visible end only the section in front of the face may cover the oven shell.
// Project that section's silhouette and use it to reveal the uncut piece, with no seam at the cut.
function ovenPiece(piece, edge, id) {
  const cut = edge - piece.c[0];
  const reach = axialReach(piece);
  const svg = pieceSvg(piece);
  if (cut <= -reach) return svg;
  if (cut >= reach) return "";
  const bake = bakedShape(piece);
  const radius = bake ? G.profileCurve(loafMeridian(bake)).radius : (s) => Math.sqrt(Math.max(0, C.DOUGH ** 2 - s ** 2));
  const profile = Array.from({ length: 25 }, (_, i) => {
    const s = cut + (reach - cut) * i / 24;
    return [s, radius(s)];
  });
  const d = G.outlineOf(profile, G.frameAlong(piece.c, X3), P, { fill: "hull", smooth: false }).fill;
  return `<clipPath id="${id}"><path d="${d}"/></clipPath><g clip-path="url(#${id})">${svg}</g>`;
}

// --- composition: back to front ---------------------------------------------------------------------------

const WHO = ["丙", "甲", "乙"];
function wingParts(side) {
  const tag = side < 0 ? "a" : "b";
  const baskets = WHO.map((who) => [who, k.depthOf([side * C.BASKET.x, C.SLOTS[who], 0], P)]).sort((a, b) => a[1] - b[1]).map(([who]) => who);
  // The tape's middle post stands just in front of the private line's crate.
  const basketRow = baskets.map((who) => basket(side, who) + `<g data-part="${tag}-basket-${who}"></g>` + (side < 0 && who === MD.CONTROLLER ? guideShaft() : "")).join("");
  const spans = beltSpans(side);
  const beltPart = belt(side, spans.far) + `<g data-part="${tag}-cleats-far"></g>`;
  // The oven, then what shows through its mouths (the belt inside and any piece on it), then its curtains, and
  // the length of belt in front of its open end.
  const oven = ovenBody(side) + ovenClip(side) + `<g data-part="${tag}-dark"></g><g clip-path="url(#rb-oven-${tag})">${belt(side, spans.middle)}<g data-part="${tag}-cleats-middle"></g><g data-part="${tag}-inside"></g></g>`
    + belt(side, spans.near) + `<g data-part="${tag}-cleats-near"></g>`;
  const slot = (name) => `<g data-part="${tag}-${name}"></g>`;
  const trough = slot("chute") + slot("chuted") + slot("chute-front");
  if (side < 0) {
    return [tubePost(side), beltPart, slot("near"), slot("hopper"), slot("gate"), slot("between"), gateFront(side), lockBox(), slot("lock"), oven, slot("beyond"), slot("oven"), slot("flag"), chutePost(side), stand(), basketRow, trough].join("");
  }
  return [basketRow, chutePost(side), trough, tubePost(side), beltPart, slot("beyond"), oven, slot("oven"), slot("between"), slot("gate"), slot("near"), gateFront(side), slot("hopper")].join("");
}
function composition(state) {
  return [
    base(),
    `<g data-part="counter"></g>`,
    `<g data-part="lamps"></g>`,
    reelBase(-1), reelBase(1),
    `<g data-part="reels"></g>`,
    gateBack(-1), gateBack(1),
    guideShadow(),
    guideSleeve(),
    readerBack(-1), readerBack(1),
    `<g data-part="tape"></g>`,
    readerFront(-1), readerFront(1),
    `<g data-part="readers"></g>`,
    wingParts(-1),
    wingParts(1),
    `<g class="rb-hits">${hitAreas()}</g>`,
  ].join("");
}
function hitAreas() {
  const zone = (name, points) => `<path data-hit="${name}" d="${k.pathOf(G.hullOf(points.map(at)), true)}"/>`;
  const boxPts = (x0, y0, x1, y1, z0, z1) => k.boxCorners({ x: x0, y: y0, w: x1 - x0, d: y1 - y0 }, z0, z1);
  const x = -C.GATE + LOCK.u, fy = LOCK.y + LOCK.d;
  return [
    zone("tape", boxPts(-C.REEL.x - 9, C.REEL.y - 9, C.REEL.x + 9, C.TAPE.y + 1, C.TAPE.z0 - 2, C.TAPE.z1 + 3)),
    zone("c", boxPts(x - 3, LOCK.y, x + 3, fy + 2, (LOCK.keys.c + LOCK.keys.i) / 2, LOCK.z + LOCK.h + 9)),
    zone("i", boxPts(x - 3, LOCK.y, x + 3, fy + 2, LOCK.z - 1, (LOCK.keys.c + LOCK.keys.i) / 2)),
  ].join("");
}

// The parts that change, each drawn from the state into its slot.
function partsOf(state) {
  const parts = {
    counter: () => counter(state),
    lamps: () => faceLamps(-1, state.wings[0].bread) + faceLamps(1, state.wings[1].bread),
    reels: () => reel(-1, state.q) + reel(1, state.q),
    tape: () => tape(state.q, state.stamps, state.stampFade),
    readers: () => readerMoving(-1, state.lamps[0], state.dips[0]) + readerMoving(1, state.lamps[1], state.dips[1]),
  };
  for (const side of [-1, 1]) {
    const tag = side < 0 ? "a" : "b";
    const wing = state.wings[side < 0 ? 0 : 1];
    for (const span_ of ["far", "middle", "near"]) parts[`${tag}-cleats-${span_}`] = () => cleats(side, state.travel, beltSpans(side)[span_]);
    parts[`${tag}-hopper`] = () => tube(side, wing.stock, wing.drop, wing.refill, wing.fall, piecesIn(wing, "fall").map(pieceSvg).join(""));
    parts[`${tag}-gate`] = () => gatePlate(side, wing.gate);
    const nearOven = side < 0 ? "beyond" : "between";
    const edge = side * C.OVEN[side < 0 ? "x0" : "x1"];
    for (const name of ["near", "between", "beyond"]) parts[`${tag}-${name}`] = () => piecesIn(wing, name).map((piece, i) =>
      name === nearOven ? ovenPiece(piece, edge, `rb-cut-${tag}-${i}`) : pieceSvg(piece)).join("");
    parts[`${tag}-dark`] = () => ovenDark(side, wing.heat);
    parts[`${tag}-inside`] = () => piecesIn(wing, "inside").map(pieceSvg).join("");
    parts[`${tag}-oven`] = () => ovenFront(side, wing.heat, wing.flaps);
    parts[`${tag}-chute`] = () => chute(side, wing.chute, false);
    parts[`${tag}-chute-front`] = () => chute(side, wing.chute, true);
    parts[`${tag}-chuted`] = () => piecesIn(wing, "chute").map(pieceSvg).join("");
    for (const who of WHO) {
      parts[`${tag}-basket-${who}`] = () => {
        const id = `rb-in-${tag}-${who === "丙" ? "c" : who === "甲" ? "j" : "y"}`;
        const pieces = piecesIn(wing, "basket-" + who);
        const across = who === MD.CONTROLLER ? 0 : 1;
        const inside = pieces.filter((piece) => piece.seated || piece.fly >= LAND_ALIGN).sort((a, b) => a.c[across] - b.c[across]);
        return insideClip(id, basketOpening(side, who), basketBody(side, who))
          + `<g clip-path="url(#${id})">${inside.map(pieceSvg).join("")}</g>`
          + pieces.filter((piece) => !piece.seated && piece.fly < LAND_ALIGN).map(pieceSvg).join("");
      };
    }
    if (side < 0) { parts["a-lock"] = () => lock(state); parts["a-flag"] = () => flag(state.flag); }
  }
  return parts;
}

// The resting scene: the private law at (1, 0), the tape at its start, nothing baked yet.
// Where the n-th loaf for `to` lies in its basket: along the basket, the second beside the first.
function seatAt(side, to, n) {
  const across = (n % 2 ? 1 : -1) * (C.LOAF + 0.08);
  const lift = basketFloor(to) + C.LOAF;
  return to === "丙" ? [side * (C.BASKET.x + across), C.SLOTS[to], lift] : [side * C.BASKET.x, C.SLOTS[to] - across, lift];
}
const LAND_ALIGN = 0.62;
// The scene the figure opens on: the private law at (1, 0) with its run and its replay just finished, both
// lines' loaves in the same baskets, the stamped tape at the public reader.
function restState() {
  const given = MD.run(MD.lawOf(1, 0), MD.S0, MD.W);
  const wing = (side) => {
    const count = { 甲: 0, 乙: 0, 丙: 0 };
    const pieces = given.items.filter((item) => item.done).map((item) => ({ to: item.to, at: "basket", seated: true, bake: 1, dir: item.to === "丙" ? Y3 : X3, c: seatAt(side, item.to, count[item.to]++) }));
    return { stock: given.state.dough, drop: 0, dv: 0, refill: [], rv: [], fall: 0, gate: 0, gateGoal: 0, heat: 0, flaps: [0, 0], chute: BASKET_ANGLE(given.items[given.items.length - 1].to), cv: 0, pieces, bread: { ...given.state.bread } };
  };
  return { law: { c: 1, i: 0 }, bezel: { c: 1, i: 0 }, keys: { c: 0, i: 0 }, flag: 1, fv: 0, q: STEPS, stamps: given.items.map((item) => (item.done ? "ok" : "no")), stampFade: 1, lamps: [null, null], dips: [0, 0], counts: [MD.W.length, MD.W.length], travel: 0, speed: 0, wings: [wing(-1), wing(1)] };
}
const REST = restState();
const fill = (state) => { const parts = partsOf(state); return composition(state).replace(/<g data-part="([^"]+)"><\/g>/g, (all, name) => (parts[name] ? `<g data-part="${name}">${parts[name]()}</g>` : all)); };

const svg = k.figureSvg({
  width: WIDTH,
  height: HEIGHT,
  className: "rb-svg",
  label: "A bread bench with two identical lines that run in from either end to two rows of baskets side by side in the middle. Each line drops a ball of dough from a glass tube onto a belt, carries it through a gate and a vaulted oven, and slides the loaf down a chute into the basket of whoever it is for: 甲, 乙, or 丙, who controls the ovens. The left line's gate is locked: 丙's key turns, the affected's key is refused, and a red flag marks a capital core. One order tape runs high over both lines from reel to reel; the left reader stamps each request with what actually happened, and the tape is wound across to the right line, whose lock has been taken off, to be replayed entry by entry. A refused entry becomes a presentation with no effect, so both rows of baskets end with the same loaves, both tubes with the same dough left, and both counts with the same number of positions.",
  body: fill(REST),
});

const CSS = `
.rb-svg{--anatomy-spec:#ffffff;--fig-shadow:.52;--rb-fault:var(--cinnabar,#c8372d);--rb-ok:#9fc7a9}
.iso[data-theme="dark"] .rb-svg{--fig-shadow:.7}
.iso[data-theme="dark"] .rb-svg .glint{opacity:.32}
.rb-svg [data-mat="jade"]{--anatomy-spec:#f3faf4}
.rb-svg [data-mat="ink"]{--anatomy-spec:#9aa4a6}
.iso[data-theme="dark"] .rb-svg [data-mat="marble"],.iso[data-theme="dark"] .rb-svg{--anatomy-spec:#9a9c98}
.iso[data-theme="dark"] .rb-svg [data-mat="jade"]{--anatomy-spec:#8fb39b}
.iso[data-theme="dark"] .rb-svg [data-mat="ink"]{--anatomy-spec:#626a6c}
.rb-svg .iso-line[data-tone="spec"]{stroke:var(--anatomy-spec)}
.rb-svg .spec{stroke-width:1.6;stroke-linecap:round;opacity:.42;filter:blur(.8px)}
.rb-svg .glint{fill:var(--anatomy-spec);stroke:none;filter:blur(1.5px);opacity:.5}
.rb-svg [data-mat="crust"]{--anatomy-paper:#e4d6bc;--anatomy-face:#e9dcc3;--anatomy-top:#f1e7d3;--anatomy-shade-0:#c7b494;--anatomy-shade-1:#d2c1a3;--anatomy-shade-2:#dccdb1;--anatomy-shade-3:#e6d9c0;--anatomy-lit-top:#f7f0e2;--anatomy-lit-shade:#dfd1b6;--anatomy-hi:#4a3f2c;--anatomy-mid:#9a8a6c;--anatomy-lo:#b4a586;--anatomy-faint:#e2d6bf;--anatomy-dot:#5a4d36;--anatomy-spec:#fffaf0}
.rb-svg [data-mat="dough"]{--anatomy-paper:#f3f0e8;--anatomy-face:#f7f4ed;--anatomy-top:#fbf9f4;--anatomy-shade-0:#d9d4c8;--anatomy-shade-1:#e2ded3;--anatomy-shade-2:#eae6dc;--anatomy-shade-3:#f1eee6;--anatomy-lit-top:#fffefb;--anatomy-lit-shade:#ede9e0;--anatomy-hi:#4a4639;--anatomy-mid:#9b9585;--anatomy-lo:#bbb5a6;--anatomy-faint:#e5e1d7;--anatomy-dot:#5a5545;--anatomy-spec:#ffffff}
.iso[data-theme="dark"] .rb-svg [data-mat="crust"]{--anatomy-paper:#5a5242;--anatomy-face:#655c4a;--anatomy-top:#716752;--anatomy-shade-0:#3c362c;--anatomy-shade-1:#453f33;--anatomy-shade-2:#4f483a;--anatomy-shade-3:#595141;--anatomy-lit-top:#7e735c;--anatomy-lit-shade:#5f5746;--anatomy-hi:#ede3cc;--anatomy-mid:#9c907a;--anatomy-lo:#6e6553;--anatomy-faint:#4a4337;--anatomy-dot:#ede3cc;--anatomy-spec:#c9bfa8}
.iso[data-theme="dark"] .rb-svg [data-mat="dough"]{--anatomy-paper:#4c4637;--anatomy-face:#58513f;--anatomy-top:#625a47;--anatomy-shade-0:#332e24;--anatomy-shade-1:#3b3529;--anatomy-shade-2:#433d2f;--anatomy-shade-3:#4c4535;--anatomy-lit-top:#6e6550;--anatomy-lit-shade:#514a3a;--anatomy-hi:#ece2c9;--anatomy-mid:#8d8369;--anatomy-lo:#5f5845;--anatomy-faint:#433d30;--anatomy-dot:#ece2c9;--anatomy-spec:#a8a08a}
.rb-svg .rb-score{fill:var(--anatomy-shade-0);stroke:none;opacity:.8}
.rb-svg .rb-rib{fill:#b9d1bd;stroke:#7fa08a;stroke-width:.25;stroke-linejoin:round}
.iso[data-theme="dark"] .rb-svg .rb-rib{fill:#2f4436;stroke:#4d6a57}
.rb-svg .rb-window{fill:#151819}
.rb-svg .rb-digit{fill:#eef2ef;font-family:var(--anatomy-mono);font-variant-numeric:tabular-nums;transition:fill .4s var(--anatomy-ease)}
.rb-svg .rb-digit.rb-same{fill:var(--rb-ok)}
.rb-svg .rb-eq{fill:#5f6a6c;stroke:none;transition:fill .4s var(--anatomy-ease)}
.rb-svg .rb-eq.rb-same{fill:var(--rb-ok)}
.rb-svg .rb-lens{fill:#2a2f30;stroke:none;transition:fill .3s var(--anatomy-ease)}
.rb-svg .rb-lens.rb-ok,.rb-svg .rb-lens.rb-run,.rb-svg .rb-lens.rb-paid{fill:var(--rb-ok)}
.rb-svg .rb-lens.rb-no{fill:var(--rb-fault)}
.rb-svg .rb-lens.rb-present{fill:#e9ebe8}
.rb-svg .rb-bezel{stroke:none;transition:fill .35s var(--anatomy-ease)}
.rb-svg .rb-bezel.rb-admit{fill:var(--rb-ok)}
.rb-svg .rb-bezel.rb-refuse{fill:var(--rb-fault)}
.rb-svg .rb-keyway,.rb-svg .rb-keyhole,.rb-svg .rb-bore{fill:#141718;stroke:none}
.rb-svg .rb-flag{fill:var(--rb-fault);stroke:#8f231b;stroke-width:.25;stroke-linejoin:round}
.rb-svg .rb-tape{fill:#f6f3ea;stroke:#a7aab0;stroke-width:.06}
.iso[data-theme="dark"] .rb-svg .rb-tape{fill:#c9c5b8;stroke:#55585c}
.rb-svg .rb-frame{fill:none;stroke:#c4c6c9;stroke-width:.08}
.rb-svg .rb-hole{fill:#2a2f30}
.rb-svg .rb-stamp-ok{fill:#7fae8b}
.rb-svg .rb-stamp-no{fill:var(--rb-fault)}
.rb-svg .rb-slot{fill:var(--anatomy-shade-0);stroke:none;opacity:.9}
.rb-svg .rb-glass{fill:#eef5f1;stroke:none;opacity:.4}
.rb-svg .rb-glass-back{fill:#dfe9e3;stroke:none;opacity:.5}
.rb-svg .rb-glass-shine{fill:none;stroke:#fff;stroke-width:1.2;opacity:.45;filter:blur(.6px)}
.iso[data-theme="dark"] .rb-svg .rb-glass{fill:#3c4642;opacity:.35}
.iso[data-theme="dark"] .rb-svg .rb-glass-back{fill:#25302b}
.rb-svg .rb-mouth{fill:#1a1512;stroke:none}
.rb-svg .rb-heat{fill:url(#rb-glow);stroke:none;transition:opacity .4s var(--anatomy-ease)}
.rb-svg .rb-pane{fill:#f4efe6;stroke:none;opacity:.14}
.rb-svg .rb-mouth-frame{fill:none;stroke:#2a2f30;stroke-width:.7}
.rb-svg .rb-strip{fill:#3a3f40;fill-opacity:.82;stroke:#1f2324;stroke-width:.2}
.rb-svg .rb-dial{fill:#f2f0ea;stroke:none}
.iso[data-theme="dark"] .rb-svg .rb-dial{fill:#c9c7c0}
.rb-svg .rb-glint{fill:#fff;stroke:none;opacity:.55}
.rb-svg .rb-hits path{fill:transparent;cursor:pointer}
.iso-stage{outline:none;touch-action:pan-y}
.iso-stage:focus-visible{box-shadow:0 0 0 1px var(--anatomy-mid)}
${SWING_CSS}
@media (max-width:560px){.iso-plate:has(.rb-svg){overflow:hidden}.rb-svg.iso-svg{width:114%;max-width:none;margin:0 -7%}}
`;
const GLOW_DEFS = `<defs><radialGradient id="rb-glow" cx=".5" cy=".7" r=".75"><stop offset="0" stop-color="#fff1d6"/><stop offset=".55" stop-color="#f1d3a2"/><stop offset="1" stop-color="#c79a62"/></radialGradient></defs>`;

const strip = (file) => readFileSync(join(HERE, file), "utf8").replace(/^export /gm, "");
const kitSource = strip("../kit/iso-kit.mjs");
const latheSource = `const LATHE = (() => {\n${strip("../kit/lathe.mjs").replace(/^import .*$/gm, "")}\nreturn { ${Object.keys(G).join(", ")} };\n})();`;
const modelSource = `const MD = (() => {\n${strip("model.mjs")}\nreturn { ${Object.keys(MD).join(", ")} };\n})();`;

const live = `
const P0 = ${JSON.stringify(P0)};
let P = P0;
${shipped({ C, GUIDE, GUIDE_SPLIT, READ_HALF, PITCH, TUBE_TOP, tubeSeat, CLAMPS, SPEED, LAG, STEPS, ROWS, FRAME, X3, Y3, Z3, READ_Z, READ_BACK, READ_FRONT, VAULT, PORT, GATE_POST, LOCK, DIAL_AT, CRATE, LOAF_PROFILE, MERIDIAN_INSET, WHO, CHUTE_LEN, LAND_ALIGN })}
const k = { ${Object.keys(k).join(", ")} };
const G = LATHE;
const LOOKS = new Map();
let looksFor = null;
${shipped({ at, S, L, D, M, n2, n3, faceY, rectD, box, cyl, FV, unit, span, planeOf, rod, smooth, halfway, litAngle, shine, edgeShine, glintAt, glint, ballGlint, brightRod, fadeFill, boxCast, grounded, shadow, halfRing, bandD, lipD, lensY, insideClip })}
${shipped({ seatAt, restState, base, face, LAMP_U, faceLamp, faceLamps, counter, packOf, tangentPoint, tapePath, frameAt, reel, tape, reelBase, guideShadow, guideSleeve, guideShaft, readerBack, readerFront, readerMoving, tubePost, tube, stand, basketFloor, basketTop, basketBody, vaultFrame, portD, loafAt, ovenDark, ovenClip, ovenFront, beltZ, beltSpans, belt, cleats, gateBack, gatePlate, gateFront, lockBox, lock, flag, ovenPlan, ovenCenter, ovenBody, mouthD, endFaces, chuteDir, BASKET_ANGLE, chuteFrame, chute, chutePost, basket, basketOpening, doughSvg, loafMeridian, loafSvg, placed, bakedShape, pieceSvg, axialReach, piecesIn, ovenPiece, wingParts, composition, hitAreas, partsOf })}
${swingSource}
${liveScript()}
`;

// The page: the tour runs the tape under three laws; the keys and the tape also answer clicks.
function liveScript() {
  return String.raw`
const root = document.querySelector('[data-figure="replay-bakery"]');
const stage = root.querySelector(".iso-stage");
const svg = stage.querySelector("svg");
const readout = root.querySelector("[data-readout]");
const still = matchMedia("(prefers-reduced-motion: reduce)");
const T = root.dataset;
const st = restState();
// The run under way: the private execution and its replay, computed once from the model.
let given = MD.run(MD.lawOf(1, 0), MD.S0, MD.W), replay = MD.replayOf(MD.lawOf(1, 0), MD.S0, MD.W);
let steps = [], step = null, stepTime = 0, touring = !still.matches, idle = 0, visible = false, frame = 0, last = 0, tourAt = 0;
const part = (name) => svg.querySelector('[data-part="' + name + '"]');
const capital = () => Boolean(MD.capitalCore(MD.lawOf(st.law.c, st.law.i), MD.S0, MD.W));
function say() {
  const done = st.counts[0] === MD.W.length && st.counts[1] === MD.W.length && !busy();
  const text = (capital() ? T.capital : T.none) + " · " + T.given + " " + st.counts[0] + "/" + MD.W.length + " · " + T.replay + " " + st.counts[1] + "/" + MD.W.length + (done ? " · " + T.same : "");
  if (readout.textContent !== text) readout.textContent = text;
  stage.setAttribute("aria-valuetext", text);
}
let shown = {};
const key = (v) => JSON.stringify(v, (k_, v_) => (typeof v_ === "number" ? Math.round(v_ * 100) / 100 : v_));
function paint(force = false) {
  const parts = partsOf(st);
  const want = { counter: key(st.counts), lamps: key(st.wings.map((wing) => MD.MEMBERS.map((who) => wing.bread[who] >= 1))), reels: key(st.q), tape: key([st.q, st.stamps, st.stampFade]), readers: key([st.lamps, st.dips]), "a-lock": key([st.bezel, st.keys]), "a-flag": key(st.flag) };
  for (const [i, tag] of [[0, "a"], [1, "b"]]) {
    const wing = st.wings[i];
    for (const span_ of ["far", "middle", "near"]) want[tag + "-cleats-" + span_] = key(st.travel);
    want[tag + "-hopper"] = key([wing.stock, wing.drop, wing.refill, wing.fall, piecesIn(wing, "fall").map((piece) => piece.c)]);
    want[tag + "-gate"] = key(wing.gate);
    for (const name of ["near", "between", "beyond"]) want[tag + "-" + name] = key(piecesIn(wing, name).map((piece) => [piece.c, piece.bake]));
    want[tag + "-dark"] = key(wing.heat);
    want[tag + "-inside"] = key(piecesIn(wing, "inside").map((piece) => [piece.c, piece.bake]));
    want[tag + "-oven"] = key([wing.heat, wing.flaps]);
    want[tag + "-chute"] = want[tag + "-chute-front"] = key(wing.chute);
    want[tag + "-chuted"] = key(piecesIn(wing, "chute").map((piece) => [piece.c, piece.dir]));
    for (const who of WHO) {
      want[tag + "-basket-" + who] = key(piecesIn(wing, "basket-" + who).map((piece) => [piece.c, piece.dir, piece.fade, piece.seated || piece.fly >= LAND_ALIGN]));
    }
  }
  for (const name of Object.keys(want)) if (force || want[name] !== shown[name]) { const el = part(name); if (el) el.innerHTML = parts[name](); }
  shown = want;
  say();
}

// --- pieces: where each ball of dough or loaf is, moved by the belt, the chute and gravity ----------------

const sideOf = (i) => (i === 0 ? -1 : 1);
// Release one ball from line i's tube for whose loaf it is.
function release(i, to) {
  const wing = st.wings[i], side = sideOf(i);
  wing.gateGoal = 1;
  wing.pieces.push({ to, at: "fall", bake: 0, c: tubeSeat(side, 0, wing.drop), v: 0 });
  wing.stock -= 1;
  wing.drop += 1;
  wing.fall = 0.001;
}
const G_ACC = 70, BELT_REST = beltZ + C.DOUGH;
const HANDOFF = C.BELT.x0 - C.PIVOT[0];
// Each loaf's seat in its basket: the first along the basket, the second beside it.
const seatOf = (i, to) => seatAt(sideOf(i), to, st.wings[i].bread[to] + st.wings[i].pieces.filter((piece) => piece.to === to && piece.at === "basket" && !piece.seated).length);
function movePieces(i, dt) {
  const wing = st.wings[i], side = sideOf(i);
  for (const piece of wing.pieces) {
    if (piece.at === "fall") {
      // Out of the escapement it drops through the collar onto the belt and settles with a small bounce.
      piece.v -= G_ACC * dt;
      piece.c[2] += piece.v * dt;
      if (piece.c[2] <= BELT_REST) {
        piece.c[2] = BELT_REST;
        if (piece.v < -6) piece.v = -piece.v * 0.18; else { piece.v = 0; piece.at = "belt"; }
      }
    } else if (piece.at === "belt") {
      piece.c[0] -= side * st.speed * dt;
      const u = Math.abs(piece.c[0]);
      // It bakes on its way through the oven: rising into a loaf over the first two thirds of the tunnel.
      piece.bake = smooth((C.OVEN.x1 - 1 - u) / ((C.OVEN.x1 - C.OVEN.x0) * 0.66));
      piece.c[2] = beltZ + C.DOUGH + (C.LOAF - C.DOUGH) * piece.bake;
      piece.dir = X3;
      if (u <= C.BELT.x0) {
        piece.c[0] = side * C.BELT.x0;
        piece.at = "chute";
        piece.s = -HANDOFF;
        piece.v = Math.max(st.speed, 6);
      }
    } else if (piece.at === "chute") {
      // Off the roller onto the chute, then sliding down it.
      piece.v = Math.min(piece.v + 16 * dt, 20);
      piece.s = Math.min(CHUTE_LEN, piece.s + piece.v * dt);
      const F = chuteFrame(side, wing.chute);
      const onFloor = G.add3(F.o, G.mul3(F.v, C.LOAF));
      const along = G.mul3(F.a, -side);
      if (piece.s < 0) {
        const t = 1 + piece.s / HANDOFF;
        const start = [side * C.BELT.x0, 0, beltZ + C.LOAF];
        piece.c = G.lerp3(start, onFloor, t);
        piece.c[2] = start[2] + (onFloor[2] - start[2]) * t * t;
        piece.dir = unit(G.lerp3(X3, along, smooth(t)));
      } else {
        piece.c = G.add3(onFloor, G.mul3(F.a, piece.s));
        piece.dir = along;
      }
      if (piece.s === CHUTE_LEN) {
        piece.seat = seatOf(i, piece.to);
        piece.at = "basket";
        piece.from = [...piece.c];
        piece.fly = 0;
        piece.dir0 = piece.dir;
        const occupied = wing.pieces.some((other) => other !== piece && other.at === "basket" && other.to === piece.to);
        const obstacle = occupied ? piece.seat[2] + C.LOAF : basketTop(piece.to);
        piece.landZ = Math.max(piece.from[2], obstacle + C.LOAF + 0.12);
      }
    } else if (piece.at === "basket" && !piece.seated) {
      // Align over the opening while clear of the rim and any loaf already there, then drop into the seat.
      piece.fly = Math.min(1, piece.fly + dt / 0.48);
      const align = Math.min(1, piece.fly / LAND_ALIGN);
      const end = piece.to === "丙" ? Y3 : X3;
      const dir = G.dot3(piece.dir0, end) < 0 ? G.mul3(end, -1) : end;
      piece.dir = unit(G.lerp3(piece.dir0, dir, smooth(align)));
      piece.c = G.lerp3(piece.from, piece.seat, align * (2 - align));
      const drop = Math.max(0, (piece.fly - LAND_ALIGN) / (1 - LAND_ALIGN));
      piece.c[2] = piece.from[2] + (piece.landZ - piece.from[2]) * align * (2 - align) + (piece.seat[2] - piece.landZ) * drop * drop;
      if (piece.fly === 1) { piece.seated = true; wing.bread[piece.to] += 1; }
    }
  }
}
// Whether anything is still on its way: the belts run while it is.
const busy = () => st.wings.some((wing) => wing.pieces.some((piece) => piece.at !== "basket" || !piece.seated));

// --- the run: the tape steps one frame at a time; the private reader reads frame n − 1 and stamps it, the
// public reader reads the stamped frame LAG frames behind it --------------------------------------------------

const DURATION = { step: 1.4, wind: 1.8, finish: 0, clear: 2, set: 0.9 };
function begin(next) {
  step = next;
  stepTime = 0;
  if (step.kind === "step") {
    step.from = st.q;
    step.a = st.q < MD.W.length ? st.q : -1; // the frame reaching the private reader
    step.b = st.q + 1 - LAG - 1 >= 0 && st.q + 1 - LAG - 1 < MD.W.length ? st.q + 1 - LAG - 1 : -1;
    step.did = {};
  } else if (step.kind === "wind") {
    step.from = st.q;
  } else if (step.kind === "clear") {
    step.from = st.q;
    st.keys = { c: 0, i: 0 };
    st.dips = [0, 0];
    st.lamps = [null, null];
    for (const wing of st.wings) for (const piece of wing.pieces) piece.lift0 = piece.c[2];
  } else if (step.kind === "set") {
    step.law = { c: step.c, i: step.i };
  }
}
function complete(next) {
  if (next.kind === "wind") st.q = LAG;
  else if (next.kind === "step") {
    st.q = next.from + 1;
    if (next.a >= 0) st.counts[0] = next.a + 1;
    if (next.b >= 0) st.counts[1] = next.b + 1;
  } else if (next.kind === "clear") {
    st.q = 0;
    st.stamps = MD.W.map(() => null);
    st.stampFade = 1;
    st.counts = [0, 0];
    st.lamps = [null, null];
    for (const wing of st.wings) { wing.pieces = []; wing.bread = { 甲: 0, 乙: 0, 丙: 0 }; }
  } else if (next.kind === "set") {
    st.law = next.law;
    st.bezel = { ...next.law };
    given = MD.run(MD.lawOf(st.law.c, st.law.i), MD.S0, MD.W);
    replay = MD.replayOf(MD.lawOf(st.law.c, st.law.i), MD.S0, MD.W);
  }
}
function advance(dt) {
  if (!step) {
    if (steps.length) begin(steps.shift());
    else if (touring) { for (const next of tourStep()) steps.push(next); begin(steps.shift()); }
    else return false;
  }
  stepTime += dt;
  if (step.kind === "finish") {
    if (busy()) return true;
    complete(step); step = null; return true;
  }
  const d = DURATION[step.kind] ?? step.t ?? 0;
  const t = d ? Math.min(1, stepTime / d) : 1;
  if (step.kind === "step") {
    // The tape moves one frame, then both readers dip.
    st.q = step.from + smooth(t / 0.28);
    const dip = t > 0.3 && t < 0.62 ? Math.sin(((t - 0.3) / 0.32) * Math.PI) : 0;
    st.dips = [step.a >= 0 ? dip : 0, step.b >= 0 ? dip : 0];
    if (step.a >= 0) privateRead(step, t);
    if (step.b >= 0) publicRead(step, t);
  } else if (step.kind === "wind") {
    st.q = step.from + (LAG - step.from) * smooth(t);
  } else if (step.kind === "clear") {
    // Whoever the loaves are for takes them; the tape winds back and the stamps are worn off at the reader;
    // the tubes are filled again from their bins.
    const u = smooth(t);
    st.q = step.from * (1 - u);
    st.stampFade = 1 - smooth(t / 0.6);
    for (const wing of st.wings) for (const piece of wing.pieces) {
      piece.fade = 1 - smooth(t / 0.5);
      if (piece.seated) piece.c[2] = piece.lift0 + 3 * smooth(t / 0.5);
    }
    if (!step.refilled && t > 0.35) {
      step.refilled = true;
      for (const wing of st.wings) {
        const n = MD.S0.dough - wing.stock;
        // Each ball drops from the bin into the tube, the next a little after it.
        wing.refill = Array.from({ length: n }, (_, j) => [wing.stock + j, TUBE_TOP + 1.5 - tubeSeat(1, wing.stock + j)[2] + j * 2.6]);
        wing.rv = wing.refill.map(() => 0);
        wing.stock = MD.S0.dough;
      }
    }
  } else if (step.kind === "set") {
    // A key's bezel changes and the flag follows.
    if (t > 0.3 && !step.shown) { step.shown = true; st.bezel = { ...step.law }; st.law = step.law; }
  }
  if (t >= 1) {
    if (step.kind === "step") st.dips = [0, 0];
    complete(step);
    step = null;
  }
  return true;
}
// The private reader: the signer's key tries the lock; a turn opens the gate and lets one ball go; a
// refusal shakes the key. Either way the frame is stamped with what happened.
function privateRead(s, t) {
  const item = given.items[s.a];
  const who = item.by === MD.CONTROLLER ? "c" : "i";
  if (t > 0.34 && !s.did.a) {
    s.did.a = true;
    st.stamps = st.stamps.map((v, j) => (j === s.a ? (item.done ? "ok" : "no") : v));
    st.lamps = [item.done ? "ok" : "no", st.lamps[1]];
    s.keyWho = who;
  }
  if (t > 0.3) {
    const u = Math.min(1, (t - 0.3) / 0.7);
    st.keys = { c: 0, i: 0 };
    st.keys[who] = item.done ? (Math.PI / 2) * smooth(u / 0.25) * (1 - smooth((u - 0.75) / 0.25)) : 0.28 * Math.sin(u * Math.PI * 6) * (1 - u) * (u < 0.6 ? 1 : 0);
  }
  if (item.done) openFor(0, s, "a", t, item.to);
}
// The public reader reads the stamp: a done entry runs again with no key; a refused one is presented with
// no effect, and only the lamp shows it.
function publicRead(s, t) {
  const entry = replay[s.b];
  if (t > 0.34 && !s.did.b) { s.did.b = true; st.lamps = [st.lamps[0], entry.op === "bake" ? "run" : "present"]; }
  if (entry.op === "bake") openFor(1, s, "b", t, entry.to);
}
function openFor(i, s, tag, t, to) {
  if (t > 0.52 && !s.did[tag + "release"]) { s.did[tag + "release"] = true; release(i, to); }
}
const TOUR_LAWS = [[1, 0], [1, 1], [0, 0]];
// The private reader reads every frame; then the transport winds the stamped frames across to the public
// reader, which reads them again.
function runList() {
  const reads = () => Array.from({ length: MD.W.length }, () => ({ kind: "step" }));
  return [...reads(), { kind: "wind" }, ...reads(), { kind: "finish" }, { kind: "hold", t: 2.4 }];
}
function tourStep() {
  const [c, i] = TOUR_LAWS[tourAt];
  tourAt = (tourAt + 1) % TOUR_LAWS.length;
  goal = { c, i };
  const list = [];
  if (st.q > 0 || st.wings.some((wing) => wing.pieces.length)) list.push({ kind: "clear" });
  if (st.law.c !== c || st.law.i !== i) list.push({ kind: "set", c, i });
  return [...list, ...runList()];
}

// --- the continuous mechanics: the belts, the gates, the tubes, the chutes, the flag and the curtains --------

function mechanics(dt) {
  if (!dt) return false;
  let moving = false;
  // The shared drive runs while anything is on a belt.
  const onBelt = st.wings.some((wing) => wing.pieces.some((piece) => piece.at === "belt"));
  const goal = onBelt ? SPEED : 0;
  st.speed += (goal - st.speed) * (1 - Math.exp(-dt / 0.18));
  if (goal === 0 && st.speed < 0.05) st.speed = 0;
  st.travel += st.speed * dt;
  if (st.speed) moving = true;
  for (const [i, wing] of st.wings.entries()) {
    movePieces(i, dt);
    // The gate drops again once the piece it let through has passed under it.
    if (wing.gateGoal === 1 && !wing.pieces.some((piece) => piece.at === "fall" || (piece.at === "belt" && Math.abs(piece.c[0]) > C.GATE - C.DOUGH - 0.8))) wing.gateGoal = 0;
    const g = wing.gateGoal ?? 0;
    wing.gate += (g - wing.gate) * (1 - Math.exp(-dt / 0.09));
    if (Math.abs(g - wing.gate) < 0.002) wing.gate = g; else moving = true;
    // The stack drops a pitch under gravity after a ball has gone; refilled balls fall onto it from the bin.
    if (wing.drop > 0) {
      wing.dv -= G_ACC * dt;
      wing.drop = Math.max(0, wing.drop + (wing.dv / PITCH) * dt);
      if (wing.drop === 0) wing.dv = 0;
      moving = true;
    }
    if (wing.refill.length) {
      // They fall under gravity until each lands on the ball below it.
      wing.refill = wing.refill.map(([slot, lift], j) => { wing.rv[j] -= G_ACC * dt; return [slot, Math.max(0, lift + wing.rv[j] * dt)]; });
      if (wing.refill.every(([, lift]) => lift === 0)) wing.refill = [];
      moving = true;
    }
    wing.fall = wing.pieces.some((piece) => piece.at === "fall") ? Math.min(1, wing.fall + dt * 2.5) : 0;
    // The chute swings to the next loaf's basket.
    // The next loaf to arrive is the one furthest in along the belt (the lines run toward the middle).
    const next = wing.pieces.filter((piece) => piece.at === "belt" || piece.at === "fall").sort((a, b) => Math.abs(a.c[0]) - Math.abs(b.c[0]))[0];
    const delivering = wing.pieces.find((piece) => piece.at === "chute" || (piece.at === "basket" && !piece.seated && piece.fly < LAND_ALIGN));
    const target = delivering ?? next;
    const aim = target ? BASKET_ANGLE(target.to) : wing.chute;
    wing.cv = (wing.cv ?? 0) + ((aim - wing.chute) * 60 - (wing.cv ?? 0) * 11) * dt;
    wing.chute += wing.cv * dt;
    if (Math.abs(aim - wing.chute) < 0.002 && Math.abs(wing.cv) < 0.01) { wing.chute = aim; wing.cv = 0; } else moving = true;
    // The fire burns while a piece is inside; each curtain swings as a piece pushes through it.
    const inside = piecesIn(wing, "inside").length > 0;
    wing.heat += ((inside ? 1 : 0) - wing.heat) * (1 - Math.exp(-dt / (inside ? 0.3 : 1.2)));
    if (wing.heat > 0.003 && !inside) moving = true; else if (!inside) wing.heat = 0;
    wing.flaps = [C.OVEN.x0, C.OVEN.x1].map((edge) => {
      return wing.pieces.reduce((open, piece) => {
        if (piece.at !== "belt" && piece.at !== "chute") return open;
        const d = Math.abs(piece.c[0]) - edge, reach = axialReach(piece);
        const length = C.MOUTH.hinge - C.MOUTH.hem;
        const entry = smooth((reach + 2.1 - d) / 1.8);
        const exit = smooth((d + length + reach + 2.1) / 1.8);
        return Math.max(open, 1.52 * entry * exit);
      }, 0);
    });
    if (wing.pieces.some((piece) => piece.at !== "basket" || !piece.seated)) moving = true;
  }
  // The flag: up exactly when the private law has a capital core.
  const up = capital() ? 1 : 0;
  st.fv += ((up - st.flag) * 70 - st.fv * 9) * dt;
  st.flag = Math.max(0, Math.min(1.08, st.flag + st.fv * dt));
  if (Math.abs(up - st.flag) < 0.002 && Math.abs(st.fv) < 0.01) { st.flag = up; st.fv = 0; } else moving = true;
  return moving;
}
function tick(time) {
  const dt = last ? Math.min((time - last) / 1000, 1 / 30) : 1 / 60;
  last = time;
  const working = advance(dt);
  const moving = mechanics(dt);
  paint();
  frame = visible && (working || moving || touring) ? requestAnimationFrame(tick) : 0;
}
const run = () => { if (!frame && visible) { last = 0; frame = requestAnimationFrame(tick); } };
const hold = () => { touring = false; clearTimeout(idle); idle = setTimeout(() => { touring = !still.matches; run(); }, 9000); };
// Under reduced motion every step lands at once: the run's final state, drawn still.
function settleNow() {
  for (let n = 0; n < 4000 && (step || steps.length || busy()); n++) { advance(0.05); mechanics(0.05); }
  st.flag = capital() ? 1 : 0;
  st.keys = { c: 0, i: 0 };
  st.dips = [0, 0];
  for (const wing of st.wings) { wing.gate = 0; wing.gateGoal = 0; wing.heat = 0; wing.flaps = [0, 0]; wing.drop = 0; wing.dv = 0; wing.refill = []; wing.fall = 0; }
  paint(true);
}
function now(list) {
  steps = still.matches ? list.filter((next) => next.kind !== "hold") : list.map((next) => (next.kind === "hold" ? { ...next, t: 6 } : next));
  if (step && step.kind !== "step" && step.kind !== "clear") step = null;
  if (!still.matches) { run(); return; }
  settleNow();
}
// The law the queued steps will set: a second click before the first has landed toggles from it.
let goal = { ...st.law };
function restart(c, i) {
  goal = { c, i };
  return [{ kind: "clear" }, { kind: "set", c, i }, ...runList()];
}
const CELLS = [[1, 0], [1, 1], [0, 0], [0, 1]];
const ACTION = { c: () => restart(1 - goal.c, goal.i), i: () => restart(goal.c, 1 - goal.i), tape: () => restart(goal.c, goal.i) };
stage.addEventListener("click", (event) => {
  const hit = event.target.closest("[data-hit]");
  if (!hit) return;
  hold();
  step = null;
  now(ACTION[hit.dataset.hit]());
});
stage.addEventListener("keydown", (event) => {
  let at = CELLS.findIndex(([c, i]) => c === goal.c && i === goal.i);
  if (event.key === "ArrowRight") at = (at + 1) % CELLS.length;
  else if (event.key === "ArrowLeft") at = (at + CELLS.length - 1) % CELLS.length;
  else if (event.key !== " " && event.key !== "Enter") return;
  event.preventDefault();
  hold();
  step = null;
  now(restart(...CELLS[at]));
});
new IntersectionObserver((entries) => { visible = entries[entries.length - 1].isIntersecting; if (visible) run(); }, { rootMargin: "120px 0px" }).observe(stage);
// The figure opens on a finished run and lets it be read before the tour winds the tape back.
if (still.matches) touring = false; else steps.push({ kind: "hold", t: 3.5 });
paint(true);
mountSwing(stage, { onHold: hold, limit: 18, onSwing: (angle) => { P = swingOf(iso, P0, FRAME, angle); svg.innerHTML = GLOW + composition(st); shown = {}; paint(true); } });
`;
}

const COPY = {
  en: {
    title: "The lock is the only difference",
    hint: "Click a key · click the tape · drag to look round",
    keys: ["Red flag: a capital core, raised exactly when the controller is admitted and the affected are refused", "Tape: one execution; the right line replays it entry by entry, a refused entry with no effect", "Green lamp: that member's maintenance is paid"],
    refs: ["Theorem 2", "Theorem 3", "Theorem 8"],
    caption: [
      "The oven is the production port and 丙 controls it. Under the left line's law L, 丙's key turns and the affected's key is refused: 甲 tries to bake her own loaf and is stopped, her bread comes out only through 丙's port, and 丙 keeps two loaves of his own. Need, return and disposal are all there, and the flag is up.",
      "Of the four settings of the two keys, only one raises the flag: the controller admitted and the affected refused. Admit the affected, or close both keys, and the permissions are no longer asymmetric. With both closed, though, no one bakes and the baskets stay empty: removing the asymmetry is not the same as delivering bread.",
      "The right line is the public interpretation, its lock taken off and only the screw holes left. The tape is stamped at the left gate with what actually happened, then wound across and replayed entry by entry at the right one. A refused entry becomes a presentation with no effect, and bakes no extra loaf. So the run has the same length and the same complete post-state: the two rows of baskets side by side in the middle hold the same loaves, the same dough is left over, maintenance is paid on one side exactly when on the other, and the right line has no capital core.",
    ],
    aria: "Replay bakery: click the left lock's upper key for the controller's access, its lower key for the affected's, the tape to run the orders again; arrow keys step through the four settings",
    capital: "C holds", none: "no C", given: "given", replay: "replay", same: "same post-state",
  },
  zh: {
    title: "差别只在那把锁",
    hint: "点击钥匙 · 点击纸带重跑 · 拖动侧看",
    keys: ["红旗：资本核心，恰在控制者获准、受影响者被拒时升起", "纸带：同一执行；右翼逐项重放，被拒的一格只呈示、不作用", "绿灯：该成员的生活维护已付"],
    refs: ["定理 2", "定理 3", "定理 8"],
    caption: [
      "烤炉是生产端口，丙是它的控制者。左翼的法则 L 下，丙的钥匙能转，受影响者的钥匙被拒：甲想自己烤一块被挡下，她的面包只能经丙的端口发出，丙还留下自己的两块。需要、回流与处分齐备，红旗升起。",
      "两把钥匙的四种设置里，只有「控制者获准、受影响者被拒」这一格升旗。放行受影响者，或者两把都关上，权限都不再不对称，旗随之落下；可两把都关上时谁也烤不成，篮子是空的：撤去不对称，不等于交付面包。",
      "右翼是公共解释：锁已拆下，只剩螺孔。纸带先在左闸盖上实际结果，再绕到右闸逐项重放；左翼被拒的一格，在右翼成为零作用的呈示，不会多烤一块。于是长度相同、完整后态相同：正中并排的两排篮子装着一样的面包，剩下的面团一样多，生活维护两边同时付清或同时欠付，右翼没有资本核心。",
    ],
    aria: "重放烤坊：点击左闸锁上方的钥匙切换控制者准入，下方的钥匙切换受影响者准入，点击纸带重跑；方向键切换四种设置",
    capital: "C 成立", none: "无 C", given: "原执行", replay: "重放", same: "后态相同",
  },
};
const bodyOf = (lang) => {
  const copy = COPY[lang];
  const data = ["capital", "none", "given", "replay", "same"].map((key) => `data-${key}="${copy[key]}"`).join(" ");
  return `<div data-figure="replay-bakery" ${data}>${k.plateHtml({
    fig: "Fig 6.1",
    title: copy.title,
    hint: copy.hint,
    readout: `${copy.capital} · ${copy.given} 6/6 · ${copy.replay} 6/6 · ${copy.same}`,
    keys: [
      { mark: "red", label: copy.keys[0] },
      { mark: "lit", label: copy.keys[1] },
      { mark: "raised", label: copy.keys[2] },
    ],
    caption: copy.caption,
    refs: copy.refs,
    body: `<div class="iso-stage" tabindex="0" role="application" aria-label="${copy.aria}">${svg.replace(/(<svg[^>]*>)/, `$1${GLOW_DEFS}`)}</div>`,
  })}</div>`;
};

const script = `{\nconst GLOW = ${JSON.stringify(GLOW_DEFS)};\n${kitSource}\n${latheSource}\n${modelSource}\n${live}\n}`.replace(/<\/(script)/gi, "<\\/$1");
if (fragment) {
  const outDir = join(HERE, "../../src/generated");
  mkdirSync(outDir, { recursive: true });
  writeFileSync(join(outDir, "replay-bakery.json"), JSON.stringify({ html: { zh: bodyOf("zh"), en: bodyOf("en") }, css: CSS, script }));
  console.log("wrote src/generated/replay-bakery.json");
} else {
  mkdirSync(join(HERE, "out"), { recursive: true });
  const name = theme === "light" ? "replay-bakery-light.html" : "replay-bakery.html";
  writeFileSync(join(HERE, "out", name), k.pageHtml({ title: "The lock is the only difference", theme, body: `<style>${CSS}</style>${bodyOf(process.argv.includes("--zh") ? "zh" : "en")}`, script, width: 760 }));
  console.log("wrote out/" + name);
}
