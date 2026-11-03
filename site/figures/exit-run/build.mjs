// Fig: an exit instrument. A jade bead, 甲, leaves its cage and runs down a precision track past three
// links: a coin whose hook lifts the gate (the payment's association), a hinged rail bridge (the path)
// and a latch held by 乙's weight (capture). It passes the life station's two services and joins the row
// of receipts (Theorem 5.1, Propositions 5.2–5.3 and Theorem 1.3 of "The Canonical Society Theorem").
//   bun build.mjs [--light]   → out/exit-run[-light].html (standalone, for checks)
//   bun build.mjs --fragment  → ../../src/generated/exit-run.json (for the site)
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

// World: x along the track from the cage (−x) to the life station (+x), y toward the viewer, z up; the
// deck's top is z = 0. The track is one straight incline in the plane y = 0.
const C = {
  BASE: { x: -112, y: -26, w: 226, d: 56, r: 4 },
  BASE_Z: [-20, 0],
  FOOT: { r: 5.5, h: 4, inset: 14 },
  FACE: 30,
  TRACK: { x0: -80, x1: 64, z0: 60, z1: 24, gauge: 1.8, rail: 0.5 },
  BEAD: 2.1,
  POSTS: [-58, -34, -14, 14, 42],
  TIES: 8,
  CAGE: { x0: -86, x1: -73, cheek: 4.4 },
  HOPPER: { x: -79.5, z0: 73, z1: 106, r: 2.9 },
  LEVER: [-76, 5.6, 71], // the gate lever's pivot, on the cage cap's front edge
  COIN: [-80, 13, 52], // the coin's dish, on a bracket from the cage's front cheek
  BRIDGE: { x0: -34, x1: -14, lift: 56 }, // hinged at x1
  LATCH: 18,
  WEIGHT: [18, 11], // 乙's lever post, in front of the latch
  STATION: { x: 60, y: -10, w: 26, d: 20, r: 1.2, h: 20 },
  ROW: { x0: -62, x1: 84, y: 24, z: 1.4 }, // the receipts channel along the deck's front
  STOP: { link: -77, path: -36.5, capture: 15.4 },
  // The front panel: the capacity window, the domain lamps, a lamp and a repair lever per failure kind.
  PANEL: { k: [-104, -86], domains: [-74, -63], kinds: [-46, -32, -18], plate: [58, 104] },
};
const SLOPE = (C.TRACK.z1 - C.TRACK.z0) / (C.TRACK.x1 - C.TRACK.x0);
const railZ = (x) => C.TRACK.z0 + SLOPE * (x - C.TRACK.x0);
// The bead rests on both rails: its centre stands above the rail axis by √((R + r)² − g²).
const LIFT = Math.sqrt((C.BEAD + C.TRACK.rail) ** 2 - C.TRACK.gauge ** 2);

const FIT = [
  ...k.boxCorners(C.BASE, C.BASE_Z[0] - C.FOOT.h, 0),
  [C.HOPPER.x, 0, C.HOPPER.z1 + 4],
  [C.TRACK.x0, 0, C.TRACK.z0 + 10],
];
const VIEW = { pad: 22, azimuth: 66, elevation: 24 };
const P0 = k.fitProjection(FIT, WIDTH, HEIGHT, VIEW);
const FRAME = { points: FIT, width: WIDTH, height: HEIGHT, pad: VIEW.pad };
let P = P0;

// --- shared with the page --------------------------------------------------------------------

const X3 = [1, 0, 0], Y3 = [0, 1, 0], Z3 = [0, 0, 1];
const at = (point) => k.iso(point, P);
const S = (paths, style) => k.solidSvg(paths, style);
const L = (d, style) => k.lineSvg(d, style);
const D = (points, style) => k.dotsSvg(points, style);
// Stone (kit iso.css, data-mat): a group remaps the tone ramp of what it holds.
const M = (material, ...svg) => `<g data-mat="${material}">${svg.join("")}</g>`;
const n2 = (v) => (Math.round(v * 100) / 100).toString();
const faceY = (y) => k.sideMatrix([0, y], 0, P, "left");
const rectD = (u0, v0, u1, v1, r = 0) => k.pathOf(k.roundedPlan({ x: u0, y: v0, w: u1 - u0, d: v1 - v0, r }, 4), true);
const box = (plan, z, h, style, steps = 3, bevel = 0) => S(k.slabOf(plan, z, h, P, steps, bevel), style);
const cyl = (x, y, r, z, h, style, steps = 20, bevel = 0) => S(k.cylinder(x, y, r, z, h, P, steps, bevel), style);
const unit = (v) => { const n = Math.hypot(...v) || 1; return v.map((c) => c / n); };
const DIR = unit([1, 0, SLOPE]);
const UP = unit([-SLOPE, 0, 1]);
// A rod between two points: the kit's turned body along its axis.
const rod = (a, b, r, style, steps) => {
  const d = [b[0] - a[0], b[1] - a[1], b[2] - a[2]];
  const length = Math.hypot(...d);
  return length < 0.05 ? "" : S(G.disc(0, length, r, G.frameAlong(a, d), P, steps ? { steps } : {}), style);
};

// The visible front half of a thin band round an upright tube, from z0 to z1: no caps, so the tube shows through.
const bandD = (x, y, r, z0, z1) => {
  const [vx, vy] = G.viewOf(P);
  const f = Math.atan2(vy, vx);
  const arc = (z, back) => Array.from({ length: 25 }, (_, i) => { const t = f - Math.PI / 2 + ((back ? 24 - i : i) / 24) * Math.PI; return at([x + r * Math.cos(t), y + r * Math.sin(t), z]); });
  return k.pathOf([...arc(z0, false), ...arc(z1, true)], true);
};

// --- the base and its panel -------------------------------------------------------------------

function base() {
  const { BASE, BASE_Z, FOOT } = C;
  const out = [`<path class="iso-halo" d="${k.haloOf(BASE, BASE_Z[0] - FOOT.h, BASE_Z[1] - BASE_Z[0], P)}"/>`];
  const feet = k.corners(BASE, FOOT.inset).sort((a, b) => k.depthOf([...a, 0], P) - k.depthOf([...b, 0], P));
  for (const [x, y] of feet) out.push(cyl(x, y, FOOT.r, BASE_Z[0] - FOOT.h, FOOT.h, { tone: "mid" }, 28, 0.4));
  out.push(box(BASE, BASE_Z[0], -BASE_Z[0] - 3, { tone: "hi", inner: L(k.sideSeam(BASE, BASE_Z[0] + 3, P, 6), { tone: "faint" }) }, 6, 1));
  const deck = k.insetPlan(BASE, 1.5);
  return M("ink", ...out) + M("marble", box(deck, -3, 3, { tone: "mid" }, 6, 0.8),
    L(k.planOutline(k.insetPlan(deck, 3.5), 0, P), { tone: "faint" }),
    D(k.corners(deck, 6).map(([x, y]) => at([x, y, 0])), { size: 0.5 }),
    L(k.corners(deck, 6).map(([x, y]) => k.ring(x, y, 1.6, 0, P, 14)).join(""), { tone: "faint" })) + panel();
}
const KINDS = ["link", "path", "capture"];
const REPAIR_OF = { link: "relink", path: "restorePath", capture: "uncapture" };
const DOMAINS_ICON = ["tenure", "health"];
function glyphD(kind) {
  if (kind === "link") return "M-3 0a1.6 1.1 0 1 0 3.2 0a1.6 1.1 0 1 0 -3.2 0M-0.2 0a1.6 1.1 0 1 0 3.2 0a1.6 1.1 0 1 0 -3.2 0";
  if (kind === "path") return "M-3.4 1Q0 -2.2 3.4 1M-3.4 -0.6H3.4";
  if (kind === "capture") return "M-2.6 1.4V-1.6M-2.6 -1H3.2";
  if (kind === "tenure") return "M-2.4 1.4V-0.4L0 -2.2L2.4 -0.4V1.4Z";
  return "M-0.7 -2H0.7V-0.7H2V0.7H0.7V2H-0.7V0.7H-2V-0.7H-0.7Z";
}
const icon = (kind, u, v) => `<g transform="translate(${u} ${v}) scale(1.15)">${L(glyphD(kind), { tone: "faint" })}</g>`;
// A lamp on the face: a bezel and its lens; `glow` is the lens's CSS class.
function faceLamp(x, z, glow) {
  const F = G.frameOf([x, C.FACE, z], Y3, X3, Z3);
  return M("ink", S(G.disc(0, 0.7, 2.4, F, P), { tone: "mid", inner: L(G.circleOf(F, 0.7, 2.05, P, 28), { tone: "faint" }) })) + `<path class="${glow}" d="${G.circleOf(F, 0.72, 1.7, P, 22)}"/>` + `<path class="er-glint" d="${G.circleOf(G.frameOf(G.pointOf(F, 0.73, 0.75, 2.3), Y3, X3, Z3), 0, 0.42, P, 10)}"/>`;
}
// The source selector: a knurled knob whose pointer stands at the loaded source, over five engraved stops.
const SELECTOR = { x: 4, z: -10.6, r: 3.1, stops: [-64, -32, 0, 32, 64] };
function selectorFace() {
  const { x, z, stops } = SELECTOR;
  const rad = (d) => (d * Math.PI) / 180;
  const pt = (d, r) => `${n2(x + r * Math.sin(rad(d)))} ${n2(-z - r * Math.cos(rad(d)))}`;
  const arc = `M${pt(stops[0], 4.6)}A4.6 4.6 0 0 1 ${pt(stops[stops.length - 1], 4.6)}`;
  const ticks = stops.map((d, i) => `M${pt(d, 4.6)}L${pt(d, i === 0 ? 6.6 : 5.8)}`).join("");
  return `<g transform="${faceY(C.FACE + 0.02)}">${L(arc + ticks, { tone: "faint" })}${L(rectD(x - 8.4, 3.4, x + 8.4, 17.4, 1.4), { tone: "faint" })}</g>`;
}
function selector(scene) {
  const { x, z, r, stops } = SELECTOR;
  const F = G.frameOf([x, C.FACE, z], Y3, X3, Z3);
  const ribs = G.ribsOf(F, 0.15, 1.85, r, 36, P, { fade: [0.1, 0.6] });
  const d = (stops[["whole", "link", "path", "capture", "single"].indexOf(scene)] * Math.PI) / 180;
  const tip = [x + (r - 0.7) * Math.sin(d), C.FACE + 2, z + (r - 0.7) * Math.cos(d)];
  return M("ink", S(G.disc(0, 0.6, r + 0.9, F, P), { tone: "mid" }), S(G.disc(0.6, 2, r, F, P, { steps: 40 }), { tone: "mid", inner: k.fadedSvg(ribs, { tone: "lo" }) }))
    + L(k.pathOf([at([x, C.FACE + 2, z]), at(tip)]), { tone: "hi" }) + D([at([x, C.FACE + 2, z])], { size: 0.5, tone: "hi" }) + M("jade", S(G.sphereOf(tip, 0.6, P), { tone: "hi", lit: true }));
}
// A repair lever: rest (0) points up and out, pulled (1) down and out.
function lever(x, pull) {
  const z = -16;
  const a = ((35 - 70 * pull) * Math.PI) / 180;
  const base = [x, C.FACE, z];
  const tip = [x, C.FACE + 7 * Math.cos(a), z + 7 * Math.sin(a)];
  const F = G.frameOf(base, Y3, X3, Z3);
  return M("ink", S(G.disc(0, 1, 2.1, F, P), { tone: "mid", inner: L(G.circleOf(F, 1, 1.45, P, 24), { tone: "faint" }) }), rod([x, C.FACE + 0.6, z], tip, 0.55, { tone: "mid" })) + M("jade", S(G.sphereOf(tip, 1.55, P), { tone: "mid" }));
}
function panel() {
  const { PANEL } = C;
  const [k0, k1] = PANEL.k;
  const [p0, p1] = PANEL.plate;
  const face = [`<g transform="${faceY(C.FACE + 0.02)}">`,
    `<path class="er-window" d="${rectD(k0, 5, k1, 16, 1.2)}"/>`, L(rectD(k0, 5, k1, 16, 1.2), { tone: "faint" }),
    L(rectD(PANEL.domains[0] - 6, 3.6, PANEL.domains[1] + 6, 17, 1.4) + rectD(PANEL.kinds[0] - 7.5, 3, PANEL.kinds[2] + 7.5, 19, 1.4), { tone: "faint" }),
    ...PANEL.domains.map((u, i) => icon(DOMAINS_ICON[i], u, 6.6)),
    ...KINDS.map((kind, i) => icon(kind, PANEL.kinds[i], 5.6)),
    L(rectD(p0, 5, p1, 15, 1.2), { tone: "faint" }), L(`M${p0 + 6} 8H${p1 - 12}M${p0 + 6} 10H${p1 - 18}M${p0 + 6} 12H${p1 - 24}`, { tone: "faint", free: true }),
    // The capacity window's bezel, and the vent slots over the drive.
    L(rectD(k0 - 1.4, 3.6, k1 + 1.4, 17.4, 1.8) + rectD(20.2, 4, 51.2, 16, 1.2), { tone: "faint" }),
    ...Array.from({ length: 7 }, (_, i) => L(rectD(24 + i * 3.4, 6, 25.4 + i * 3.4, 14, 0.7), { tone: "faint" })),
    `</g>`];
  const screws = [[p0 + 2.4, -7], [p1 - 2.4, -7], [p0 + 2.4, -13], [p1 - 2.4, -13], [k0 - 0.4, -4.6], [k1 + 0.4, -4.6], [k0 - 0.4, -16.4], [k1 + 0.4, -16.4], [21.6, -7], [21.6, -13], [49.8, -7], [49.8, -13]];
  const out = [M("ink", face.join(""), selectorFace(), D(screws.map(([u, z]) => at([u, C.FACE, z])), { size: 0.45 }))];
  out.push(k.faceTextSvg(`${faceY(C.FACE + 0.02)} translate(${k0 - 2.6} 14)`, "K", { size: 5, tone: "faint", anchor: "end" }));
  return out.join("");
}
// The panel's moving parts: the capacity digit, the domain and source lamps, the levers.
function readings(state) {
  const { PANEL } = C;
  const K = MD.capacityOf(MD.SOURCES[state.scene]);
  const reached = state.arrived ? MD.reachedOf(MD.SOURCES[state.scene]) : [];
  const kind = MD.kindOf(state.scene);
  const out = [`<text class="er-digit" transform="${faceY(C.FACE + 0.05)} translate(${(PANEL.k[0] + PANEL.k[1]) / 2} 14.4)" font-size="9" text-anchor="middle">${K}</text>`];
  PANEL.domains.forEach((u, i) => out.push(faceLamp(u, -11.6, reached.includes(MD.DOMAINS[i]) ? "er-lens er-reach" : "er-lens")));
  KINDS.forEach((name, i) => {
    out.push(faceLamp(PANEL.kinds[i], -9.6, kind === name ? "er-lens er-fault" : "er-lens"));
    out.push(lever(PANEL.kinds[i], state.pull[i]));
  });
  out.push(selector(state.scene));
  return out.join("");
}

// --- the track ----------------------------------------------------------------------------------

// A rail run from x0 to x1 on one side (y = ±gauge); the bridge's runs come from bridgeRails.
const railRun = (x0, x1, side) => rod([x0, side * C.TRACK.gauge, railZ(x0)], [x1, side * C.TRACK.gauge, railZ(x1)], C.TRACK.rail, { tone: "mid" }, 10);
const FIXED = [[C.TRACK.x0 - 4, C.BRIDGE.x0], [C.BRIDGE.x1, C.TRACK.x1]];
function rails(side) {
  return M("ink", ...FIXED.map(([a, b]) => railRun(a, b, side)), endStops(side));
}
// Stops at each open rail end, so a bead never leaves the track: at the bridge gap and the track's foot.
function endStops(side) {
  const y = side * C.TRACK.gauge;
  return [C.BRIDGE.x0, C.TRACK.x1].map((x) => S(G.disc(-0.6, 0.6, 0.9, G.frameAlong([x, y, railZ(x)], DIR), P, { steps: 12 }), { tone: "mid" })).join("");
}
// A tie under both rails at x, square to the incline.
function tie(x, z = railZ(x)) {
  const F = G.frameOf([x, 0, z - C.TRACK.rail - 0.5], DIR, Y3, UP);
  return S(G.prismOf(F, [[-3.6, -0.6], [3.6, -0.6], [3.6, 0.6], [-3.6, 0.6]], -0.9, 0.9, P), { tone: "mid" });
}
// The chairs that clip each rail to its tie, outboard of the rail so the bead clears them.
function chairs(x, z = railZ(x)) {
  const F = G.frameOf([x, 0, z - C.TRACK.rail - 0.5], DIR, Y3, UP);
  const g = C.TRACK.gauge;
  return [1, -1].map((side) => S(G.prismOf(F, [[g - 0.1, 0.55], [g + 1.3, 0.55], [g + 1.3, 0.95], [g + 0.9, 1.3], [g - 0.1, 1.3]].map(([u, v]) => [side * u, v]), -0.6, 0.6, P), { tone: "mid" })).join("");
}
function ties() {
  const out = [], clips = [];
  for (let x = C.TRACK.x0 + 2; x < C.TRACK.x1 - 1; x += C.TIES) if (x < C.BRIDGE.x0 - 1 || x > C.BRIDGE.x1 + 1) out.push(tie(x)), clips.push(chairs(x));
  return M("marble", ...out) + M("ink", ...clips);
}
// Soft shadows where the posts, the coin's bracket and the station stand on the deck.
function shadows() {
  const spot = (x, y, r, o = 0.35) => `<path class="iso-halo" d="${k.haloOf({ x: x - r, y: y - r, w: 2 * r, d: 2 * r, r }, 0, 0.1, P)}" style="filter:blur(2.5px);opacity:calc(var(--anatomy-halo-opacity) * ${o})"/>`;
  // The track's own shadow, a faint band on the deck under the rails.
  const band = `<path class="iso-halo" d="${k.haloOf({ x: C.CAGE.x1, y: -2, w: C.STATION.x - C.CAGE.x1, d: 4, r: 2 }, 0, 0.1, P)}" style="filter:blur(3px);opacity:calc(var(--anatomy-halo-opacity) * .2)"/>`;
  return [band, ...C.POSTS.map((x) => spot(x, 0, 4.6)), spot(C.WEIGHT[0], C.WEIGHT[1], 4), `<path class="iso-halo" d="${k.haloOf({ x: C.CAGE.x0 - 1, y: -6, w: C.CAGE.x1 - C.CAGE.x0 + 2, d: 12, r: 2 }, 0, 0.1, P)}" style="filter:blur(3px);opacity:calc(var(--anatomy-halo-opacity) * .4)"/>`, `<path class="iso-halo" d="${k.haloOf(k.insetPlan(C.STATION, -2), 0, 0.1, P)}" style="filter:blur(4px);opacity:calc(var(--anatomy-halo-opacity) * .4)"/>`].join("");
}
// A post under the track: an ink foot, a marble column, a jade collar and the saddle the tie sits on.
function post(x) {
  const top = railZ(x) - C.TRACK.rail - 1.1;
  const F = G.frameOf([x, 0, 0], Z3, X3, Y3);
  // A torus base, a fluted shaft with an astragal under the capital, a flared capital.
  const profile = [[0, 3.4], [0.9, 3.4, 1], [1.3, 3.0, 1], [1.8, 2.5, 1], [2.3, 1.75, 1], [2.9, 1.6], [top - 5.4, 1.5], [top - 5.0, 1.95, 1], [top - 4.6, 1.5], [top - 3, 1.5], [top - 2.4, 2.2, 1], [top - 0.8, 2.2]];
  const ribs = G.ribsOf(F, 2.9, top - 5.4, 1.6, 10, P, { fade: [0.05, 0.6], r1: 1.5, seams: true });
  const bolts = [0.6, 2.2, 3.8, 5.4].map((t) => at([x + 3.8 * Math.cos(t), 3.8 * Math.sin(t), 0.9]));
  return M("ink", cyl(x, 0, 4.2, 0, 0.9, { tone: "mid" }, 28, 0.3), D(bolts, { size: 0.36 })) + M("marble", S(G.solidOf(profile, F, P), { tone: "mid", inner: k.fadedSvg(ribs, { tone: "faint" }) })) + M("jade", cyl(x, 0, 2.6, top - 0.8, 0.8, { tone: "mid" }, 20, 0.2));
}

// The hinged bridge: two rails and two ties on one frame, turning about the hinge at x1.
function bridgeRails(lift, side) {
  const { x0, x1 } = C.BRIDGE;
  const a = (lift * C.BRIDGE.lift * Math.PI) / 180;
  const base = Math.atan2(SLOPE, 1);
  const hinge = [x1, 0, railZ(x1)];
  const len = Math.hypot(x1 - x0, railZ(x0) - railZ(x1));
  // Turning about y at the hinge: the far end rises as `lift` grows.
  const pointAt = (along) => [hinge[0] - along * Math.cos(base - a), 0, hinge[2] - along * Math.sin(base - a)];
  const y = side * C.TRACK.gauge;
  const [p0, p1] = [pointAt(0), pointAt(len)];
  return M("ink", rod([p0[0], y, p0[2]], [p1[0], y, p1[2]], C.TRACK.rail, { tone: "mid" }, 10)) + (lift > 0.2 && side > 0 ? D([at([p1[0], y, p1[2]])], { size: 1.1, tone: "red" }) : "");
}
function bridgeTies(lift) {
  const { x0, x1 } = C.BRIDGE;
  const a = (lift * C.BRIDGE.lift * Math.PI) / 180;
  const base = Math.atan2(SLOPE, 1);
  const len = Math.hypot(x1 - x0, railZ(x0) - railZ(x1));
  const hinge = [x1, 0, railZ(x1)];
  const dir = [-Math.cos(base - a), 0, -Math.sin(base - a)];
  const up = [-Math.sin(base - a), 0, Math.cos(base - a)];
  const out = [];
  for (const along of [4, len - 4]) {
    const c = [hinge[0] + dir[0] * along, 0, hinge[2] + dir[2] * along];
    const F = G.frameOf([c[0] - up[0] * (C.TRACK.rail + 0.5), 0, c[2] - up[2] * (C.TRACK.rail + 0.5)], dir, Y3, up);
    out.push(S(G.prismOf(F, [[-3.6, -0.6], [3.6, -0.6], [3.6, 0.6], [-3.6, 0.6]], -0.9, 0.9, P), { tone: "mid" }));
  }
  return M("marble", ...out);
}
// The hinge block and its pin, on the post at the bridge's right end.
function hinge() {
  const { x1 } = C.BRIDGE;
  const z = railZ(x1);
  return M("ink", S(G.prismOf(G.frameOf([x1, 0, z - 2.4], DIR, Y3, UP), [[-4, -1.2], [4, -1.2], [4, 1.2], [-4, 1.2]], -1.8, 1.8, P), { tone: "mid" }), S(G.disc(-4.6, 4.6, 0.7, G.frameOf([x1, 0, z - 1.4], Y3, X3, Z3), P), { tone: "hi" }));
}

// --- the cage, the hopper and the gate -----------------------------------------------------------

function cage(side) {
  const { x0, x1, cheek } = C.CAGE;
  const y = side * cheek;
  const zb = railZ(x1) - 3, zt = railZ(x0) + 8;
  const plate = { x: x0, y: y - 0.6, w: x1 - x0, d: 1.2, r: 0.4 };
  const out = [M("marble", box(plate, zb, zt - zb, { tone: "mid" }, 2, 0.3))];
  out.push(D([[x0 + 2, zb + 2], [x1 - 2, zb + 2], [x0 + 2, zt - 2], [x1 - 2, zt - 2]].map(([x, z]) => at([x, y + 0.62 * side, z])), { size: 0.4 }));
  // The front cheek: a sunk panel between the screws, and the gate pin's boss.
  if (side > 0) out.push(`<g transform="${faceY(y + 0.62)}">${L(rectD(x0 + 3.2, -(zt - 3.2), x1 - 3.2, -(zb + 3.2), 0.8) + rectD(x0 + 3.9, -(zt - 3.9), x1 - 3.9, -(zb + 3.9), 0.5), { tone: "faint" })}</g>`,
    M("ink", S(G.disc(0, 0.5, 0.95, G.frameOf([x1 - 0.05, y + 0.6, railZ(x1) + 6.4], Y3, X3, Z3), P), { tone: "mid" })));
  return out.join("");
}
// The cage's cap: an overhanging ink slab and a raised step the tube's flange stands on.
function cageCap() {
  const { x0, x1, cheek } = C.CAGE;
  const zt = railZ(x0) + 8;
  const cap = { x: x0 - 0.5, y: -cheek - 1, w: x1 - x0 + 1, d: 2 * cheek + 2, r: 0.6 };
  const step = k.insetPlan(cap, 1.3);
  return M("ink", box(cap, zt, 1.2, { tone: "mid", inner: L(k.sideSeam(cap, zt + 0.5, P, 2), { tone: "faint" }) }, 2, 0.3), box(step, zt + 1.2, 0.7, { tone: "mid" }, 2, 0.2), D(k.corners(step, 0.9).map(([x, y]) => at([x, y, zt + 1.9])), { size: 0.4 }));
}
// The tower the cage and its tube stand on: a fluted marble pier on an ink plinth, a jade capital.
function tower() {
  const { x0, x1 } = C.CAGE;
  const top = railZ(x1) - 3;
  const pier = { x: x0 + 1.5, y: -3.6, w: x1 - x0 - 3, d: 7.2, r: 0.8 };
  const plinth = k.insetPlan(pier, -2.2);
  const out = [M("ink", box(plinth, 0, 2.6, { tone: "mid" }, 2, 0.4), D(k.corners(plinth, 1).map(([x, y]) => at([x, y, 2.6])), { size: 0.4 }))];
  // Flutes on the two faces the viewer sees, from the base moulding up to the necking band.
  const [f0, f1] = [3.5, top - 3.6];
  const flutes = [];
  for (const u of [0.2, 0.4, 0.6, 0.8]) flutes.push(k.pathOf([at([pier.x + pier.w * u, pier.y + pier.d, f0]), at([pier.x + pier.w * u, pier.y + pier.d, f1])]));
  for (const u of [0.3, 0.7]) flutes.push(k.pathOf([at([pier.x + pier.w, pier.y + pier.d * u, f0]), at([pier.x + pier.w, pier.y + pier.d * u, f1])]));
  out.push(M("marble", box(pier, 2.6, top - 2.6 - 2, { tone: "mid", inner: L(flutes.join(""), { tone: "faint" }) }, 2, 0.4), box(k.insetPlan(pier, -0.9), 2.6, 0.9, { tone: "mid" }, 2, 0.3), box(k.insetPlan(pier, -0.45), f1, 0.8, { tone: "mid" }, 2, 0.2)));
  out.push(M("jade", box(k.insetPlan(pier, -1.2), top - 2, 2, { tone: "mid", inner: L(k.sideSeam(k.insetPlan(pier, -1.2), top - 1, P, 2), { tone: "faint" }) }, 2, 0.4)));
  return out.join("");
}
// The supply tube above the cage: a stack of beads behind glass.
function hopper(shift) {
  const { x, z0, z1, r } = C.HOPPER;
  const flange = G.frameOf([x, 0, z0 - 1.6], Z3, X3, Y3);
  const out = [M("ink", cyl(x, 0, r + 1.4, z0 - 1.6, 1.6, { tone: "mid" }, 24, 0.3), D(G.dotsOf(flange, 1.6, r + 0.85, 6, P, { all: true, phase: 0.5 }), { size: 0.36 }))];
  out.push(`<path class="er-glass-back" d="${k.cylinder(x, 0, r, z0, z1 - z0, P, 28).fill}"/>`);
  for (let i = 0; i < 8; i++) {
    const z = z0 + C.BEAD + i * 2 * C.BEAD + shift * 2 * C.BEAD;
    if (z < z1 - C.BEAD) out.push(M("jade", S(G.sphereOf([x, 0, z], C.BEAD - 0.1, P), { tone: "mid" })));
  }
  const glass = k.cylinder(x, 0, r, z0, z1 - z0, P, 28);
  out.push(`<path class="er-glass" d="${glass.fill}"/>`, L(glass.outline, { tone: "mid" }), L(k.pathOf([at([x - r * 0.45, r * 0.8, z0 + 3]), at([x - r * 0.45, r * 0.8, z1 - 3])]), { tone: "faint", free: true }));
  // Two clamp rings hold the glass; the cap is knurled, with a filler plug.
  for (const z of [z0 + (z1 - z0) * 0.36, z0 + (z1 - z0) * 0.7]) { const d = bandD(x, 0, r + 0.3, z, z + 0.7); out.push(M("ink", S({ fill: d, outline: d }, { tone: "mid", flat: true }))); }
  out.push(M("ink", cyl(x, 0, r + 1.2, z1, 1.8, { tone: "mid", inner: L(k.knurl(x, 0, r + 1.2, z1, z1 + 1.8, 40, P, 0.12), { tone: "lo" }) }, 28), cyl(x, 0, r + 0.5, z1 + 1.8, 0.5, { tone: "mid" }, 24, 0.15), cyl(x, 0, 1.4, z1 + 2.3, 1.6, { tone: "mid" }, 12, 0.2), S(G.sphereOf([x, 0, z1 + 4.2], 0.7, P), { tone: "mid" })));
  return out.join("");
}
// The gate: a jade flap hanging across the rails from a pin at the cage's top; `open` swings it up.
function gate(open) {
  const x = C.CAGE.x1;
  const z = railZ(x) + 6.4;
  const a = open * 1.25;
  const dir = [Math.sin(a), 0, -Math.cos(a)];
  const F = G.frameOf([x, 0, z], dir, Y3, [Math.cos(a), 0, Math.sin(a)]);
  return M("jade", S(G.prismOf(F, [[-3, -0.4], [3, -0.4], [3, 0.4], [-3, 0.4]], 0, 6.6, P), { tone: "mid" })) + M("ink", S(G.disc(-4.2, 4.2, 0.6, G.frameOf([x, 0, z], Y3, X3, Z3), P), { tone: "mid" }));
}
// The gate's lever: from the gate pin forward over the coin; the coin's weight on its hook holds the gate up.
function gateLever(open) {
  const [px, py, pz] = C.LEVER;
  const tip = leverTip(open);
  const tail = [C.CAGE.x1, -C.CAGE.cheek, railZ(C.CAGE.x1) + 6.4];
  const PF = G.frameOf([px, py, pz], X3, Y3, Z3);
  return M("ink", rod(tail, [C.CAGE.x1, py, pz], 0.45, { tone: "mid" }), rod([C.CAGE.x1, py, pz], [px, py, pz], 0.45, { tone: "mid" }), rod([px, py, pz], tip, 0.55, { tone: "mid" }),
    S(G.disc(-1, 1, 1.2, PF, P), { tone: "mid", inner: L(G.circleOf(PF, 1, 0.75, P, 16), { tone: "faint" }) }), S(G.sphereOf([C.CAGE.x1, py, pz], 0.85, P), { tone: "mid" }))
    + M("jade", S(G.sphereOf(tip, 0.75, P), { tone: "mid" }));
}
// The lever's tip, over the coin's dish; the coin's pull tilts it down as the gate swings up.
const leverTip = (open) => { const [px, py, pz] = C.LEVER; const a = -0.1 + open * 0.22; return [C.COIN[0], py + 7.4 * Math.cos(a), pz - 7.4 * Math.sin(a) - (px - C.COIN[0]) * 0.1]; };
// The payment: a cash coin on its dish post, tied by a cord to the lever's tip; untied, the cord hangs.
function coinPost() {
  const [x, y, z] = C.COIN;
  // The bracket's foot is screwed to the pier's front face (the tower's pier stands 3.6 out from the track).
  const face = 3.6, foot = face + 1.2;
  return M("ink", rod([x, foot, z - 1.6], [x, y, z - 1.6], 0.6, { tone: "mid" }), S(G.prismOf(G.frameOf([x, face, z - 3], Z3, X3, Y3), [[-1.6, 0], [1.6, 0], [1.6, 1.2], [-1.6, 1.2]], 0, 2.8, P), { tone: "mid" }),
    D([at([x - 1.05, foot, z - 2.4]), at([x + 1.05, foot, z - 0.8])], { size: 0.34 }), S(G.disc(-1.4, 0, 0.9, G.frameOf([x, y, z - 1.6], Z3, X3, Y3), P), { tone: "mid" }))
    + M("marble", S(G.lathe([[0, 0], [0, 1.4], [0.8, 3.6, 1], [1.4, 4.2]], G.frameOf([x, y, z - 1.4], Z3, X3, Y3), P, { fill: "surface" }), { tone: "mid" }));
}
function coin(loose, open) {
  const [x, y] = C.COIN;
  const tip = leverTip(open);
  // Tied, the coin hangs from the lever a little above its dish; untied, it lies in the dish.
  const hang = [x, y, C.COIN[2] + 3];
  const rest = [x, y, C.COIN[2] + 0.4];
  const c = hang.map((v, i) => v + (rest[i] - v) * loose);
  const F = G.frameOf(c, Z3, X3, Y3);
  const out = [M("ink", S(G.disc(-0.5, 0.5, 3.4, F, P, { steps: 36 }), { tone: "hi" }), L(k.planOutline({ x: c[0] - 1, y: c[1] - 1, w: 2, d: 2, r: 0 }, c[2] + 0.5, P, 1) + k.ring(c[0], c[1], 2.7, c[2] + 0.5, P, 28), { tone: "faint" }))];
  // The cord: from the lever's tip to the coin's eye; loose, it hangs from the tip with its hook free.
  const eye = [c[0], c[1], c[2] + 0.5];
  const free = [tip[0] + 1.4, tip[1] + 1.2, tip[2] - 9];
  const to = eye.map((v, i) => v + (free[i] - v) * loose);
  out.push(L(k.pathOf([at(tip), at(to)]), { tone: loose > 0.5 ? "red" : "hi", className: "er-cord" }), D([at(to)], { size: 0.9, tone: loose > 0.5 ? "red" : "hi" }));
  return out.join("");
}

// --- the latch and 乙's weight ----------------------------------------------------------------------

// The latch tongue between the rails, pivoted under them: up (`up` 1) it stands across the track.
function latch(up) {
  const x = C.LATCH;
  const z = railZ(x) - C.TRACK.rail - 0.4;
  const a = up * (Math.PI / 2 - 0.12);
  const dir = [-Math.cos(a) * DIR[0] + Math.sin(a) * UP[0], 0, -Math.cos(a) * DIR[2] + Math.sin(a) * UP[2]];
  const F = G.frameOf([x, 0, z], dir, Y3, unit([-dir[2], 0, dir[0]]));
  return M("ink", S(G.prismOf(F, [[-1.1, -0.35], [1.1, -0.35], [1.1, 0.35], [-1.1, 0.35]], 0, 6.4, P), { tone: "hi" }), S(G.disc(-1.6, 1.6, 0.6, G.frameOf([x, 0, z], Y3, X3, Z3), P), { tone: "mid" }));
}
// 乙's lever: a post in front of the latch, an arm, and the weight that keeps the tongue up; lifted onto
// its peg (`up` 0) the weight no longer bears on the arm.
function weight(up) {
  const [x, y] = C.WEIGHT;
  const zp = railZ(x) - 1;
  const out = [M("marble", cyl(x, y, 3.2, 0, 1, { tone: "mid" }, 22, 0.3), cyl(x, y, 1.1, 1, zp - 1, { tone: "mid", crease: "none" }, 14))];
  const a = -0.05 + up * 0.32;
  const arm = [x + 9 * Math.cos(a), y, zp - 9 * Math.sin(a)];
  out.push(M("ink", rod([x - 4, y, zp + 4 * Math.sin(a) * 0.3], arm, 0.5, { tone: "mid" }), rod([x - 4, y, zp], [x - 1, 0, railZ(x) - 1.6], 0.4, { tone: "mid" }), S(G.disc(-1, 1, 1.1, G.frameOf([x, y, zp], Y3, X3, Z3), P), { tone: "mid" })));
  // The weight hangs from the arm's end when it bears; parked, it sits on the peg beside the post.
  const hangTop = [arm[0], y, arm[2] - 0.6];
  const parked = [x + 4.6, y + 3.2, 9.6];
  const top = hangTop.map((v, i) => v + (parked[i] - v) * (1 - up));
  out.push(L(k.pathOf([at(up > 0.5 ? arm : [x + 4.6, y + 3.2, 12]), at(top)]), { tone: "mid" }));
  const F = G.frameOf([top[0], top[1], top[2] - 7], Z3, X3, Y3);
  out.push(M("ink", S(G.solidOf([[0, 2.6], [0.6, 2.8, 1], [5.4, 2.6, 1], [6.2, 1.6, 1], [6.8, 1.4]], F, P), { tone: "hi" }), S(G.sphereOf([top[0], top[1], top[2] + 0.4], 1.1, P), { tone: "hi" })));
  out.push(M("ink", S(G.disc(0, 3, 0.4, G.frameOf([x + 1.2, y + 1, 12], unit([0.8, 0.6, 0]), Z3, X3), P), { tone: "mid" })));
  return out.join("");
}

// --- the life station and the receipts --------------------------------------------------------------

// The station the track runs into: a funnel on its roof, a window for each installed service.
function station(homeLit, clinicLit, shut) {
  const s = C.STATION;
  const front = s.y + s.d;
  const plinth = { x: s.x - 1.5, y: s.y - 1.5, w: s.w + 3, d: s.d + 3, r: 1.2 };
  const out = [box(plinth, 0, 1.6, { tone: "mid" }, 2, 0.4), D(k.corners(plinth, 0.9).map(([x, y]) => at([x, y, 1.6])), { size: 0.36 }), box(s, 1.6, s.h - 1.6, { tone: "mid", inner: L(k.sideSeam(s, 6, P, 2), { tone: "faint" }) }, 2, 0.5)];
  // A window: its pane (lit while its service is installed), a shutter that drops over it, glazing bars.
  const pane = (u0, u1, lit, closing) => `<path class="er-pane${lit ? " er-lit" : ""}" d="${rectD(u0, -16.4, u1, -9, 0.6)}"/>` + (closing > 0 ? `<path class="er-shutter" d="${rectD(u0, -16.4, u1, -16.4 + 7.4 * closing, 0)}"/>` : "")
    + L(`M${(u0 + u1) / 2} -16.4V-9M${u0} -12.7H${u1}`, { tone: "lo" }) + L(rectD(u0, -16.4, u1, -9, 0.6), { tone: "mid" });
  out.push(`<g transform="${faceY(front)}">${pane(s.x + 3.5, s.x + 11, homeLit, 0)}${pane(s.x + 15, s.x + 22.5, clinicLit, shut)}<path class="er-pane" d="${rectD(s.x + 9.5, -5.6, s.x + 16.5, -1.6, 0.8)}"/>${L(rectD(s.x + 9.5, -5.6, s.x + 16.5, -1.6, 0.8), { tone: "mid" })}</g>`);
  // The sills under the windows and the hood over the outlet the bead leaves by.
  for (const [u0, u1] of [[s.x + 2.4, s.x + 12.1], [s.x + 13.9, s.x + 23.6]]) out.push(box({ x: u0, y: front - 0.2, w: u1 - u0, d: 1.1, r: 0.3 }, 7.4, 0.7, { tone: "mid" }, 2, 0.15));
  out.push(M("ink", box({ x: s.x + 8.9, y: front - 0.2, w: 8.2, d: 1.6, r: 0.3 }, 5.9, 0.6, { tone: "mid" }, 2, 0.15)));
  // Corner pilasters on the three corners in view.
  for (const [x, y] of [[s.x + s.w, s.y], [s.x, s.y + s.d], [s.x + s.w, s.y + s.d]]) out.push(box({ x: x - 1.1, y: y - 1.1, w: 2.2, d: 2.2, r: 0.3 }, 1.6, s.h - 1.6, { tone: "mid" }, 2, 0.2));
  // The two services' marks above their windows.
  out.push(`<g transform="${faceY(front + 0.02)}"><g transform="translate(${s.x + 7.25} -18.2) scale(0.85)">${L(glyphD("tenure"), { tone: "lo" })}</g><g transform="translate(${s.x + 18.75} -18.2) scale(0.85)">${L(glyphD("health"), { tone: "lo" })}</g></g>`);
  // The roof: a jade cornice under an ink lid with a sunk panel and screws.
  const cornice = k.insetPlan(s, -0.8), roof = k.insetPlan(s, -1.2);
  out.push(M("jade", box(cornice, s.h, 0.8, { tone: "mid" }, 2, 0.2)));
  out.push(M("ink", box(roof, s.h + 0.8, 0.8, { tone: "mid" }, 2, 0.25), L(k.planOutline(k.insetPlan(roof, 2.4), s.h + 1.6, P, 2), { tone: "faint" }), D(k.corners(roof, 1.2).map(([x, y]) => at([x, y, s.h + 1.6])), { size: 0.4 })));
  // The funnel the track's foot drops into: a collar at its stem and a rolled rim.
  const F = G.frameOf([C.TRACK.x1 + 1, 0, s.h + 1.6], Z3, X3, Y3);
  out.push(M("ink", S(G.disc(0, 0.6, 2.4, F, P), { tone: "mid" })));
  out.push(M("jade", S(G.lathe([[0, 1.6], [0.6, 1.8, 1], [3.6, 4.4, 1], [4.2, 4.8]], F, P, { fill: "surface" }), { tone: "mid", inner: L(G.arcOf(F, 3.75, 4.5, P, { slope: 0.67 }), { tone: "lo" }) })));
  return M("marble", ...out);
}
// The receipts: a glazed channel along the deck's front; every arriving bead joins the row's end.
function channel() {
  const { x0, x1, y, z } = C.ROW;
  const out = [box({ x: x0 - 2, y: y - 3.4, w: x1 - x0 + 4, d: 6.8, r: 1 }, 0, z, { tone: "mid" }, 2, 0.3)];
  out.push(`<path class="iso-shade" data-shade="0" d="${k.planOutline({ x: x0, y: y - 2.4, w: x1 - x0, d: 4.8, r: 0.8 }, z + 0.01, P, 2)}"/>`);
  return M("marble", ...out);
}
// The channel's lip carries the frontier's index: a tick at each bead's place, a long one every fifth.
function ruler() {
  const { y, z } = C.ROW;
  const lip = y + 3.4;
  const minor = [], major = [];
  for (let i = 0; rowAt(i) < C.ROW.x1 - C.BEAD; i++) (i % 5 ? minor : major).push(k.lineOnTop([rowAt(i), lip], [rowAt(i), lip - (i % 5 ? 1 : 1.9)], z, P));
  return L(minor.join(""), { tone: "faint" }) + L(major.join(""), { tone: "lo" });
}
function channelGlass() {
  const { x0, x1, y, z } = C.ROW;
  const h = 4.6, yf = y + 2.4;
  const top = k.planOutline({ x: x0, y: y - 2.4, w: x1 - x0, d: 4.8, r: 0.8 }, z + h, P, 2);
  const front = k.pathOf([[x0 + 1, yf, z], [x1 - 1, yf, z], [x1 - 1, yf, z + h], [x0 + 1, yf, z + h]].map(at), true);
  const out = [`<path class="er-glass" d="${front}"/>`, `<path class="er-glass" d="${top}"/>`, L(top, { tone: "faint" }),
    L(k.pathOf([at([x0 + 6, yf, z + h - 1.1]), at([x1 - 30, yf, z + h - 1.1])]), { tone: "faint", free: true })];
  // The glass stands between two end blocks with ink caps.
  for (const x of [x0 - 2, x1 - 1]) {
    const block = { x, y: y - 3.4, w: 3, d: 6.8, r: 0.6 };
    out.push(M("marble", box(block, z, h, { tone: "mid" }, 2, 0.3)), M("ink", box(k.insetPlan(block, -0.3), z + h, 0.8, { tone: "mid" }, 2, 0.2), D([at([x + 1.5, y + 3.4, z + 1.4]), at([x + 1.5, y + 3.4, z + 3.2])], { size: 0.36 })));
  }
  return out.join("");
}
const rowAt = (i) => C.ROW.x0 + C.BEAD + i * 2 * C.BEAD;
function row(count) {
  const shown = Math.min(count, Math.floor((C.ROW.x1 - C.ROW.x0) / (2 * C.BEAD)) - 1);
  const out = [];
  for (let i = 0; i < shown; i++) out.push(S(G.sphereOf([rowAt(i), C.ROW.y, C.ROW.z + C.BEAD], C.BEAD - 0.1, P), { tone: "mid" }));
  return M("jade", ...out);
}

// --- the bead -----------------------------------------------------------------------------------------

// The bead's journey as one parameter: 0 in the cage, 1 at the track's foot, then the drop through the
// station (1–2) and the roll along the channel to the row's end (2–3).
function beadAt(state) {
  const s = state.s;
  if (s <= 1) {
    const x = C.CAGE.x0 + 5 + (C.TRACK.x1 - C.CAGE.x0 - 5) * s;
    return [x, 0, railZ(x) + LIFT];
  }
  if (s <= 2) {
    const t = s - 1;
    const from = [C.TRACK.x1 + 1, 0, C.STATION.h + 3], to = [C.STATION.x + 13, C.STATION.y + C.STATION.d + 2.5, C.ROW.z + C.BEAD];
    return from.map((v, i) => v + (to[i] - v) * t);
  }
  const t = s - 2;
  const from = [C.STATION.x + 13, C.ROW.y, C.ROW.z + C.BEAD], to = [rowAt(state.receipts), C.ROW.y, C.ROW.z + C.BEAD];
  return from.map((v, i) => v + (to[i] - v) * t);
}
const beadSvg = () => M("jade", S(G.sphereOf([0, 0, 0], C.BEAD, P), { tone: "hi", lit: true }));
const beadTransform = (state) => k.translateAlong(P, beadAt(state));
const stopS = (kind) => (C.STOP[kind] - C.CAGE.x0 - 5) / (C.TRACK.x1 - C.CAGE.x0 - 5);

function composition(state) {
  const inside = state.s > 1 && state.s < 2;
  const onRow = state.s >= 2;
  return [
    base(),
    `<g data-part="readings">${readings(state)}</g>`,
    shadows(),
    tower(),
    ...C.POSTS.filter((x) => x < C.STATION.x).map(post),
    hinge(),
    cage(-1),
    ties(),
    `<g data-part="bridge-ties">${bridgeTies(state.lift)}</g>`,
    rails(-1),
    `<g data-part="bridge-back">${bridgeRails(state.lift, -1)}</g>`,
    `<g data-part="latch">${latch(state.up)}</g>`,
    `<g data-part="gate">${gate(state.open)}</g>`,
    `<g data-part="bead-track" style="display:${onRow || inside ? "none" : "inline"}"><g data-part="bead" transform="${beadTransform(state)}" style="opacity:${n2(state.fade)}">${beadSvg()}</g></g>`,
    rails(1),
    `<g data-part="bridge-front">${bridgeRails(state.lift, 1)}</g>`,
    cage(1),
    cageCap(),
    `<g data-part="hopper">${hopper(state.feed)}</g>`,
    `<g data-part="lever">${gateLever(state.open)}</g>`,
    coinPost(),
    `<g data-part="coin">${coin(state.loose, state.open)}</g>`,
    `<g data-part="weight">${weight(state.up)}</g>`,
    `<g data-part="station">${station(state.homeLit, state.clinicLit, state.shut)}</g>`,
    channel(),
    `<g data-part="row">${row(state.receipts)}</g>`,
    `<g data-part="bead-row" style="display:${onRow ? "inline" : "none"}"><g data-part="bead-low" transform="${beadTransform(state)}" style="opacity:${n2(state.fade)}">${beadSvg()}</g></g>`,
    channelGlass(),
    ruler(),
    `<g class="er-hits">${hitAreas()}</g>`,
  ].join("");
}
function hitAreas() {
  const zone = (name, points) => `<path data-hit="${name}" d="${k.pathOf(G.hullOf(points.map(at)), true)}"/>`;
  const boxPts = (x0, y0, x1, y1, z0, z1) => k.boxCorners({ x: x0, y: y0, w: x1 - x0, d: y1 - y0 }, z0, z1);
  const s = C.STATION;
  return [
    zone("link", boxPts(C.COIN[0] - 6, C.COIN[1] - 6, C.COIN[0] + 6, C.COIN[1] + 6, C.COIN[2] - 5, C.LEVER[2] + 3)),
    zone("path", boxPts(C.BRIDGE.x0 - 2, -4, C.BRIDGE.x1 + 2, 4, railZ(C.BRIDGE.x1) - 4, railZ(C.BRIDGE.x0) + 14)),
    zone("capture", boxPts(C.LATCH - 6, -4, C.WEIGHT[0] + 12, C.WEIGHT[1] + 6, 0, railZ(C.LATCH) + 6)),
    zone("clinic", boxPts(s.x + 13, s.y, s.x + s.w, s.y + s.d + 1, 0, s.h)),
    ...KINDS.map((name, i) => zone(`repair-${name}`, boxPts(C.PANEL.kinds[i] - 7, C.FACE - 1, C.PANEL.kinds[i] + 7, C.FACE + 9, -19, -2))),
  ].join("");
}

// The resting first frame: a whole exit has just joined the row; the next bead waits in the cage.
const REST = { scene: "whole", s: 0, fade: 1, feed: 0, arrived: true, loose: 0, open: 0, lift: 0, up: 0, shut: 0, pull: [0, 0, 0], receipts: 7, homeLit: true, clinicLit: true };

const svg = k.figureSvg({
  width: WIDTH,
  height: HEIGHT,
  className: "er-svg",
  label: "An exit instrument. A jade bead waits in a cage under a tube of beads, at the top of a two-rail track that runs down to a station with two windows, one for each service, and from there into a glazed channel where arrived beads line up. On the way it meets three links: a cash coin tied by a cord to the lever that lifts the cage's gate, a hinged section of rail over a gap, and a latch tongue held up by a weight on 乙's lever. The base's panel shows the exit capacity K, a lamp for each service reached, and a lamp and a repair lever for each kind of failure. Untying the coin, raising the bridge or letting 乙's weight bear on the latch each reads K = 0, and only the matching lever repairs it. Shuttering the health window leaves K at 1. Each completed exit adds one bead to the row.",
  body: composition(REST),
});

const CSS = `
.er-svg{--er-fault:var(--cinnabar,#c8372d);--er-reach:#9fc7a9}
.er-svg .er-window{fill:#151819}
.er-svg .er-digit{fill:#eef2ef;font-family:var(--anatomy-mono);font-variant-numeric:tabular-nums}
.er-svg .er-lens{fill:#2a2f30;transition:fill .35s var(--anatomy-ease)}
.er-svg .er-lens.er-reach{fill:var(--er-reach)}
.er-svg .er-lens.er-fault{fill:var(--er-fault)}
.er-svg .er-pane{fill:#7b8486;stroke:none;transition:fill .5s var(--anatomy-ease)}
.er-svg .er-pane.er-lit{fill:#eef6ea}
.er-svg .er-shutter{fill:var(--anatomy-shade-1);stroke:var(--anatomy-mid);stroke-width:.4}
.er-svg .er-glass{fill:#eef5f1;stroke:none;opacity:.42}
.er-svg .er-glass-back{fill:#dfe9e3;stroke:none;opacity:.5}
.er-svg .er-glint{fill:#fff;stroke:none;opacity:.55}
.er-svg .er-cord{stroke-width:1.1}
.er-svg .iso-line[data-tone="red"]{stroke:var(--er-fault)}
.er-svg .iso-dots[data-tone="red"] circle{fill:var(--er-fault);opacity:1}
.er-svg .er-hits path{fill:transparent;cursor:pointer}
.iso[data-theme="dark"] .er-svg .er-pane{fill:#101314}
.iso[data-theme="dark"] .er-svg .er-pane.er-lit{fill:#cfe6d2}
.iso-stage{outline:none;touch-action:pan-y}
.iso-stage:focus-visible{box-shadow:0 0 0 1px var(--anatomy-mid)}
${SWING_CSS}
@media (max-width:560px){.iso-plate:has(.er-svg){overflow:hidden}.er-svg.iso-svg{width:114%;max-width:none;margin:0 -7%}}
`;

const strip = (file) => readFileSync(join(HERE, file), "utf8").replace(/^export /gm, "");
const kitSource = strip("../kit/iso-kit.mjs");
const latheSource = `const LATHE = (() => {\n${strip("../kit/lathe.mjs").replace(/^import .*$/gm, "")}\nreturn { ${Object.keys(G).join(", ")} };\n})();`;
const modelSource = `const MD = (() => {\n${strip("model.mjs")}\nreturn { ${Object.keys(MD).join(", ")} };\n})();`;

const live = `
const P0 = ${JSON.stringify(P0)};
let P = P0;
${shipped({ C, SELECTOR, SLOPE, LIFT, FRAME, KINDS, REPAIR_OF, DOMAINS_ICON, X3, Y3, Z3 })}
const k = { ${Object.keys(k).join(", ")} };
const G = LATHE;
${shipped({ railZ, at, S, L, D, M, n2, faceY, rectD, box, cyl, unit })}
const DIR = unit([1, 0, SLOPE]);
const UP = unit([-SLOPE, 0, 1]);
${shipped({ rod, bandD, chairs, selector, selectorFace, ruler, shadows, tower, base, glyphD, icon, faceLamp, lever, panel, readings, railRun, rails, endStops, tie, ties, post, bridgeRails, bridgeTies, hinge, cage, cageCap, hopper, gate, gateLever, leverTip, coinPost, coin, latch, weight, station, channel, channelGlass, rowAt, row, beadAt, beadSvg, beadTransform, stopS, composition, hitAreas })}
const FIXED = [[C.TRACK.x0 - 4, C.BRIDGE.x0], [C.BRIDGE.x1, C.TRACK.x1]];
${swingSource}
${liveScript()}
`;

// The page: a tour of the five sources, clicks that break a link, levers that repair it.
function liveScript() {
  return String.raw`
const root = document.querySelector('[data-figure="exit-run"]');
const stage = root.querySelector(".iso-stage");
const svg = stage.querySelector("svg");
const readout = root.querySelector("[data-readout]");
const still = matchMedia("(prefers-reduced-motion: reduce)");
const T = root.dataset;
const st = { scene: "whole", s: 0, fade: 1, feed: 0, arrived: true, loose: 0, open: 0, lift: 0, up: 0, shut: 0, pull: [0, 0, 0], receipts: 7, homeLit: true, clinicLit: true };
const goal = { loose: 0, lift: 0, up: 0, shut: 0 };
let steps = [], step = null, stepTime = 0, touring = !still.matches, idle = 0, visible = false, frame = 0, last = 0, tourAt = 0;
const part = (name) => svg.querySelector('[data-part="' + name + '"]');
const sourceOf = () => MD.SOURCES[st.scene];
const K = () => MD.capacityOf(sourceOf());
// How far the bead can run: to the foot when an exit exists, else to the failing link.
const stopAt = () => (K() > 0 ? 3 : stopS(MD.kindOf(st.scene)));
function say() {
  const kind = MD.kindOf(st.scene), reached = st.arrived ? MD.reachedOf(sourceOf()) : [];
  const parts = ["K " + K()];
  if (kind) parts.push(T.source + " " + T[kind]);
  else if (st.arrived) parts.push(reached.map((d) => T[d]).join(" ") + (reached.length < MD.DOMAINS.length ? " · " + T.health + " " + T.none : ""));
  parts.push(T.receipts + " " + st.receipts);
  const text = parts.join(" · ");
  if (readout.textContent !== text) readout.textContent = text;
  stage.setAttribute("aria-valuetext", text);
}
let shown = {};
function paint(force = false) {
  const key = (v) => JSON.stringify(v);
  const want = {
    readings: key([st.scene, st.arrived, st.pull.map(n2)]), row: key([st.receipts]), hopper: key([n2(st.feed)]),
    "bridge-ties": key([n2(st.lift)]), "bridge-back": key([n2(st.lift)]), "bridge-front": key([n2(st.lift)]),
    latch: key([n2(st.up)]), gate: key([n2(st.open)]), lever: key([n2(st.open)]), coin: key([n2(st.loose), n2(st.open)]),
    weight: key([n2(st.up)]), station: key([st.homeLit, st.clinicLit, n2(st.shut)]),
  };
  const draw = {
    readings: () => readings(st), row: () => row(st.receipts), hopper: () => hopper(st.feed),
    "bridge-ties": () => bridgeTies(st.lift), "bridge-back": () => bridgeRails(st.lift, -1), "bridge-front": () => bridgeRails(st.lift, 1),
    latch: () => latch(st.up), gate: () => gate(st.open), lever: () => gateLever(st.open), coin: () => coin(st.loose, st.open),
    weight: () => weight(st.up), station: () => station(st.homeLit, st.clinicLit, st.shut),
  };
  for (const name of Object.keys(want)) if (force || want[name] !== shown[name]) part(name).innerHTML = draw[name]();
  shown = want;
  // The bead moves by a transform; on the track, in the station and on the row it sits in different slots.
  const onRow = st.s >= 2, inside = st.s > 1 && st.s < 2;
  part("bead-track").style.display = onRow || inside ? "none" : "inline";
  part("bead-row").style.display = onRow ? "inline" : "none";
  for (const name of ["bead", "bead-low"]) { const node = part(name); node.setAttribute("transform", beadTransform(st)); node.style.opacity = n2(st.fade); }
  say();
}
const cycle = () => [{ kind: "feed" }, { kind: "release" }, { kind: "run" }, { kind: "arrive" }, { kind: "wait", t: 1.2 }];
const pullStep = (i) => [{ kind: "pull", i }, { kind: "wait", t: 0.5 }];
const breakStep = (name) => [{ kind: "break", name }, { kind: "wait", t: 0.8 }];
const sceneSteps = (name) => (name === "single" ? [{ kind: "single", on: true }] : name === "whole" ? [{ kind: "single", on: false }] : breakStep(name));
const TOUR = [
  ...cycle(),
  ...breakStep("link"), ...cycle(), ...pullStep(0), ...cycle(),
  ...breakStep("path"), ...cycle(), ...pullStep(2), { kind: "wait", t: 0.7 }, ...pullStep(1), ...cycle(),
  ...breakStep("capture"), ...cycle(), ...pullStep(1), { kind: "wait", t: 0.7 }, ...pullStep(2), ...cycle(),
  { kind: "single", on: true }, { kind: "wait", t: 0.8 }, ...cycle(), { kind: "single", on: false }, { kind: "wait", t: 0.8 },
];
function apply(name) {
  goal.loose = name === "link" ? 1 : 0;
  goal.lift = name === "path" ? 1 : 0;
  goal.up = name === "capture" ? 1 : 0;
  goal.shut = name === "single" ? 1 : 0;
}
function begin(next) {
  step = next;
  stepTime = 0;
  if (step.kind === "feed") { st.arrived = false; if (st.s >= 1) { st.s = 0; st.fade = 0; } }
  else if (step.kind === "break") { st.scene = step.name; st.arrived = false; st.clinicLit = true; apply(st.scene); }
  else if (step.kind === "single") { st.scene = step.on ? "single" : "whole"; st.arrived = false; st.clinicLit = !step.on; apply(st.scene); }
  else if (step.kind === "pull") {
    const kind = KINDS[step.i];
    // A lever repairs its own link only; on any other source it springs back and changes nothing.
    if (MD.kindOf(st.scene) === kind && MD.effective(sourceOf(), REPAIR_OF[kind])) { st.scene = "whole"; apply("whole"); }
  }
}
function advance(dt) {
  if (!step) {
    if (steps.length) begin(steps.shift());
    else if (touring) { begin(TOUR[tourAt]); tourAt = (tourAt + 1) % TOUR.length; }
    else return false;
  }
  stepTime += dt;
  if (step.kind === "feed") {
    // A new bead drops from the tube into the cage.
    st.fade = Math.min(1, stepTime / 0.4);
    st.feed = Math.max(0, 1 - stepTime / 0.4);
    if (stepTime >= 0.45) { st.fade = 1; st.feed = 0; step = null; }
  } else if (step.kind === "release") {
    // Tied, the coin's weight swings the gate up; untied, the gate stays down.
    const want = MD.SOURCES[st.scene].link ? 1 : 0;
    st.open = Math.min(1, stepTime / 0.4) * want;
    if (stepTime >= 0.45) step = null;
  } else if (step.kind === "run") {
    const target = stopAt();
    const speed = st.s < 1 ? 0.42 : st.s < 2 ? 1.6 : 0.9;
    st.s = Math.min(target, st.s + dt * speed);
    if (st.s > 0.08) st.open = Math.max(0, st.open - dt * 2);
    if (st.s > 1.3 && K() > 0) st.arrived = true;
    if (st.s >= target) step = null;
  } else if (step.kind === "arrive") {
    if (K() > 0 && st.s >= 3) { st.receipts += 1; st.s = 3; st.fade = 0; }
    step = null;
  } else if (step.kind === "pull") {
    const t = stepTime / 0.6;
    st.pull[step.i] = Math.sin(Math.min(1, t) * Math.PI);
    if (t >= 1) { st.pull[step.i] = 0; step = null; }
  } else if (step.kind === "wait") { if (stepTime >= step.t) step = null; }
  else step = null;
  return true;
}
function ease(dt) {
  let moving = false;
  const f = still.matches || !dt ? 1 : 1 - Math.exp(-dt / 0.18);
  for (const name of ["loose", "lift", "up", "shut"]) {
    const next = st[name] + (goal[name] - st[name]) * f;
    st[name] = Math.abs(goal[name] - next) < 0.002 ? goal[name] : next;
    if (st[name] !== goal[name]) moving = true;
  }
  return moving;
}
function tick(time) {
  const dt = last ? Math.min((time - last) / 1000, 1 / 30) : 1 / 60;
  last = time;
  const busy = advance(dt);
  const moving = ease(dt);
  paint();
  frame = visible && (busy || moving || touring) ? requestAnimationFrame(tick) : 0;
}
const run = () => { if (!frame && visible) { last = 0; frame = requestAnimationFrame(tick); } };
const hold = () => { touring = false; clearTimeout(idle); idle = setTimeout(() => { touring = !still.matches; run(); }, 9000); };
// Under reduced motion each request is carried out at once.
function now(list) {
  if (!still.matches) { steps.push(...list); run(); return; }
  for (const next of list) {
    begin(next);
    if (next.kind === "feed") { st.fade = 1; st.feed = 0; }
    if (next.kind === "run") { st.s = stopAt(); if (K() > 0) st.arrived = true; }
    if (next.kind === "arrive") { step = next; advance(0); }
    step = null;
  }
  st.pull = [0, 0, 0];
  st.open = 0;
  ease(0);
  paint();
}
stage.addEventListener("click", (event) => {
  const hit = event.target.closest("[data-hit]");
  hold();
  steps = [];
  step = null;
  const name = hit ? hit.dataset.hit : "run";
  if (name === "clinic") now([{ kind: "single", on: st.scene !== "single" }, ...cycle()]);
  else if (name.startsWith("repair-")) now([...pullStep(KINDS.indexOf(name.slice(7))), ...cycle()]);
  else if (KINDS.includes(name)) now([...breakStep(name), ...cycle()]);
  else now(cycle());
});
const ORDER = ["whole", "link", "path", "capture", "single"];
stage.addEventListener("keydown", (event) => {
  const i = ORDER.indexOf(st.scene);
  let next = null;
  if (event.key === "ArrowRight") next = ORDER[(i + 1) % ORDER.length];
  else if (event.key === "ArrowLeft") next = ORDER[(i + ORDER.length - 1) % ORDER.length];
  else if (event.key === " " || event.key === "Enter") next = st.scene;
  else return;
  event.preventDefault();
  hold();
  steps = [];
  step = null;
  now([...sceneSteps(next), ...cycle()]);
});
new IntersectionObserver((entries) => { visible = entries[entries.length - 1].isIntersecting; if (visible) run(); }, { rootMargin: "120px 0px" }).observe(stage);
if (still.matches) touring = false;
paint(true);
// A sideways drag swings the view (../swing.mjs): the instrument is redrawn from there.
mountSwing(stage, { onHold: hold, onSwing: (angle) => { P = swingOf(iso, P0, FRAME, angle); svg.innerHTML = composition(st); shown = {}; paint(true); } });
`;
}

const COPY = {
  en: {
    title: "Three zeros, two ones",
    hint: "Click a link · levers repair · drag to look round",
    keys: ["K: the exit capacity, an accurate count", "Lamp: the source keeps the failure kind", "Bead: one paid exit, never reissued"],
    refs: ["Theorem 5.1", "Propositions 5.2–5.3", "Theorem 1.3"],
    caption: [
      "甲, the jade bead, leaves its cage. A real exit needs one action that continues outside the old role, is not idle, is not captured, carries the payment's association, and has a path to a service actually provided. The capacity K counts how many such exits can hold at once; here it is 1.",
      "Untie the coin, raise the bridge, or let 乙's weight hold the latch: each reads K = 0, and the three sources stay distinct. No function of K recovers which link broke, and the lever that repairs one leaves the others at 0. The source keeps its failure kind, and with it the one effective lever.",
      "Shutter the health window and K still reads 1, yet the health service no longer occurs: an accurate count cannot decide whether the full life bundle holds.",
      "Each completed exit adds its own bead to the row. K stays 1, while the paid frontier keeps every old bead and gains one outside it.",
    ],
    aria: "Exit instrument: click the coin, the bridge or 乙's weight to break a link, the levers to repair, the health window to remove its service; arrow keys step through the sources",
    source: "source", link: "payment link", path: "path", capture: "captured", tenure: "home", health: "health", none: "no service", receipts: "beads",
  },
  zh: {
    title: "三个零，两个一",
    hint: "点击断开一环 · 拉杆修复 · 拖动侧看",
    keys: ["K：退出容量，准确的计数", "灯：来源保留失败的种类", "玉珠：一次已付的退出，不会重开"],
    refs: ["定理 5.1", "命题 5.2–5.3", "定理 1.3"],
    caption: [
      "玉珠甲离开笼门。一条真实的退出，需要同一项行动同时满足：在原角色之外继续、不闲置、不受捕获、带着这次支付的关联，并有通路接到实际已经提供的服务。退出容量 K 计数能同时成立的退出，这里是 1。",
      "解开铜钱的绳、吊起轨桥，或让乙的坠子压住锁舌：三种情形都读出 K = 0，三个来源却彼此不同。任何只看 K 的函数都无法恢复断在哪一环；修好其中一环的那根拉杆，对另外两种仍是 0。来源保留了失败的种类，也就保留了唯一有效的那根拉杆。",
      "合上健康窗的百叶，K 仍读 1，健康服务却已不再发生：准确的计数也判断不了完整的生活组合是否成立。",
      "每走通一次，队列里就多一颗自己的玉珠。K 一直是 1，已付的前沿保住每一颗旧珠，又加上一颗旧像之外的新珠。",
    ],
    aria: "出路仪：点击铜钱、轨桥或乙的坠子断开一环，拉杆修复，点击健康窗撤去健康服务；方向键切换来源",
    source: "来源", link: "支付关联", path: "通路", capture: "捕获", tenure: "居", health: "医", none: "无服务", receipts: "玉珠",
  },
};
const bodyOf = (lang) => {
  const copy = COPY[lang];
  const data = ["source", "link", "path", "capture", "tenure", "health", "none", "receipts"].map((key) => `data-${key}="${copy[key]}"`).join(" ");
  return `<div data-figure="exit-run" ${data}>${k.plateHtml({
    fig: "Fig 5.2",
    title: copy.title,
    hint: copy.hint,
    readout: `K 1 · ${copy.tenure} ${copy.health} · ${copy.receipts} 7`,
    keys: [
      { mark: "raised", label: copy.keys[0] },
      { mark: "red", label: copy.keys[1] },
      { mark: "lit", label: copy.keys[2] },
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
  writeFileSync(join(outDir, "exit-run.json"), JSON.stringify({ html: { zh: bodyOf("zh"), en: bodyOf("en") }, css: CSS, script }));
  console.log("wrote src/generated/exit-run.json");
} else {
  mkdirSync(join(HERE, "out"), { recursive: true });
  const name = theme === "light" ? "exit-run-light.html" : "exit-run.html";
  writeFileSync(join(HERE, "out", name), k.pageHtml({ title: "Three zeros, two ones", theme, body: `<style>${CSS}</style>${bodyOf(process.argv.includes("--zh") ? "zh" : "en")}`, script: `{\n${kitSource}\n${latheSource}\n${modelSource}\n${live}\n}`, width: 760 }));
  console.log("wrote out/" + name);
}
