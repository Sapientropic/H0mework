// Fig: a paper-tape reader that runs prog_κ(T) (Theorem 3.9).
//   bun build.mjs [--light]   → out/source-tape[-light].html (standalone, for checks)
//   bun build.mjs --fragment  → ../../src/generated/source-tape.json (for the site)
import { mkdirSync, readFileSync, writeFileSync } from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";
import * as k from "../kit/iso-kit.mjs";
import { CHANNELS, READ_CHANNELS, figureData } from "./model.mjs";
import { shipped, SWING_CSS, swingSource } from "../swing.mjs";

const HERE = dirname(fileURLToPath(import.meta.url));
const theme = process.argv.includes("--light") ? "light" : "dark";
const fragment = process.argv.includes("--fragment");

const WIDTH = 640;
const HEIGHT = 280;

const PLATE = { x: -165, y: -42, w: 330, d: 136, r: 8 };
const PLATE_H = 10;
const FOOT_H = 5;

const TAPE_Z = 26;
const TAPE_T = 0.8;
const TAPE_TOP = TAPE_Z + TAPE_T;
const TAPE = { from: -112, to: 112, y: -14, d: 28 };
const PITCH = 8.5;
const CH_Y = CHANNELS.map((_, index) => -10.8 + 3.6 * index);
const HOLE_R = 1.45;
const FEED_R = 0.75;

const EXEC_X = -48;
const READ_X = 48;
const CHEEK_H = 42;
const BRIDGE_H = 8;
const SHOES = [-84, 0, 84];

const BIN_H = 46;
const BIN_L = { x: -152, y: -28, w: 40, d: 56, r: 3 };
const BIN_R = { x: 112, y: -28, w: 40, d: 56, r: 3 };

const SRC_BOARD = { x: -158, y: 48, w: 62, d: 28, r: 3 };
const READ_BOARD = { x: 18, y: 48, w: 62, d: 28, r: 3 };
const BOARD_H = 5;

const DIAL = [-68, 56];
const DIAL_R = 15;
const DIAL_Z = 20;
const DIAL_TOP = DIAL_Z + 7;
const PER_TURN = 10;

const KAPPA = { x: -50, y: 64, w: 34, d: 12, r: 2 };
const KAPPA_H = 3;
const KAPPA_STOPS = { zero: KAPPA.x + 9, size: KAPPA.x + KAPPA.w - 7 };

const FIT = [
  ...k.boxCorners(PLATE, -PLATE_H - FOOT_H, 0),
  [EXEC_X, 0, CHEEK_H + BRIDGE_H + 6],
  [BIN_L.x, BIN_L.y, BIN_H + 4],
  [BIN_R.x + BIN_R.w, BIN_R.y + BIN_R.d, BIN_H + 4],
];
const P = k.fitProjection(FIT, WIDTH, HEIGHT, { pad: 26, azimuth: 58 });
// The page swings the view (../swing.mjs), framed by the same fit, and redraws `composition` there.
const FRAME = { points: FIT, width: WIDTH, height: HEIGHT, pad: 26 };

const at = (point) => k.iso(point, P);
const S = (paths, style) => k.solidSvg(paths, style);
const L = (d, style) => k.lineSvg(d, style);
const D = (points, style) => k.dotsSvg(points, style);
// Stone (kit iso.css, data-mat): a group remaps the tone ramp of what it holds.
const M = (material, ...svg) => `<g data-mat="${material}">${svg.join("")}</g>`;
const byDepth = (points) => [...points].sort((a, b) => k.depthOf([a[0], a[1], 0], P) - k.depthOf([b[0], b[1], 0], P));
const loop = (points) => k.pathOf(points.map(at)) + "Z";

function plate() {
  const out = [`<path class="iso-halo" d="${k.haloOf(PLATE, -PLATE_H - FOOT_H, PLATE_H, P)}"/>`];
  for (const [x, y] of byDepth(k.corners(PLATE, 24))) {
    out.push(M("ink", S(k.cylinder(x, y, 8, -PLATE_H - FOOT_H, 1.6, P, 28), { tone: "lo" }), S(k.cylinder(x, y, 6, -PLATE_H - FOOT_H + 1.6, FOOT_H - 1.6, P, 28), { tone: "mid" })));
  }
  const top = [S(k.slabOf(PLATE, -PLATE_H, PLATE_H, P, 8, 1.6), { tone: "mid", inner: L(k.sideSeam(PLATE, -4, P, 8), { tone: "faint" }) })];
  top.push(L(k.planOutline(k.insetPlan(PLATE, 5), 0, P), { tone: "lo" }));
  const screws = k.corners(PLATE, 11);
  top.push(L(screws.map(([x, y]) => k.ring(x, y, 2.2, 0, P, 16)).join(""), { tone: "lo" }));
  top.push(D(screws.map(([x, y]) => at([x, y, 0])), { size: 0.5 }));
  out.push(M("marble", ...top));
  const strip = { x: -142, y: PLATE.y + PLATE.d - 15, w: 230, d: 7, r: 1 };
  const ticks = k.topTicks(strip.x + 4, strip.x + strip.w - 4, PITCH, 5, strip.y + 0.8, 0.6, [2, 3.6], P);
  out.push(M("jade", S(k.slabOf(strip, 0, 0.6, P, 3), { tone: "lo", crease: "none" }), L(ticks.minor, { tone: "lo" }), L(ticks.major, { tone: "mid" }),
    D([at([strip.x + 2, strip.y + 3.5, 0.6]), at([strip.x + strip.w - 2, strip.y + 3.5, 0.6])], { size: 0.45 })));
  const label = { x: 104, y: 58, w: 42, d: 18, r: 1.5 };
  out.push(M("ink", S(k.slabOf(label, 0, 0.8, P, 3, 0.3), { tone: "lo", crease: "none" }),
    ...[label.y + 5, label.y + 9, label.y + 13].map((y, index) => L(k.lineOnTop([label.x + 5, y], [label.x + (index === 2 ? 22 : 37), y], 0.8, P), { tone: "faint", free: true })),
    D([at([label.x + 2, label.y + 2.5, 0.8]), at([label.x + label.w - 2, label.y + label.d - 2.5, 0.8])], { size: 0.4 })));
  return out.join("");
}

function board(plan) {
  const out = [`<path class="iso-halo" d="${k.haloOf(plan, 0, BOARD_H, P)}" style="filter:blur(4px)"/>`];
  const grid = [];
  for (let gx = plan.x + 9; gx <= plan.x + plan.w - 8; gx += 9) for (let gy = plan.y + 8; gy <= plan.y + plan.d - 5; gy += 10) grid.push(at([gx, gy, BOARD_H]));
  out.push(M("jade", S(k.slabOf(plan, 0, BOARD_H, P, 4, 0.6), { tone: "mid" }), L(k.planOutline(k.insetPlan(plan, 2.5), BOARD_H, P, 3), { tone: "faint" }), D(grid, { size: 0.45, tone: "lo" })));
  return out.join("");
}

function bin(plan, side) {
  const halo = `<path class="iso-halo" d="${k.haloOf(plan, 0, BIN_H, P)}"/>`;
  const out = [];
  out.push(S(k.slabOf(plan, 0, BIN_H, P, 4, 0.8), { tone: "mid", inner: L(k.sideSeam(plan, 6, P, 4), { tone: "faint" }) }));
  const lid = k.insetPlan(plan, -1);
  out.push(S(k.slabOf(lid, BIN_H, 4, P, 4, 0.6), { tone: "mid" }));
  out.push(L(k.planOutline(k.insetPlan(lid, 4), BIN_H + 4, P, 3), { tone: "faint" }));
  const pull = { x: plan.x + plan.w / 2 - 7, y: plan.y + plan.d / 2 - 2, w: 14, d: 4, r: 1.5 };
  out.push(M("jade", S(k.slabOf(pull, BIN_H + 4, 2, P, 3), { tone: "mid", crease: "none" })));
  out.push(D(k.corners(lid, 3.5).map(([x, y]) => at([x, y, BIN_H + 4])), { size: 0.45 }));
  // Vent slots on the front face (y = plan.y + plan.d), closed outlines.
  const front = plan.y + plan.d;
  for (let index = 0; index < 4; index++) {
    const x0 = plan.x + 8 + index * 7;
    out.push(L(loop([[x0, front, 18], [x0 + 3, front, 18], [x0 + 3, front, 34], [x0, front, 34]]), { tone: "lo" }));
  }
  const tag = [plan.x + 7, plan.x + 33, 37.5, 43];
  out.push(L(loop([[tag[0], front, tag[2]], [tag[1], front, tag[2]], [tag[1], front, tag[3]], [tag[0], front, tag[3]]]), { tone: "mid" }));
  out.push(L(k.segment([tag[0] + 3, front, 41], [tag[0] + 17, front, 41], P), { tone: "faint", free: true }));
  out.push(L(k.segment([tag[0] + 3, front, 39.3], [tag[0] + 11, front, 39.3], P), { tone: "faint", free: true }));
  out.push(D([at([tag[0] - 2, front, 40.2]), at([tag[1] + 2, front, 40.2])], { size: 0.45 }));
  if (side === "left") {
    // The slot on the +x face that the tape leaves through.
    const face = plan.x + plan.w;
    out.push(L(loop([[face, TAPE.y - 2, TAPE_Z - 1.6], [face, TAPE.y + TAPE.d + 2, TAPE_Z - 1.6], [face, TAPE.y + TAPE.d + 2, TAPE_TOP + 1.6], [face, TAPE.y - 2, TAPE_TOP + 1.6]]), { tone: "mid" }));
    out.push(D([at([face, TAPE.y - 5, TAPE_Z]), at([face, TAPE.y + TAPE.d + 5, TAPE_Z])], { size: 0.45 }));
  }
  return halo + M("ink", ...out);
}

const cheek = (x, front) => ({ x: x - 12, y: front ? 17 : -28, w: 24, d: 11, r: 1.5 });
const bridge = (x) => ({ x: x - 13, y: -29, w: 26, d: 58, r: 2 });

function headBack(x) {
  const plan = cheek(x, false);
  return M("marble", S(k.slabOf(plan, 0, CHEEK_H, P, 3, 0.5), { tone: "mid" }));
}

function shoe(x) {
  const out = [M("marble", S(k.cylinder(x, 0, 2.6, 0, TAPE_Z - 3, P, 20), { tone: "mid" }))];
  out.push(M("ink", S(k.cylinder(x, 0, 5, 0, 1.6, P, 24), { tone: "lo" })));
  out.push(M("jade", S(k.slabOf({ x: x - 7, y: -19, w: 14, d: 38, r: 2 }, TAPE_Z - 3, 3, P, 3, 0.4), { tone: "mid" }), S(k.slabOf(guide(x, false), TAPE_Z, 2.6, P, 2, 0.3), { tone: "mid" })));
  return out.join("");
}

const guide = (x, front) => ({ x: x - 5, y: front ? TAPE.y + TAPE.d + 0.6 : TAPE.y - 2.6, w: 10, d: 2, r: 0.6 });
const shoeFront = (x) => M("jade", S(k.slabOf(guide(x, true), TAPE_Z, 2.6, P, 2, 0.3), { tone: "mid" })) + D([at([x - 3, TAPE.y + TAPE.d + 1.6, TAPE_Z + 2.6]), at([x + 3, TAPE.y + TAPE.d + 1.6, TAPE_Z + 2.6])], { size: 0.4 });

function tape() {
  const plan = { x: TAPE.from, y: TAPE.y, w: TAPE.to - TAPE.from, d: TAPE.d, r: 0 };
  return S(k.slabOf(plan, TAPE_Z, TAPE_T, P, 1), { tone: "hi", lit: true, crease: "lo" });
}

function headFront(x, kind) {
  const out = [];
  const plan = cheek(x, true);
  out.push(M("marble", S(k.slabOf(plan, 0, CHEEK_H, P, 3, 0.5), { tone: "mid", inner: L(k.sideSeam(plan, 6, P, 3), { tone: "faint" }) })));
  const top = bridge(x);
  out.push(M("marble", S(k.slabOf(top, CHEEK_H, BRIDGE_H, P, 4, 0.8), { tone: "mid" }), D(k.corners(top, 3.5).map(([px, py]) => at([px, py, CHEEK_H + BRIDGE_H])), { size: 0.45 })));
  const face = plan.y + plan.d;
  if (kind === "exec") {
    // Step counter: a recessed window on the front face with two digits.
    const w0 = x - 8, w1 = x + 8, z0 = 26, z1 = 36;
    out.push(`<path class="iso-fill" d="${loop([[w0, face, z0], [w1, face, z0], [w1, face, z1], [w0, face, z1]])}" style="fill:var(--anatomy-shade-0)"/>`);
    out.push(L(loop([[w0, face, z0], [w1, face, z0], [w1, face, z1], [w0, face, z1]]), { tone: "mid" }));
    out.push(L(k.segment([x, face, z0], [x, face, z1], P), { tone: "faint" }));
    out.push(`<text data-part="counter" class="iso-face-text" data-tone="hi" transform="${k.sideMatrix([x, face], z0 + 2.2, P, "left")}" font-size="7" text-anchor="middle" letter-spacing="2.4">00</text>`);
    out.push(D([at([x - 10, face, 31]), at([x + 10, face, 31])], { size: 0.45 }));
    out.push(L(k.sideRing([x, face, 20], 2, "y", P, 24), { tone: "mid" }));
    out.push(`<path class="st-lamp" d="${k.sideRing([x, face, 20], 1.2, "y", P, 20)}"/>`);
    out.push(`<path class="st-lamp" data-on data-part="pay" style="opacity:0" d="${k.sideRing([x, face, 20], 1.2, "y", P, 20)}"/>`);
  } else {
    // A row of five sensing pins on the bridge, one over each channel the reader uses;
    // the map channel has a blanking plug, the feed track a sprocket boss.
    const z = CHEEK_H + BRIDGE_H;
    const cells = CHANNELS.map((name, index) => ({ name, y: CH_Y[index] })).sort((a, b) => a.y - b.y);
    out.push(M("ink", S(k.slabOf({ x: x - 4, y: -14, w: 8, d: 28, r: 1.5 }, z, 2, P, 3, 0.4), { tone: "mid" })));
    for (const { name, y } of cells) {
      if (name === "feed") out.push(S(k.cylinder(x, y, 1, z + 2, 0.8, P, 16), { tone: "lo" }));
      else if (name === "map") out.push(S(k.cylinder(x, y, 0.9, z + 2, 0.4, P, 16), { tone: "lo", crease: "none" }));
      else out.push(`<g data-pin="${name}" data-mat="jade">${S(k.cylinder(x, y, 1.2, z + 2, 5, P, 16), { tone: "hi" })}</g>`);
    }
    // One lamp per sensed channel, mirroring the pins above.
    const bezel = { x: x - 10, z0: 27, z1: 35 };
    out.push(L(loop([[bezel.x, face, bezel.z0], [x + 10, face, bezel.z0], [x + 10, face, bezel.z1], [bezel.x, face, bezel.z1]]), { tone: "mid" }));
    READ_CHANNELS.forEach((name, index) => {
      const cx = x - 8 + index * 4;
      out.push(L(k.sideRing([cx, face, 31], 1.5, "y", P, 20), { tone: "lo" }));
      out.push(`<path class="st-lamp" data-lamp="${name}" d="${k.sideRing([cx, face, 31], 1, "y", P, 16)}"/>`);
    });
    out.push(D([at([x - 10, face, 22]), at([x + 10, face, 22])], { size: 0.45 }));
  }
  return out.join("");
}

function dial() {
  const out = [];
  const [x, y] = DIAL;
  out.push(`<path class="iso-halo" d="${k.haloOf({ x: x - 8, y: y - 8, w: 16, d: 16, r: 8 }, 0, 3, P)}" style="filter:blur(4px)"/>`);
  out.push(M("ink", S(k.cylinder(x, y, 8, 0, 3, P, 32, 0.5), { tone: "mid" })));
  out.push(M("marble", S(k.cylinder(x, y, 2.6, 3, DIAL_Z - 3, P, 20), { tone: "mid" })));
  out.push(M("jade", S(k.cylinder(x, y, DIAL_R, DIAL_Z, DIAL_TOP - DIAL_Z, P, 64, 0.8), { tone: "hi", crease: "lo" }), L(k.knurl(x, y, DIAL_R, DIAL_TOP - 2.6, DIAL_TOP, 72, P, 0.3), { tone: "lo" })));
  out.push(`<path class="iso-fill" d="${k.ring(x, y, DIAL_R - 0.9, DIAL_TOP, P, 64)}" style="fill:var(--anatomy-face)"/>`);
  out.push(L(k.ring(x, y, DIAL_R - 2, DIAL_TOP, P, 64), { tone: "lo" }));
  const ticks = k.radialTicks(x, y, DIAL_R - 2.6, 50, 5, DIAL_TOP, [1.1, 2.6], P);
  out.push(L(ticks.minor, { tone: "lo" }), L(ticks.major, { tone: "mid" }));
  out.push(L(k.lineOnTop([x, y - (DIAL_R - 2)], [x, y - (DIAL_R - 6.4)], DIAL_TOP, P), { tone: "hi" }));
  out.push(L(k.ring(x, y, 1.4, DIAL_TOP, P, 16), { tone: "mid" }));
  return out.join("");
}

function kappaSwitch() {
  const out = [M("marble", S(k.slabOf(KAPPA, 0, KAPPA_H, P, 3, 0.5), { tone: "mid" }))];
  const slot = { x: KAPPA_STOPS.zero - 2, y: KAPPA.y + KAPPA.d / 2 - 1.2, w: KAPPA_STOPS.size - KAPPA_STOPS.zero + 4, d: 2.4, r: 1.2 };
  out.push(L(k.planOutline(slot, KAPPA_H, P, 4), { tone: "lo" }));
  out.push(D([KAPPA_STOPS.zero, KAPPA_STOPS.size].map((sx) => at([sx, KAPPA.y + 2.4, KAPPA_H])), { size: 0.5, tone: "mid" }));
  out.push(D([at([KAPPA.x + 2.4, KAPPA.y + 2.4, KAPPA_H]), at([KAPPA.x + KAPPA.w - 2.4, KAPPA.y + KAPPA.d - 2.4, KAPPA_H])], { size: 0.4 }));
  out.push(k.faceTextSvg(k.topMatrix([KAPPA.x + 3, KAPPA.y + KAPPA.d - 2.2], KAPPA_H, P), "κ", { size: 4, tone: "mid" }));
  return out.join("");
}

function kappaKnob() {
  const y = KAPPA.y + KAPPA.d / 2;
  return M("jade",
    S(k.cylinder(0, y, 1.2, KAPPA_H, 2, P, 16), { tone: "mid" }),
    S(k.cylinder(0, y, 3.2, KAPPA_H + 2, 4, P, 28), { tone: "hi" }),
    L(k.knurl(0, y, 3.2, KAPPA_H + 2, KAPPA_H + 6, 22, P), { tone: "lo" }),
  );
}

function dialWire() {
  const floor = 0.4;
  return k.wireSvg(at([EXEC_X - 6, 28, 5]), at([DIAL[0] + 4.6, DIAL[1] - 4.6, 3]), { via: [[EXEC_X - 6, 31, floor], [EXEC_X - 10, 40, floor], [DIAL[0] + 7, DIAL[1] - 7, floor]].map(at) });
}

// --- live drawing, shared by the build (first frame) and the page ---------

function treeLayout(tree, plan) {
  const nodes = [];
  let leaves = 0;
  const walk = (node, depth, parent) => {
    const index = nodes.length;
    nodes.push({ label: node[0], depth, parent, slot: 0 });
    const kids = node[1].map((child) => walk(child, depth + 1, index));
    nodes[index].slot = kids.length ? (nodes[kids[0]].slot + nodes[kids[kids.length - 1]].slot) / 2 : leaves++;
    return index;
  };
  walk(tree, 0, -1);
  return nodes.map((node) => ({ ...node, x: plan.x + plan.w / 2 + (node.slot - (leaves - 1) / 2) * 16, y: plan.y + 7 + node.depth * 9.5 }));
}

function boardPegs(kit, P, plan, z, tree, shown) {
  const nodes = treeLayout(tree, plan).slice(0, shown);
  const height = { a: 6, b: 10, c: 14 };
  const grooves = nodes.filter((node) => node.parent >= 0).map((node) => kit.lineOnTop([nodes[node.parent].x, nodes[node.parent].y], [node.x, node.y], z, P)).join("");
  const pegs = [...nodes].sort((a, b) => kit.depthOf([a.x, a.y, 0], P) - kit.depthOf([b.x, b.y, 0], P)).map((node) =>
    `<g data-mat="ink">${kit.solidSvg(kit.cylinder(node.x, node.y, 3.8, z, 0.8, P, 24), { tone: "lo" })}</g>` +
    `<g data-mat="marble">${kit.solidSvg(kit.cylinder(node.x, node.y, 2.7, z + 0.8, height[node.label], P, 20), { tone: node.parent < 0 ? "hi" : "mid" })}</g>` +
    kit.lineSvg(kit.ring(node.x, node.y, 1.2, z + 0.8 + height[node.label], P, 12), { tone: "lo" }));
  return (grooves ? kit.lineSvg(grooves, { tone: "hi" }) : "") + pegs.join("");
}

function holesOf(kit, P, rows, from, to) {
  // rows[i] is the hole list of tape row i; row i sits at local x = -i * PITCH.
  const out = { punched: [], map: [] };
  for (let i = from; i < to; i++) {
    const row = rows[((i % rows.length) + rows.length) % rows.length];
    for (const name of row) {
      const y = CH_Y[CHANNELS.indexOf(name)];
      const d = kit.ring(TAPE.from - i * PITCH, y, name === "feed" ? FEED_R : HOLE_R, TAPE_TOP + 0.05, P, 10);
      (name === "map" ? out.map : out.punched).push(d);
    }
  }
  return out;
}

const needleAt = (kit, P, turn) => {
  const angle = turn * Math.PI * 2;
  const [x, y] = DIAL;
  return kit.lineOnTop([x - Math.sin(angle) * 3, y + Math.cos(angle) * 3], [x + Math.sin(angle) * (DIAL_R - 3.4), y - Math.cos(angle) * (DIAL_R - 3.4)], DIAL_TOP + 0.2, P);
};

// The tape: every program followed by a blank leader just longer than the
// distance between the heads, so the read head finishes one program before the
// exec head starts the next and the readout can follow a single tree.
const GAP = Math.ceil((READ_X - EXEC_X) / PITCH) + 1;
function tapeSequence(data) {
  const rows = [], meta = [];
  data.forEach((entry, tree) => {
    let vars = 0;
    entry.rows.forEach((holes, index) => {
      rows.push(holes);
      const isVar = holes.includes("cost") && !holes.includes("bilinear");
      meta.push({ tree, index, cost: entry.cost[index], node: isVar ? vars++ : -1 });
    });
    for (let index = 0; index < GAP; index++) {
      rows.push([]);
      meta.push({ tree: -1 });
    }
  });
  return { rows, meta };
}

const DATA = { zero: figureData("zero"), size: figureData("size") };
const SEQ = { zero: tapeSequence(DATA.zero), size: tapeSequence(DATA.size) };
const N = SEQ.zero.rows.length;
const VISIBLE = Math.ceil((TAPE.to - TAPE.from) / PITCH) + 2;
const kitNames = ["lineOnTop", "depthOf", "solidSvg", "cylinder", "lineSvg", "ring", "translateAlong"];
const kitLocal = Object.fromEntries(kitNames.map((name) => [name, k[name]]));

// Resting state shown before the page runs and under reduced motion: T5 fully read.
const LAST = DATA.zero.length - 1;
const restRow = SEQ.zero.meta.findLastIndex((row) => row.tree === LAST);
const REST_S = restRow * PITCH + (READ_X - TAPE.from) + PITCH * 2;

function firstFrame() {
  const holes = holesOf(kitLocal, P, SEQ.zero.rows, -VISIBLE, N);
  const sized = holesOf(kitLocal, P, SEQ.size.rows, -VISIBLE, N);
  return {
    holes: L(holes.punched.join(""), { tone: "hi" }).replace("iso-line", "iso-line tape-hole"),
    map: L(sized.map.join(""), { tone: "hi" }).replace("iso-line", "iso-line tape-hole"),
    source: boardPegs(kitLocal, P, SRC_BOARD, BOARD_H, DATA.zero[LAST].tree, 99),
    read: boardPegs(kitLocal, P, READ_BOARD, BOARD_H, DATA.zero[LAST].tree, 99),
  };
}

const clipId = "st-tape-clip";

// The pegboards stand in front of the heads, so they are drawn after them: low as they are, from
// either side of the swing a peg can rise over a head's front cheek.
function composition() {
  const first = firstFrame();
  const tapeClip = loop([[TAPE.from, TAPE.y, TAPE_TOP], [TAPE.to, TAPE.y, TAPE_TOP], [TAPE.to, TAPE.y + TAPE.d, TAPE_TOP], [TAPE.from, TAPE.y + TAPE.d, TAPE_TOP]]);
  return [
    `<defs><clipPath id="${clipId}"><path d="${tapeClip}"/></clipPath></defs>`,
    plate(),
    bin(BIN_L, "left"),
    headBack(EXEC_X),
    headBack(READ_X),
    ...SHOES.map(shoe),
    tape(),
    ...SHOES.map(shoeFront),
    `<g clip-path="url(#${clipId})"><g data-part="holes" transform="${k.translateAlong(P, [REST_S, 0, 0])}">${first.holes}<g data-part="map">${first.map}</g></g></g>`,
    headFront(EXEC_X, "exec"),
    headFront(READ_X, "read"),
    bin(BIN_R, "right"),
    board(SRC_BOARD),
    `<g data-part="source">${first.source}</g>`,
    board(READ_BOARD),
    `<g data-part="read">${first.read}</g>`,
    dialWire(),
    dial(),
    `<path data-part="needle" class="iso-line" data-tone="hi" data-free="start" d="${needleAt(k, P, 0)}" style="stroke-width:1.1"/>`,
    kappaSwitch(),
    `<g data-part="knob" transform="${k.translateAlong(P, [KAPPA_STOPS.zero, 0, 0])}">${kappaKnob()}</g>`,
  ].join("");
}

const svg = k.figureSvg({
  width: WIDTH,
  height: HEIGHT,
  className: "st-svg",
  label:
    "A paper-tape reader on a bench. A pegboard on the left holds a rooted tree; its whole-tree program is punched on a tape that runs from a supply bin through two heads into a take-up bin. The first head executes the program: its counter totals the punched cost channel, and a wire takes the value to a dial. The second head only feels the holes with pins and rebuilds the tree on a second pegboard. With the constructor set to zero the dial reads 0 for every tree, while the tape and the rebuilt tree still differ tree by tree.",
  body: composition(),
});

const CSS = `
.st-svg{--st-hole:var(--anatomy-shade-0)}
.iso[data-theme="light"] .st-svg{--st-hole:var(--anatomy-mid)}
.st-svg .tape-hole{fill:var(--st-hole);stroke:var(--anatomy-hi);stroke-width:.4}
.st-svg [data-part="map"]{transition:opacity .4s var(--anatomy-ease)}
.st-svg .st-lamp{fill:var(--anatomy-shade-0);stroke:none}
.st-svg .st-lamp[data-on]{fill:var(--anatomy-hi)}
.iso-stage{outline:none;cursor:pointer;touch-action:pan-y}
${SWING_CSS}
@media (max-width:560px){.iso-plate:has(.st-svg){overflow:hidden}.st-svg.iso-svg{width:118%;max-width:none;margin:0 -9%}}
.iso-stage:focus-visible{box-shadow:0 0 0 1px var(--anatomy-mid)}
`;

const live = `
const P0 = ${JSON.stringify(P)};
let P = P0;
${shipped({ PLATE, PLATE_H, FOOT_H, TAPE_Z, TAPE_T, TAPE_TOP, TAPE, PITCH, CH_Y, HOLE_R, FEED_R, EXEC_X, READ_X, CHEEK_H, BRIDGE_H, SHOES, BIN_H, BIN_L, BIN_R, SRC_BOARD, READ_BOARD, BOARD_H, DIAL, DIAL_R, DIAL_Z, DIAL_TOP, PER_TURN, KAPPA, KAPPA_H, KAPPA_STOPS, CHANNELS, READ_CHANNELS, DATA, SEQ, N, VISIBLE, LAST, REST_S, FRAME, clipId })}
const PIN_Z = ${CHEEK_H + BRIDGE_H + 2};
const k = { ${Object.keys(k).join(", ")} };
const kit = k, kitLocal = k;
const at = (point) => k.iso(point, P);
const S = (paths, style) => k.solidSvg(paths, style);
const L = (d, style) => k.lineSvg(d, style);
const D = (points, style) => k.dotsSvg(points, style);
const M = ${M.toString()};
${shipped({ byDepth, loop, plate, board, bin, cheek, bridge, headBack, shoe, guide, shoeFront, tape, headFront, dial, kappaSwitch, kappaKnob, dialWire, treeLayout, boardPegs, holesOf, needleAt, firstFrame, composition })}
${swingSource}
const root = document.querySelector('[data-figure="source-tape"]');
const stage = root.querySelector(".iso-stage");
const part = (name) => stage.querySelector('[data-part="' + name + '"]');
// The live nodes, found again whenever a swing redraws the figure; the pins keep how far they had dropped.
let holes, mapHoles, source, readBoard, needle, knob, counter, payLamp, lamps, pins = [];
function bind() {
  holes = part("holes"); mapHoles = part("map"); source = part("source"); readBoard = part("read");
  needle = part("needle"); knob = part("knob"); counter = part("counter"); payLamp = part("pay");
  lamps = Object.fromEntries([...stage.querySelectorAll("[data-lamp]")].map((node) => [node.dataset.lamp, node]));
  const dropOf = Object.fromEntries(pins.map((pin) => [pin.name, pin.drop]));
  pins = [...stage.querySelectorAll("[data-pin]")].map((node) => ({ node, name: node.dataset.pin, drop: dropOf[node.dataset.pin] ?? 0 }));
}
bind();
let flash = 0, lastPaid = { tree: -1, paid: 0 };
const readout = root.querySelector("[data-readout]");
const still = matchMedia("(prefers-reduced-motion: reduce)");
const SPEED = 30; // tape units per second: five rows a second
const LEN = N * PITCH;
const mod = (value, size) => ((value % size) + size) % size;
let s = REST_S, target = null, kappa = "zero", knobX = KAPPA_STOPS.zero, value = 0;
let touring = !still.matches, visible = false, frame = 0, last = 0, idle = 0;
let shown = { source: "", read: "" };

// Index of the last row that has passed tape position x (rows run toward +x).
const passed = (x) => Math.floor((s - (x - TAPE.from)) / PITCH);
const metaAt = (i) => SEQ[kappa].meta[mod(i, N)];
function lastTree(i) {
  for (let j = i; j > i - N; j--) { const row = metaAt(j); if (row.tree >= 0) return { tree: row.tree, at: j - row.index }; }
  return { tree: 0, at: 0 };
}
function state() {
  const exec = lastTree(passed(EXEC_X));
  const read = lastTree(passed(READ_X));
  // The left board shows the tree whose program the exec head is running, so the
  // board, the counter and the readout always name the same tree.
  const src = exec;
  const paidUpTo = passed(EXEC_X) - exec.at;
  let paid = 0, nodes = 0;
  DATA[kappa][exec.tree].cost.forEach((c, index) => { if (index <= paidUpTo) paid += c; });
  const readUpTo = passed(READ_X) - read.at;
  DATA[kappa][read.tree].rows.forEach((row, index) => { if (index <= readUpTo && row.includes("cost") && !row.includes("bilinear")) nodes++; });
  return { exec, read, src, paid, nodes };
}
function draw(dt) {
  holes.setAttribute("transform", kit.translateAlong(P, [mod(s, LEN), 0, 0]));
  const now = state();
  const execEntry = DATA[kappa][now.exec.tree], readEntry = DATA[kappa][now.read.tree];
  const done = now.paid === execEntry.budget;
  const want = done ? execEntry.value : 0;
  value = still.matches || !dt ? want : value + (want - value) * (1 - Math.exp(-dt / 0.35));
  needle.setAttribute("d", needleAt(kit, P, value / PER_TURN));
  // The pay lamp flashes once for every cost hole the exec head takes.
  if (lastPaid.tree === now.exec.tree && now.paid > lastPaid.paid && dt) flash = 1;
  lastPaid = { tree: now.exec.tree, paid: now.paid };
  flash = still.matches ? 0 : flash * Math.exp(-(dt || 0) / 0.18);
  payLamp.style.opacity = flash.toFixed(3);
  const digits = String(now.paid).padStart(2, "0");
  if (counter.textContent !== digits) counter.textContent = digits;
  const srcKey = now.src.tree + "";
  if (shown.source !== srcKey) { source.innerHTML = boardPegs(kit, P, SRC_BOARD, BOARD_H, DATA[kappa][now.src.tree].tree, 99); shown.source = srcKey; }
  const readKey = now.read.tree + ":" + now.nodes;
  if (shown.read !== readKey) { readBoard.innerHTML = boardPegs(kit, P, READ_BOARD, BOARD_H, readEntry.tree, now.nodes); shown.read = readKey; }
  // Sensing pins drop into whatever hole is under the read head.
  const offset = s - (READ_X - TAPE.from);
  const i = Math.round(offset / PITCH);
  const near = Math.abs(offset - i * PITCH);
  const row = SEQ[kappa].rows[mod(i, N)];
  for (const pin of pins) {
    const want = row.includes(pin.name) && near < 1.4 ? 1.4 : 0;
    pin.drop = still.matches || !dt ? want : pin.drop + (want - pin.drop) * (1 - Math.exp(-dt / 0.05));
    pin.node.setAttribute("transform", kit.translateAlong(P, [0, 0, -pin.drop]));
    lamps[pin.name]?.toggleAttribute("data-on", pin.drop > 0.7);
  }
  knobX = still.matches || !dt ? KAPPA_STOPS[kappa] : knobX + (KAPPA_STOPS[kappa] - knobX) * (1 - Math.exp(-dt / 0.18));
  knob.setAttribute("transform", kit.translateAlong(P, [knobX, 0, 0]));
  mapHoles.style.opacity = kappa === "size" ? "1" : "0";
  // Report one tree: the one under the exec head. The read head reaches it later.
  const size = execEntry.rows.filter((r) => r.includes("cost") && !r.includes("bilinear")).length;
  const rebuilt = now.read.tree === now.exec.tree ? now.nodes : 0;
  const text = "T" + (now.exec.tree + 1) + " · paid " + now.paid + "/" + execEntry.budget + " · ev " + (done ? execEntry.value : "…") + " · read " + rebuilt + "/" + size;
  if (readout.textContent !== text) readout.textContent = text;
  stage.setAttribute("aria-valuenow", String(now.exec.tree + 1));
  stage.setAttribute("aria-valuetext", text);
}
function tick(time) {
  const dt = last ? Math.min((time - last) / 1000, 1 / 30) : 1 / 60;
  last = time;
  if (target !== null) {
    const step = Math.min(Math.abs(target - s), Math.max(SPEED, Math.abs(target - s) * 3) * dt);
    s += Math.sign(target - s) * step;
    if (Math.abs(target - s) < 0.01) { s = target; target = null; }
  } else if (touring) s += SPEED * dt;
  draw(dt);
  frame = visible ? requestAnimationFrame(tick) : 0;
}
const run = () => { if (!frame && visible && !still.matches) { last = 0; frame = requestAnimationFrame(tick); } };
// Rest a tree just after its last row has crossed the read head.
const restOf = (tree) => {
  const end = SEQ[kappa].meta.findLastIndex((row) => row.tree === tree);
  const base = end * PITCH + (READ_X - TAPE.from) + PITCH * 2;
  return base + Math.round((s - base) / LEN) * LEN;
};
const settleIdle = () => { clearTimeout(idle); idle = setTimeout(() => { touring = !still.matches; run(); }, 6000); };
function choose(tree) {
  touring = false;
  target = restOf(tree);
  if (target < s - LEN / 2) target += LEN;
  if (still.matches) { s = target; target = null; draw(0); }
  settleIdle(); run();
}
function flip() {
  kappa = kappa === "zero" ? "size" : "zero";
  shown = { source: "", read: "" };
  if (still.matches) draw(0);
  settleIdle(); run();
}
stage.addEventListener("keydown", (event) => {
  const current = state().exec.tree, count = DATA.zero.length;
  if (event.key === "ArrowRight") choose((current + 1) % count);
  else if (event.key === "ArrowLeft") choose((current + count - 1) % count);
  else if (/^[1-9]$/.test(event.key) && +event.key <= count) choose(+event.key - 1);
  else if (event.key === "k" || event.key === "K" || event.key === " ") flip();
  else return;
  event.preventDefault();
});
stage.addEventListener("click", flip);
new IntersectionObserver((entries) => { visible = entries[entries.length - 1].isIntersecting; if (visible) run(); }, { rootMargin: "120px 0px" }).observe(stage);
draw(0);
// A sideways drag swings the view (../swing.mjs): the bench is redrawn from there, then the moving parts
// are painted again where they were (a draw with no time passing).
const svg = stage.querySelector("svg");
const hold = () => { touring = false; settleIdle(); };
mountSwing(stage, { onHold: hold, onSwing: (angle) => {
  P = swingOf(iso, P0, FRAME, angle);
  svg.innerHTML = composition();
  bind();
  shown = { source: "", read: "" };
  draw(1e-6);
} });
`;

const COPY = {
  en: {
    title: "Whole-tree program",
    hint: "Drag: look round · click: flip constructor · ← →: tree",
    keys: ["The tape: prog κ(T), the source", "Pegboards: T on the left, read(prog T) on the right; peg height is the root label a, b, c", "Dial: the reading ev = fold κ(T)"],
    refs: ["Theorem 3.9"],
    caption: [
      "A paper-tape reader: each tree’s whole-tree program is punched on a tape, and two heads read it.",
      "The punching rule: one row per syntax node, and a cost hole on every variable and bilinear node. The first head totals the cost holes, r(prog T) = β(T) = 2, 5, 8, 11, 14, fixed by the tree’s shape alone.",
      "With κ ≡ 0 the dial reads 0 for every tree. The second head never evaluates: its pins skip the map channel, and it still rebuilds each tree exactly.",
      "Flip κ to count nodes, and only the map channel and the dial change.",
    ],
    aria: "Paper-tape reader: arrow keys choose a tree, K flips the constructor",
  },
  zh: {
    title: "整树程序",
    hint: "拖动侧看 · 点击切换构造子 · ← → 换树",
    keys: ["纸带：源程序 prog κ(T)", "钉板：左为 T，右为 read(prog T)；钉高即根标签 a、b、c", "表盘：读数 ev = fold κ(T)"],
    refs: ["定理 3.9"],
    caption: [
      "一台纸带读带机：每棵树的整树程序打在一条纸带上，两只读头各读一遍。",
      "打孔规则是：每个语法节点一行，变量与双线性节点各打一个计费孔。第一读头累计计费孔，r(prog T) = β(T) = 2、5、8、11、14，只由树形决定。",
      "κ ≡ 0 时，表盘对每棵树都读 0。第二读头从不求值，探针跳过映射通道，照样逐棵重建原树。",
      "把 κ 切到节点计数，改变的只有映射通道和表盘。",
    ],
    aria: "纸带读带机：方向键选树，K 切换构造子",
  },
};
const restNodes = SEQ.zero.meta.filter((row) => row.tree === LAST && row.node >= 0).length;
const restReadout = `T5 · paid ${DATA.zero[LAST].budget}/${DATA.zero[LAST].budget} · ev ${DATA.zero[LAST].value} · read ${restNodes}/${restNodes}`;
const bodyOf = (lang) => {
  const copy = COPY[lang];
  return `<div data-figure="source-tape">${k.plateHtml({
    fig: "Fig 3.9",
    title: copy.title,
    hint: copy.hint,
    readout: restReadout,
    keys: [
      { mark: "lit", label: copy.keys[0] },
      { mark: "raised", label: copy.keys[1] },
      { mark: "dim", label: copy.keys[2] },
    ],
    caption: copy.caption,
    refs: copy.refs,
    body: `<div class="iso-stage" tabindex="0" role="slider" aria-label="${copy.aria}" aria-valuemin="1" aria-valuemax="${DATA.zero.length}" aria-valuenow="${DATA.zero.length}">${svg}</div>`,
  })}</div>`;
};

const kitSource = readFileSync(join(HERE, "../kit/iso-kit.mjs"), "utf8").replace(/^export /gm, "");
if (fragment) {
  const outDir = join(HERE, "../../src/generated");
  mkdirSync(outDir, { recursive: true });
  writeFileSync(join(outDir, "source-tape.json"), JSON.stringify({ html: { zh: bodyOf("zh"), en: bodyOf("en") }, css: CSS, script: `{\n${kitSource}\n${live}\n}`.replace(/<\/(script)/gi, "<\\/$1") }));
  console.log("wrote src/generated/source-tape.json");
} else {
  mkdirSync(join(HERE, "out"), { recursive: true });
  const name = theme === "light" ? "source-tape-light.html" : "source-tape.html";
  writeFileSync(join(HERE, "out", name), k.pageHtml({ title: "Whole-tree program", theme, body: `<style>${CSS}</style>${bodyOf("en")}`, script: kitSource + live, width: 700 }));
  console.log("wrote out/" + name);
}
