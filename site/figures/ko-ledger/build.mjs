// Fig: a goban and its superko ledger (§1.1, Example 2.3, Lemma 3.2; GO2).
// Two legal openings, γ1 (5 plies) and γ2 (7 plies), reach one visible corner. The ledger in front of
// the board keeps one tile for every board the game has shown: a set, so a pass that repeats a board
// adds nothing. To test W(0,0), the carriage carries the board that move would leave, B*, along the
// ledger. After γ2 it finds B* and the stop pin rises on A19; after γ1 there is no such tile and the
// point is open: 357 legal ports against 356, on the same board.
//   bun build.mjs [--light]   → out/ko-ledger[-light].html (standalone, for checks)
//   bun build.mjs --fragment  → ../../src/generated/ko-ledger.json (for the site)
import { mkdirSync, readFileSync, writeFileSync } from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";
import * as k from "../kit/iso-kit.mjs";
import * as G from "../kit/lathe.mjs";
import { BLACK, GAMMA, KO, N, WHITE, after, cornerOf, keyOf, pointOf, portsOf, replay } from "./model.mjs";
import { paperFigureCss, paperFigureSource, paperPlate } from "../paper-figure.mjs";
import { shipped, swingSource } from "../swing.mjs";

const HERE = dirname(fileURLToPath(import.meta.url));
const theme = process.argv.includes("--light") ? "light" : "dark";
const fragment = process.argv.includes("--fragment");

const WIDTH = 640;
const HEIGHT = 460;

// --- the two histories, worked out here and shipped as data ---------------------------------
// Each ply: the stones on the corner after it, the tile it files (or the tile it repeats), what it
// captured, and the ports of the side to move afterwards.
const STONES = (board) => board.flatMap((c, p) => (c ? [[Math.floor(p / N), p % N, c]] : []));
const HISTORIES = GAMMA.map((moves) => {
  const game = replay(moves);
  const tiles = [{ key: keyOf(game.history[0].board), corner: cornerOf(game.history[0].board) }];
  const plies = game.plies.map((ply, i) => {
    const key = keyOf(ply.board);
    let slot = tiles.findIndex((t) => t.key === key);
    if (ply.fresh) { tiles.push({ key, corner: cornerOf(ply.board) }); slot = tiles.length - 1; }
    return { colour: ply.colour, move: ply.move, stones: STONES(ply.board), captured: ply.captured.map((p) => [Math.floor(p / N), p % N]), slot, fresh: ply.fresh, ports: portsOf({ ...ply, history: game.history.slice(0, i + 2) }) };
  });
  const star = after(game.board, WHITE, pointOf(...KO)).board;
  const match = tiles.findIndex((t) => t.key === keyOf(star));
  return { plies, tiles: tiles.map((t) => t.corner), match, star: cornerOf(star) };
});
const PORTS0 = 362; // empty board, Black to move: 361 points and pass

// World: x and y on the floor, z up; the mat's top is z = 0. Board point (r, j) sits at
// (GX − SP·j, GY − SP·r): A19 = (0, 0) is the corner nearest the viewer.
const C = {
  MAT: { x: -58, y: -54, w: 140, d: 134, r: 2 },
  MAT_H: 3,
  BOARD: { x: -43, y: -45.5, w: 86, d: 91, r: 1, z: 11.2, h: 11.8 },
  SP: 4.2,
  GX: 37.8,
  GY: 37.8,
  LEGS: 12, // inset of the legs from the board's corners
  TRAY: { x: -52, y: 54, w: 104, d: 15, h: 2.4, pitch: 12.6, tile: 10.6, first: -44 },
  RAIL: { y: 71, d: 3.4, h: 2.2 },
  CARRIAGE: { park: 54, travelZ: 9.4, matchZ: 5.7 },
  COUNTER: { x: 57, y: 52, w: 15, d: 12, h: 10 },
  BOWLS: { white: [64, -16], black: [66, 14], lid: [70, 36], r: 9.6 },
};
const PX = (j) => C.GX - C.SP * j;
const PY = (r) => C.GY - C.SP * r;
const TOP = C.BOARD.z + C.BOARD.h;
const slotX = (i) => C.TRAY.first + i * C.TRAY.pitch;
const TILE_Y = C.TRAY.y + C.TRAY.d / 2;

const FIT = [...k.boxCorners(C.MAT, -C.MAT_H, 0), [C.BOARD.x, C.BOARD.y, TOP + 2], [C.BOWLS.white[0], C.BOWLS.white[1] - 10, 14]];
const VIEW = { pad: 20, azimuth: 52, elevation: 36 };
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
const byDepth = (items, key) => [...items].sort((a, b) => depthAt(...key(a)) - depthAt(...key(b)));
const UP = [0, 0, 1];
const n2 = (v) => (Math.round(v * 100) / 100).toString();
const upright = (key, x, y, z, draw) => {
  if (!upright.parts) upright.parts = new Map();
  if (!upright.parts.has(key)) upright.parts.set(key, draw({ ...P0, origin: [0, 0] }));
  const [dx, dy] = at([x, y, z]), scale = P.scale / P0.scale;
  return `<g transform="translate(${n2(dx)} ${n2(dy)}) scale(${scale})">${upright.parts.get(key)}</g>`;
};

// A go stone: a lens turned about the vertical, standing on z. Black is ink, white is shell.
const LENS = [[0, 0.5], [0.12, 1.2, 1], [0.38, 1.7, 1], [0.75, 1.98, 1], [1.12, 1.7, 1], [1.38, 1.2, 1], [1.5, 0.5]];
function stoneSvg(x, y, z, colour) {
  return upright("stone-" + colour, x, y, z, (camera) => {
    const F = G.frameAlong([0, 0, 0], UP);
    return M(colour === 1 ? "ink" : "marble", S(G.solidOf(LENS, F, camera, { steps: 26 }), { tone: "hi", crease: "none" }));
  });
}
// Transient stones share the board's depth order while they land or are removed.
function stonesSvg(stones, drop, removing) {
  const current = stones.map(([r, j, c]) => ({ r, j, c, lift: 0, fade: 1 }));
  if (drop) current.push(drop);
  if (removing) current.push(...removing);
  return byDepth(current, ({ r, j, lift }) => [PX(j), PY(r), TOP + lift]).map(({ r, j, c, lift, fade }) => {
    const svg = stoneSvg(PX(j), PY(r), TOP + lift, c);
    return fade === 1 ? svg : `<g opacity="${n2(fade)}">${svg}</g>`;
  }).join("");
}

// A ledger tile: the 3 × 3 corner of one board, as a small marble plaque with its own lines and stones.
function tileSvg(x, y, z, corner, style = {}) {
  const t = C.TRAY.tile, h = 1.1, plan = { x: x - t / 2, y: y - t / 2, w: t, d: t, r: 0.6 }, g = 3.1;
  // The tile's corner (0,0) is its near (+x, +y) corner, as on the board.
  // The board's edge is the first line on the near sides; the lines run on to the tile's far edges.
  const px = (j) => x + g - g * j, py = (r) => y + g - g * r, edge = t / 2;
  const lines = [0, 1, 2].map((i) => k.lineOnTop([px(i), py(0)], [px(i), y - edge], z + h, P) + k.lineOnTop([px(0), py(i)], [x - edge, py(i)], z + h, P)).join("");
  const black = [], white = [];
  corner.forEach((row, r) => row.forEach((c, j) => { if (c === 1) black.push(at([px(j), py(r), z + h])); else if (c === 2) white.push([px(j), py(r)]); }));
  return M("marble", S(k.slabOf(plan, z, h, P, 2, 0.3), { tone: "hi", ...style }), L(lines, { tone: "mid" }),
    white.map(([wx, wy]) => `<path class="iso-fill" d="${k.ring(wx, wy, 1.35, z + h, P, 18)}"/>` + L(k.ring(wx, wy, 1.35, z + h, P, 18), { tone: "hi" })).join(""),
    black.map(([cx, cy]) => `<circle cx="${n2(cx)}" cy="${n2(cy)}" r="${n2(P.scale * 1.45)}" class="ko-tile-stone"/>`).join(""));
}

// The tiles filed so far; `merging` is a repeated board's tile settling onto its twin.
function ledgerSvg(tiles, count, arriving, merging, lit) {
  const out = [];
  for (let i = 0; i < count; i++) {
    const z = C.TRAY.h + (i === count - 1 && arriving ? arriving.lift : 0);
    const svg = tileSvg(slotX(i), TILE_Y, z, tiles[i], lit === i ? { lit: true } : {});
    out.push(i === count - 1 && arriving && arriving.fade < 1 ? `<g opacity="${n2(arriving.fade)}">${svg}</g>` : svg);
  }
  if (merging) out.push(`<g opacity="${n2(merging.fade)}">${tileSvg(slotX(merging.slot), TILE_Y, C.TRAY.h + merging.lift, tiles[merging.slot])}</g>`);
  return out.join("");
}

// The carriage runs on the front rail. At a match the tile lowers onto the same x and y as the filed board.
function carriageSvg(x, z, star, found) {
  const r = C.RAIL, top = r.h + 5.2, ty = TILE_Y - 2.2, armZ = 14.4;
  const arm = { x: x - 1.4, y: ty - 1.4, w: 2.8, d: r.y + r.d / 2 - ty + 1.4, r: 0.5 };
  const body = { x: x - 4.4, y: r.y - 1.2, w: 8.8, d: r.d + 2.4, r: 1 };
  return tileSvg(x, TILE_Y, z, star, { lit: found }) +
    M("jade", S(k.slabOf(body, r.h, 5.2, P, 3, 0.5), { tone: "hi", inner: L(k.sideSeam(body, r.h + 1.6, P, 3), { tone: "faint" }) }), D([at([x - 2.8, r.y + r.d / 2, top]), at([x + 2.8, r.y + r.d / 2, top])], { size: 0.42 })) +
    M("ink", S(k.cylinder(x, r.y + r.d / 2, 1.2, top, armZ - top, P, 14), { tone: "mid" }), S(k.cylinder(x, ty, 0.7, z + 1.1, armZ - z - 1.1, P, 10), { tone: "mid", crease: "none" }), S(k.slabOf(arm, armZ, 1.4, P, 2, 0.3), { tone: "mid" }));
}

// The verdict at A19: an open point shows the stone that could go there; a blocked one raises the pin.
function verdictSvg(state, amount) {
  if (!state || amount < 0.02) return "";
  const x = PX(KO[1]), y = PY(KO[0]);
  if (state === "open") return `<g opacity="${n2(amount)}">${M("jade", S(k.cylinder(x, y, 2.5, TOP, 0.35, P, 28), { tone: "hi", crease: "none" }), L(k.ring(x, y, 1.6, TOP + 0.35, P, 20), { tone: "mid" }))}</g><g opacity="${n2(0.55 * amount)}">${stoneSvg(x, y, TOP + 0.35, 2)}</g>`;
  const up = 5 * amount;
  return M("cinnabar", S(k.cylinder(x, y, 1.7, TOP, 0.5, P, 20), { tone: "mid" }), S(k.cylinder(x, y, 0.6, TOP + 0.5, up, P, 12), { tone: "hi", crease: "none" }), S(k.cylinder(x, y, 1.2, TOP + 0.5 + up, 1, P, 16, 0.3), { tone: "hi" }));
}

// The port counter: three drums behind windows on its front face.
function counterSvg(value) {
  const c = C.COUNTER, face = c.y + c.d, digits = String(value).padStart(3, " ").split("");
  const plan = { x: c.x, y: c.y, w: c.w, d: c.d, r: 1.2 };
  const windows = digits.map((digit, i) => {
    const x0 = c.x + 1.5 + i * 4.1, win = [[x0, face, 2.7], [x0 + 3.8, face, 2.7], [x0 + 3.8, face, 7.8], [x0, face, 7.8]].map(at);
    const outline = k.pathOf(win, true), id = "ko-counter-" + i;
    const text = k.faceTextSvg(k.sideMatrix([x0 + 1.9, face], 3.65, P, "left"), digit, { size: 3.9, tone: "hi", anchor: "middle" });
    return `<clipPath id="${id}"><path d="${outline}"/></clipPath><path class="iso-fill" d="${outline}"/><g clip-path="url(#${id})">${text}</g>` + L(outline, { tone: "mid" });
  });
  return M("jade", S(k.slabOf(plan, 0, c.h, P, 3, 0.5), { tone: "hi", inner: L(k.sideSeam(plan, 1.6, P, 3), { tone: "faint" }) }), D(k.corners(plan, 1.6).map(([x, y]) => at([x, y, c.h])), { size: 0.45 })) +
    M("marble", windows.join(""));
}

// --- static art ------------------------------------------------------------------------------

// A tatami mat: a straw field with its weave running along x, and the dark cloth border (heri) on the
// long edges.
function mat() {
  const m = C.MAT, out = [`<path class="iso-halo" d="${k.haloOf(m, -C.MAT_H, C.MAT_H, P)}"/>`];
  const heri = 5;
  const weave = [];
  for (let y = m.y + heri + 2; y < m.y + m.d - heri - 1; y += 2.4) weave.push(k.lineOnTop([m.x, y], [m.x + m.w, y], 0, P));
  out.push(M("marble", S(k.slabOf(m, -C.MAT_H, C.MAT_H, P, 2, 0.6), { tone: "mid", inner: L(k.sideSeam(m, -1.4, P, 2), { tone: "faint" }) }), L(weave.join(""), { tone: "faint" })));
  for (const y of [m.y, m.y + m.d - heri]) out.push(M("ink", S(k.slabOf({ x: m.x, y, w: m.w, d: heri, r: 0.4 }, -0.01, 0.31, P, 2), { tone: "mid", crease: "none" }), L(k.lineOnTop([m.x, y + 1.2], [m.x + m.w, y + 1.2], 0.3, P) + k.lineOnTop([m.x, y + heri - 1.2], [m.x + m.w, y + heri - 1.2], 0.3, P), { tone: "lo" })));
  return out.join("");
}

// The legs: turned kuchinashi feet under the board's corners.
const LEG = [[0, 2.8], [0.8, 3.4, 1], [2.6, 4.3, 1], [4.8, 4.5, 1], [6.8, 3.7, 1], [8.2, 2.6, 1], [9, 2.4]];
function legSvg(x, y) {
  return upright("leg", x, y, 0, (camera) => M("ink", S(G.solidOf(LEG.map(([z, r, smooth]) => [z * C.BOARD.z / 9, r, smooth]), G.frameAlong([0, 0, 0], UP), camera, { steps: 40 }), { tone: "mid", crease: "none" })));
}
function boardSvg() {
  const b = C.BOARD, plan = { x: b.x, y: b.y, w: b.w, d: b.d, r: b.r };
  const lines = [];
  for (let i = 0; i < N; i++) {
    lines.push(k.lineOnTop([PX(i), PY(0)], [PX(i), PY(N - 1)], TOP, P));
    lines.push(k.lineOnTop([PX(0), PY(i)], [PX(N - 1), PY(i)], TOP, P));
  }
  const hoshi = [3, 9, 15].flatMap((r) => [3, 9, 15].map((j) => at([PX(j), PY(r), TOP])));
  return M("ink", S(k.slabOf(plan, b.z, 2.1, P, 3, 0.5), { tone: "mid" }))
    + M("marble", S(k.slabOf(plan, b.z + 2.1, b.h - 2.1, P, 3, 0.8), { tone: "hi", inner: L(k.sideSeam(plan, b.z + 4.1, P, 3), { tone: "faint" }) }),
    L(lines.join(""), { tone: "mid" }), D(hoshi, { size: 0.85, tone: "hi" }),
    k.faceTextSvg(k.topMatrix([PX(0) - 0.8, PY(0) + 4.9], TOP, P), "A19", { size: 2.8, tone: "hi", anchor: "middle" }));
}

// A go-ke: a squat turned bowl. `open` shows the stones inside instead of the lid.
const BOWL = [[0, 5.2], [0.8, 6.4, 1], [2.6, 8.6, 1], [5, 9.6, 1], [7.4, 9.1, 1], [9, 7.8]];
const LID = [[0, 7.9], [0.9, 8.4, 1], [2, 7.2, 1], [2.6, 4.8, 1], [2.8, 0]];
function bowlSvg([x, y], colour, open) {
  const mat = colour === 1 ? "jade" : "marble";
  const out = [upright("bowl-" + mat, x, y, 0, (camera) => M(mat, S(G.solidOf(BOWL, G.frameAlong([0, 0, 0], UP), camera, { steps: 60 }), { tone: "mid", crease: "none" })))];
  if (open) {
    const rim = G.frameOf([x, y, 9], UP, [1, 0, 0], [0, 1, 0]);
    out.push(M(mat, `<path class="iso-fill" d="${G.circleOf(rim, 0, 7.6, P)}" style="fill:var(--anatomy-shade-0)"/>`, L(G.circleOf(rim, 0, 7.8, P), { tone: "lo" })));
    const inside = [[-2.6, -2], [1.4, -3], [3.6, 0.6], [-0.8, 1.4], [-3.8, 2.2], [2, 3.6], [0.6, -0.4]];
    for (const [dx, dy] of byDepth(inside, ([dx, dy]) => [x + dx, y + dy, 8])) out.push(stoneSvg(x + dx, y + dy, 7.6, colour));
  } else out.push(upright("bowl-lid-" + mat, x, y, 9, (camera) => M(mat, S(G.solidOf(LID, G.frameAlong([0, 0, 0], UP), camera, { steps: 56 }), { tone: "hi", crease: "none" }))));
  return out.join("");
}
// The black player's lid, upside down beside the bowl: it keeps the stones Black has captured.
function lidSvg(prisoners) {
  const [x, y] = C.BOWLS.lid;
  const dish = [[0, 4.4], [0.4, 6.6, 1], [1.6, 8, 1], [2.6, 8.4]];
  const out = [upright("prisoners-lid", x, y, 0, (camera) => {
    const F = G.frameAlong([0, 0, 0], UP);
    return M("jade", S(G.solidOf(dish, F, camera, { steps: 52 }), { tone: "mid", crease: "none" }), `<path class="iso-fill" d="${G.circleOf(F, 2.6, 7.2, camera)}" style="fill:var(--anatomy-shade-1)"/>`, L(G.circleOf(F, 2.6, 7.4, camera), { tone: "lo" }));
  })];
  const spots = [[-1.2, 0.6], [2.2, -1.4]];
  for (let i = 0; i < prisoners.count; i++) out.push(`<g opacity="${n2(i === prisoners.count - 1 ? prisoners.fade : 1)}">${stoneSvg(x + spots[i][0], y + spots[i][1], 1.2, 2)}</g>`);
  return out.join("");
}

function traySvg() {
  const t = C.TRAY, plan = { x: t.x, y: t.y, w: t.w, d: t.d, r: 1.6 };
  const slots = Array.from({ length: 7 }, (_, i) => k.planOutline({ x: slotX(i) - t.tile / 2 - 0.6, y: TILE_Y - t.tile / 2 - 0.6, w: t.tile + 1.2, d: t.tile + 1.2, r: 0.8 }, t.h, P, 2)).join("");
  const labels = Array.from({ length: 7 }, (_, i) => k.faceTextSvg(k.topMatrix([slotX(i), t.y + t.d - 0.45], t.h, P), String(i + 1), { size: 2.25, anchor: "middle", tone: "hi" })).join("");
  return M("jade", S(k.slabOf(plan, 0, t.h, P, 4, 0.5), { tone: "hi", inner: L(k.sideSeam(plan, 0.9, P, 4), { tone: "faint" }) }), L(k.planOutline(k.insetPlan(plan, .55), t.h, P, 4), { className: "polished-edge" }), L(slots, { tone: "lo" }), labels);
}
function railSvg() {
  const r = C.RAIL, x0 = C.TRAY.x - 2, x1 = C.CARRIAGE.park + 6, plan = { x: x0, y: r.y, w: x1 - x0, d: r.d, r: 0.8 };
  return M("ink", S(k.slabOf(plan, 0, r.h, P, 2, 0.4), { tone: "mid" }), L(k.lineOnTop([x0, r.y + r.d / 2], [x1, r.y + r.d / 2], r.h, P), { tone: "faint" })) +
    [x0 + 1.4, x1 - 1.4].map((x) => M("jade", S(k.slabOf({ x: x - 1.4, y: r.y - 0.6, w: 2.8, d: r.d + 1.2, r: 0.5 }, r.h, 2, P, 2, 0.3), { tone: "mid" }))).join("");
}

// The whole drawing at a view of the game.
function composition(view) {
  const legs = k.corners(C.BOARD, C.LEGS);
  const h = HISTORIES[view.history];
  const back = byDepth(legs, ([x, y]) => [x, y]);
  return [
    mat(),
    ...back.slice(0, 2).map(([x, y]) => legSvg(x, y)),
    `<path class="iso-halo" d="${k.haloOf(C.BOARD, 0, 2, P)}" style="opacity:calc(var(--anatomy-halo-opacity) * .7)"/>`,
    ...back.slice(2).map(([x, y]) => legSvg(x, y)),
    boardSvg(),
    `<g data-part="stones">${stonesSvg(view.stones, view.drop, view.removing)}</g>`,
    `<g data-part="verdict">${verdictSvg(view.verdict, view.verdictAmount)}</g>`,
    bowlSvg(C.BOWLS.white, 2, false),
    bowlSvg(C.BOWLS.black, 1, true),
    `<g data-part="lid">${lidSvg(view.prisoners)}</g>`,
    traySvg(),
    `<g data-part="ledger">${ledgerSvg(h.tiles, view.tiles, view.arriving, view.merging, view.lit)}</g>`,
    railSvg(),
    `<g data-part="carriage">${carriageSvg(view.carriage, view.tileZ, h.star, view.lit >= 0)}</g>`,
    `<g data-part="counter">${counterSvg(view.ports)}</g>`,
  ].join("");
}

// The settled view after `history` has been played in full and W(0,0) tested.
function finalView(history) {
  const h = HISTORIES[history], last = h.plies[h.plies.length - 1];
  return {
    history,
    stones: last.stones,
    drop: null,
    removing: null,
    tiles: h.tiles.length,
    arriving: null,
    merging: null,
    prisoners: { count: h.plies.reduce((n, p) => n + p.captured.length, 0), fade: 1 },
    carriage: h.match >= 0 ? slotX(h.match) : slotX(0),
    tileZ: h.match >= 0 ? C.CARRIAGE.matchZ : C.CARRIAGE.travelZ,
    lit: h.match,
    verdict: h.match >= 0 ? "blocked" : "open",
    verdictAmount: 1,
    ports: last.ports,
  };
}
const NAMES = ["γ₁", "γ₂"];
function readoutOf(history, lang) {
  const h = HISTORIES[history], last = h.plies[h.plies.length - 1], blocked = h.match >= 0;
  const zh = lang === "zh";
  return NAMES[history] + " · " + h.tiles.length + (zh ? " 个盘面 · A19 " : " boards · A19 ") + (blocked ? (zh ? "禁着" : "blocked") : (zh ? "可下" : "legal")) + " · " + last.ports + (zh ? " 个合法着" : " legal moves");
}
const REST = finalView(1);
const art = composition(REST);
const CSS = `${paperFigureCss}
.ko-tile-stone { fill: var(--anatomy-hi); }
.iso[data-theme="dark"] .ko-tile-stone { fill: #151717; stroke: var(--anatomy-mid); stroke-width: .4; }
`;

const strip = (file) => readFileSync(join(HERE, file), "utf8").replace(/^export /gm, "");
const kitSource = strip("../kit/iso-kit.mjs");
const latheSource = `const LATHE = (() => {\n${strip("../kit/lathe.mjs").replace(/^import .*$/gm, "")}\nreturn { ${Object.keys(G).join(", ")} };\n})();`;
const live = `
const P0 = ${JSON.stringify(P0)};
let P = P0;
${shipped({ C, HISTORIES, KO, N, TOP, TILE_Y, PORTS0, FRAME, NAMES })}
const k = { ${Object.keys(k).join(", ")} };
const G = LATHE;
${shipped({ PX, PY, slotX, at, S, L, D, M, depthAt, byDepth, UP, n2, upright, LENS, stoneSvg, stonesSvg, tileSvg, ledgerSvg, carriageSvg, verdictSvg, counterSvg, mat, LEG, legSvg, boardSvg, BOWL, LID, bowlSvg, lidSvg, traySvg, railSvg, composition, finalView, readoutOf })}
${swingSource}
${paperFigureSource}
const root = document.querySelector('[data-figure="ko-ledger"]');
const lang = root.lang;
const stage = root.querySelector(".iso-stage");
const svgEl = stage.querySelector("svg");
const paintPart = partPainter(stage);
const readout = root.querySelector("[data-readout]");
const buttons = [...root.querySelectorAll("[data-history]")];
const still = matchMedia("(prefers-reduced-motion: reduce)");
let view = finalView(1);
let beats = [], beat = 0, clock = 0, tourClock = 0, touring = !still.matches;
const PLY = 0.72, SCAN = 0.21;

function say(text) {
  if (readout.textContent !== text) readout.textContent = text;
}
function select(history) {
  for (const button of buttons) button.setAttribute("aria-pressed", String(Number(button.dataset.history) === history));
}
function settle() {
  view = finalView(view.history);
  beats = [];
  beat = 0;
  tourClock = 0;
  paint();
  say(readoutOf(view.history, lang));
}
function play(history) {
  const h = HISTORIES[history];
  select(history);
  view = { history, stones: [], drop: null, removing: null, tiles: 1, arriving: null, merging: null, prisoners: { count: 0, fade: 1 }, carriage: C.CARRIAGE.park, tileZ: C.CARRIAGE.travelZ, lit: -1, verdict: null, verdictAmount: 0, ports: PORTS0 };
  if (still.matches) { settle(); return; }
  const stop = h.match >= 0 ? h.match : 0;
  beats = [
    ...h.plies.map((ply, index) => ({ length: PLY, ply, index })),
    { length: SCAN * (Math.round((C.CARRIAGE.park - slotX(stop)) / C.TRAY.pitch) + 1), scan: slotX(stop) },
    { length: 0.58, verdict: h.match >= 0 ? "blocked" : "open" },
  ];
  beat = 0; clock = 0; beatText = -1;
  say(NAMES[history] + " · " + root.dataset.start);
  paint();
  run();
}
const ease = (t) => (t <= 0 ? 0 : t >= 1 ? 1 : t * t * (3 - 2 * t));
function apply(step, t) {
  if (step.ply) {
    const { ply } = step, u = ease(t / 0.36);
    const prior = HISTORIES[view.history].plies[step.index - 1];
    const zh = lang === "zh", move = ply.move === "pass" ? (zh ? "虚着" : "Pass") : "ABCDEFGHJKLMNOPQRST"[ply.move[1]] + (N - ply.move[0]);
    const side = ply.colour === 1 ? (zh ? "黑" : "Black") : (zh ? "白" : "White");
    const count = step.index + 1;
    if (beatText !== beat) {
      say(NAMES[view.history] + " · " + (zh ? "第 " + count + " 手" : "Move " + count) + " · " + side + " " + move + (ply.move === "pass" ? (zh ? " · 盘面集合不变" : " · board already filed") : ""));
      beatText = beat;
    }
    if (ply.move === "pass") {
      view.stones = prior ? prior.stones : [];
      view.drop = null;
      view.merging = t < 0.57 ? { slot: ply.slot, lift: 6 - 4.65 * u, fade: Math.min(1, u * 3) * (1 - ease((t - 0.29) / 0.28)) } : null;
    } else {
      const [r, j] = ply.move;
      view.stones = u < 1 ? (prior?.stones ?? []) : ply.stones;
      view.drop = u < 1 ? { r, j, c: ply.colour, lift: 9 * (1 - u), fade: Math.min(1, u * 3) } : null;
      const out = ease((t - 0.36) / 0.16);
      view.removing = ply.captured.length && u === 1 && out < 1
        ? ply.captured.map(([r, j]) => ({ r, j, c: ply.colour === 1 ? 2 : 1, lift: 3 * out, fade: 1 - out })) : null;
      if (ply.captured.length) view.prisoners = { count: ply.captured.length, fade: ease((t - 0.45) / 0.22) };
      if (ply.fresh && t >= 0.36) {
        const filing = ease((t - 0.36) / 0.36);
        view.tiles = ply.slot + 1;
        view.arriving = filing < 1 ? { lift: 5 * (1 - filing), fade: Math.min(1, filing * 3) } : null;
      }
    }
    if (t >= 0.52) view.ports = ply.ports;
  } else if (step.scan !== undefined) {
    if (beatText !== beat) { say(NAMES[view.history] + " · " + root.dataset.search); beatText = beat; }
    const u = ease(t / step.length);
    view.carriage = C.CARRIAGE.park + (step.scan - C.CARRIAGE.park) * u;
  } else {
    const u = ease(t / step.length), h = HISTORIES[view.history];
    view.lit = h.match;
    if (h.match >= 0) view.tileZ = C.CARRIAGE.travelZ + (C.CARRIAGE.matchZ - C.CARRIAGE.travelZ) * u;
    view.verdict = step.verdict;
    view.verdictAmount = u;
  }
}
let beatText = -1;
function paint() {
  const h = HISTORIES[view.history];
  paintPart("stones", JSON.stringify([view.stones, view.drop, view.removing]), () => stonesSvg(view.stones, view.drop, view.removing));
  paintPart("verdict", view.verdict + ":" + view.verdictAmount, () => verdictSvg(view.verdict, view.verdictAmount));
  paintPart("lid", view.prisoners.count + ":" + view.prisoners.fade, () => lidSvg(view.prisoners));
  const ledger = [view.history, view.tiles, view.arriving, view.merging, view.lit];
  paintPart("ledger", JSON.stringify(ledger), () => ledgerSvg(h.tiles, view.tiles, view.arriving, view.merging, view.lit));
  paintPart("carriage", [view.history, view.carriage, view.tileZ, view.lit].join(), () => carriageSvg(view.carriage, view.tileZ, h.star, view.lit >= 0));
  paintPart("counter", view.ports, () => counterSvg(view.ports));
}
function step(dt) {
  if (beats.length) {
    clock += dt;
    const action = beats[beat];
    apply(action, Math.min(clock, action.length));
    if (clock >= action.length) { clock = 0; beat++; }
    if (beat === beats.length) settle();
    else paint();
  } else if (touring) {
    tourClock += dt;
    if (tourClock > 4.2) play(1 - view.history);
  }
  return beats.length > 0 || touring;
}
const run = playOnScreen(stage, still, step, () => { touring = false; settle(); });
const hold = () => { touring = false; readout.setAttribute("aria-live", "polite"); };
const choose = (history) => { hold(); play(history); };
root.addEventListener("focusin", hold);
buttons.forEach((button) => button.addEventListener("click", () => choose(Number(button.dataset.history))));
stage.addEventListener("click", () => choose(1 - view.history));
stage.addEventListener("keydown", (event) => {
  if (event.key === "1") choose(0);
  else if (event.key === "2") choose(1);
  else if (event.key === " " || event.key === "Enter" || event.key === "ArrowRight" || event.key === "ArrowLeft") choose(1 - view.history);
  else return;
  event.preventDefault();
});
mountSwing(stage, { touch: false, limit: 26, home: 2500, onHold: hold, onDragStart: run.pause, onDragEnd: run.resume, onSwing: (angle) => { P = swingOf(k.iso, P0, FRAME, angle); syncFigureArt(svgEl, composition(view)); paintPart.reset(); } });
// For checks: drive.mjs settles a history directly.
window.__koLedger = (history) => { hold(); select(history); view.history = history; settle(); };
`;

const COPY = {
  en: {
    title: "Superko ledger",
    hint: "Drag to rotate · 1 and 2 replay the openings",
    openings: "Replay an opening",
    opening: (i, n) => `${NAMES[i]} · ${n} moves`,
    start: "Empty board",
    search: "Checking the board after a capture at A19…",
    keys: ["Lit tile · matching post-capture board", "One tile per distinct board, including the empty board", "Red pin · White cannot play A19"],
    refs: ["Lemma 3.2", "Example 2.3", "§1.1"],
    caption: [
      "The two openings reach the same board with White to move and zero consecutive passes. Under positional superko a stone placement may recreate no earlier board after captures. Pass is exempt, so Black's pass in γ₂ adds no tile to the set of distinct boards.",
      "The carriage carries the board that a White capture at A19 would leave. After γ₁ that board is fresh, and White has 357 legal moves. After γ₂ it matches the sixth tile, filed after move 6. The red pin marks the forbidden capture, leaving 356 legal moves. Both counts include pass.",
      "Board, side to move, pass count, game status and the set of past boards determine which moves are legal. Equal states also give equal successors under each legal move. This is the strong bisimulation of Lemma 3.2.",
    ],
    aria: "Superko ledger. Keys 1 and 2 replay the two openings. Space switches between them.",
    alt: "A19 is the near corner of the Go board. A carriage compares the proposed post-capture board against the filed boards. A red pin at A19 marks a match and a forbidden capture.",
  },
  zh: {
    title: "超劫账簿",
    hint: "拖动旋转 · 数字键 1、2 重放开局",
    openings: "重放开局",
    opening: (i, n) => `${NAMES[i]} · ${n} 手`,
    start: "空盘",
    search: "比对 A19 提子后的盘面…",
    keys: ["亮牌 · 匹配的提子后盘面", "每个不同盘面存一块牌，空盘也计入", "朱红钉 · 白棋禁下 A19"],
    refs: ["引理 3.2", "例 2.3", "§1.1"],
    caption: [
      "两种开局抵达同一盘面，均轮白下，连续虚着数均为零。位置超劫禁止落子提子后重现旧盘面。虚着豁免，所以 γ₂ 中黑棋虚着时，账簿里仍是同一批盘面。",
      "滑车载着白棋在 A19 提子后将形成的盘面。γ₁ 的账簿中没有这块牌，白有 357 个合法着。γ₂ 的第六块牌正是第六手后存入的这个盘面，朱红钉升起，表示禁着，白剩 356 个合法着。两处计数均含虚着。",
      "盘面、执子方、连续虚着数、对局状态与历史盘面集合共同决定合法着法。这些量相同的两局，下同一合法着后，这些量仍相同。这就是引理 3.2 的强双模拟。",
    ],
    aria: "超劫账簿。数字键 1 与 2 重放两种开局，空格在两者之间切换。",
    alt: "A19 是棋盘朝近处的角点。滑车把假设提子后的盘面与账簿逐一比对。若匹配旧盘面，A19 升起朱红钉表示禁着。",
  },
};
const bodyOf = (lang) => {
  const copy = COPY[lang];
  const svg = k.figureSvg({ width: WIDTH, height: HEIGHT, className: "paper-figure-art", label: copy.alt, body: art });
  const buttons = HISTORIES.map((h, i) => `<button type="button" data-history="${i}" aria-pressed="${i === 1}">${copy.opening(i, h.plies.length)}</button>`).join("");
  return `<div data-figure="ko-ledger" lang="${lang}" data-start="${copy.start}" data-search="${copy.search}">${paperPlate({
    title: copy.title,
    hint: copy.hint,
    readout: readoutOf(1, lang),
    keys: [
      { mark: "lit", label: copy.keys[0] },
      { mark: "raised", label: copy.keys[1] },
      { mark: "red", label: copy.keys[2] },
    ],
    caption: copy.caption,
    refs: copy.refs,
    body: `<div class="iso-stage paper-figure-stage" data-advance tabindex="0" role="group" aria-label="${copy.aria}">${svg}</div><div class="paper-figure-controls" role="group" aria-label="${copy.openings}">${buttons}</div>`,
  })}</div>`;
};

const script = `{\n${kitSource}\n${latheSource}\n${live}\n}`;
if (fragment) {
  const outDir = join(HERE, "../../src/generated");
  mkdirSync(outDir, { recursive: true });
  writeFileSync(join(outDir, "ko-ledger.json"), JSON.stringify({ html: { zh: bodyOf("zh"), en: bodyOf("en") }, css: CSS, script: script.replace(/<\/(script)/gi, "<\\/$1") }));
  console.log("wrote src/generated/ko-ledger.json");
} else {
  mkdirSync(join(HERE, "out"), { recursive: true });
  const lang = process.argv.includes("--zh") ? "zh" : "en";
  const name = theme === "light" ? "ko-ledger-light.html" : "ko-ledger.html";
  writeFileSync(join(HERE, "out", name), k.pageHtml({ title: COPY[lang].title, theme, body: `<style>${CSS}</style>${bodyOf(lang)}`, script, width: 740 }));
  console.log("wrote out/" + name);
}
