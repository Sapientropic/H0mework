// Fig: a tower of glass pages, one per tick, every debt a thread through them, on a round deck
// (Theorem 6.2, Proposition 5.2 and the settlement type (44) of "Book-Balancing Magic Has Nowhere to Hide").
//   bun build.mjs [--light] [--zh] → out/whole-ledger-tower[-light].html (standalone, for checks)
//   bun build.mjs --fragment       → ../../src/generated/whole-ledger-tower.json (for the site)
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

// World: z up, the tower's axis at the origin. Everything is laid out round that axis; the deck's
// front faces the viewer (FRONT, the camera's azimuth), and its controls sit on an arc there.
const C = {
  FRONT: 52,
  FEET: { r: 52, radius: 4.6, h: 6 },
  DECK: { r: 64, z0: 6, z1: 14 },
  SPINDLE: { r0: 2.9, r1: 1.8 },
  PAGES: { count: 5, z0: 40, gap: 18, r: 47, glass: 45, rimH: 2.2, t: 1 },
  LANES: { P: 35, Q: 19.5 },
  ANGLES: { a: -6, b: 168, c: 200, d: 120 }, // degrees: each lineage keeps its own bearing up the tower
  PUCK: { r: 5.6, h: 2.6, ring: 4.8, ringH: 0.9, gap: 0.22 },
  VIAL: { angle: 52, len: 11, radius: 1.5 }, // dead front, so every page shows its level square to the viewer
  ARC: 56, // the radius of the control arc on the deck
  // Controls on the arc, by bearing from the front: transfer lever, receipt key, beads, successor key, action lever.
  SLOTS: { transfer: 47, receipt: 27, beads: 0, successor: -27, act: -47 },
};
C.pageZ = (i) => C.PAGES.z0 + C.PAGES.gap * i;
C.TOP = C.pageZ(C.PAGES.count - 1);
C.CROWN = C.TOP + 24;

const FIT = [
  ...Array.from({ length: 24 }, (_, i) => [C.DECK.r * Math.cos((i / 24) * Math.PI * 2), C.DECK.r * Math.sin((i / 24) * Math.PI * 2), 0]),
  ...Array.from({ length: 24 }, (_, i) => [C.PAGES.r * Math.cos((i / 24) * Math.PI * 2), C.PAGES.r * Math.sin((i / 24) * Math.PI * 2), C.TOP + 3]),
  [0, 0, C.CROWN + 8],
];
// A single standing object: the card keeps a fixed height and the tower stands centred in it.
const VIEW = { pad: 26, azimuth: C.FRONT, elevation: 28 };
const HEIGHT = 600;
const P = k.fitProjection(FIT, WIDTH, HEIGHT, VIEW);

// --- live drawing: one factory shared by the build (first frame) and the page --------------

// The whole machine turns on the spindle's axis. The kit's light is camera-locked, so turning it by θ is
// the kit's own drawing from azimuth FRONT + θ: `view` swaps the camera, and every part below reads `P`
// when it draws. Paths, shades and depth sorts all follow; only the order of whole groups (`order`) is
// decided here.
function makeLive(k, G, P0, C) {
  let P = P0;
  const view = (yaw) => { P = { ...P0, azimuth: C.FRONT + yaw }; };
  const at = (p) => k.iso(p, P);
  const S = (paths, style) => k.solidSvg(paths, style);
  const L = (d, style) => k.lineSvg(d, style);
  const D = (points, style) => k.dotsSvg(points, style);
  const X = [1, 0, 0], Y = [0, 1, 0], Z = [0, 0, 1];
  const TAU = Math.PI * 2;
  const RAD = Math.PI / 180;
  const add = (a, b) => [a[0] + b[0], a[1] + b[1], a[2] + b[2]];
  const mul = (s, a) => [s * a[0], s * a[1], s * a[2]];
  const cross = (a, b) => [a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]];
  const unit = (v) => { const n = Math.hypot(v[0], v[1], v[2]) || 1; return [v[0] / n, v[1] / n, v[2] / n]; };
  const n2 = (v) => v.toFixed(2);
  const depth = (p) => k.depthOf(p, P);
  // Paints are inline so the drawing reads the same wherever its SVG is shown on its own (the home cards).
  // The one colour is cinnabar: debt A's thread and the seal of its terminal receipt.
  const RED = "var(--cinnabar, #c8372d)";
  const PAINT = {
    glass: "fill:var(--anatomy-face);opacity:.22",
    dark: "fill:var(--anatomy-shade-0)",
    lampOn: "fill:var(--anatomy-lit)",
    bubble: "fill:var(--anatomy-face);stroke:var(--anatomy-mid);stroke-width:.6px",
    thread: "fill:none;stroke:var(--anatomy-lo);stroke-width:.85px;stroke-linecap:round",
    threadA: `fill:none;stroke:${RED};stroke-width:1.7px;stroke-linecap:round`,
    seal: `fill:${RED};stroke:none`,
    sealMark: "fill:none;stroke:var(--anatomy-face);stroke-width:.7px",
    knot: `fill:${RED}`,
    vacant: `fill:none;stroke:${RED};stroke-width:.8px`,
    vial: "fill:var(--anatomy-face)",
    bubbleIn: "fill:var(--anatomy-shade-1);stroke:var(--anatomy-hi);stroke-width:.55px",
  };
  const FV = (x, y) => G.frameOf([x, y, 0], Z, X, Y);
  const FT = FV(0, 0);
  const HV = [Math.sin(C.FRONT * RAD), -Math.cos(C.FRONT * RAD), 0]; // across the front, fixed to the deck
  const polar = (r, deg, z) => [r * Math.cos(deg * RAD), r * Math.sin(deg * RAD), z];
  const PK = C.PUCK;
  const PG = C.PAGES;
  const glassTop = (z) => z + 0.6 + PG.t;
  const stackHeight = (budget) => PK.h + budget * (PK.gap + PK.ringH);
  const spot = (debt, z) => polar(C.LANES[debt.bearer], C.ANGLES[debt.lineage], z);
  const ring = (c, r, n = 24) => k.pathOf(Array.from({ length: n }, (_, i) => at([c[0] + r * Math.cos((i / n) * TAU), c[1] + r * Math.sin((i / n) * TAU), c[2]])), true);

  // A body turned about a vertical axis draws the same from every azimuth, because the kit's light turns
  // with the camera, and moving it only shifts its picture. So it is drawn once, standing at the origin,
  // and placed with a translate: a turn redraws only what has a direction (marks, levels, levers, bolts).
  const memo = new Map();
  const once = (key, draw) => {
    let svg = memo.get(key);
    if (svg === undefined) { if (memo.size > 800) memo.clear(); svg = draw(); memo.set(key, svg); }
    return svg;
  };
  const upright = (key, c, draw) => {
    const a = at(c), o = at([0, 0, 0]);
    return `<g transform="translate(${n2(a[0] - o[0])} ${n2(a[1] - o[1])})">${once(key, draw)}</g>`;
  };

  // --- a debt on a page: a puck, a ring per unit of budget, the seal of its terminal receipt -----
  function puck(debt, c, { isA = false, seal = false, knot = false } = {}) {
    const out = [];
    // Debt A carries the dark edge; the others stay quiet, so the eye follows the red thread.
    const edge = isA ? "hi" : "mid";
    out.push(upright("puck" + isA, c, () => S(G.disc(0, PK.h, PK.r, FT, P), { tone: edge, lit: isA, inner: L(G.arcOf(FT, PK.h * 0.55, PK.r, P), { tone: "faint" }) })));
    let z = c[2] + PK.h;
    for (let i = 0; i < debt.budget; i++) {
      out.push(upright("ring" + isA, [c[0], c[1], z + PK.gap], () => S(G.disc(0, PK.ringH, PK.ring, FT, P), { tone: isA ? "mid" : "lo" })));
      z += PK.gap + PK.ringH;
    }
    if (seal) {
      // The seal of the terminal receipt, a cinnabar cap with a square cut in its face.
      out.push(upright("seal", [c[0], c[1], z], () => { const cap = G.disc(0, 1.3, 3.8, FT, P); return S(cap, { tone: "hi" }) + `<path style="${PAINT.seal}" d="${cap.fill}"/>`; }));
      const sq = [[-1.5, -1.5], [1.5, -1.5], [1.5, 1.5], [-1.5, 1.5]].map(([u, v]) => at([c[0] + u, c[1] + v, z + 1.3]));
      out.push(`<path style="${PAINT.sealMark}" d="${k.pathOf(sq, true)}"/>`);
    } else if (knot) {
      out.push(upright("knot", [c[0], c[1], z], () => `<path style="${PAINT.knot}" d="${ring([0, 0, 0], 1)}"/>`));
    }
    return out.join("");
  }

  // --- a glass page in its rim: the whole ledger at one tick ----------------------------------
  function page(z, { vacant = [], ping = 0 } = {}) {
    const out = [];
    const gTop = glassTop(z);
    // Two engraved tracks: the outer lane is bearer P, the inner one bearer Q.
    out.push(upright("glass", [0, 0, z], () => `<path style="${PAINT.glass}" d="${G.disc(0.6, glassTop(0), PG.glass, FT, P).fill}"/>`
      + L(G.circleOf(FT, glassTop(0), C.LANES.P, P) + G.circleOf(FT, glassTop(0), C.LANES.Q, P), { tone: "faint" })));
    // Where a debt stood on the page below and is gone from this one, its socket is left empty, ringed in
    // cinnabar; when the settlement lands, a ripple goes out from it.
    for (const v of vacant) {
      const c = spot(v, gTop);
      out.push(upright("vacant", c, () => `<path style="${PAINT.vacant}" d="${ring([0, 0, 0], PK.r + 0.8, 28)}"/>` + L(ring([0, 0, 0], PK.r - 1.8), { tone: "faint" })));
      if (ping > 0 && ping < 1) out.push(`<path style="${PAINT.vacant};opacity:${n2(1 - ping)}" d="${ring(c, PK.r + 0.8 + 7 * ping, 32)}"/>`);
    }
    // The rim: a thin metal band round the glass, marked at the four bearings and holding the level.
    // The kit's ring would fill its whole face, so the rim is drawn by hand: the outer wall's visible
    // shades, a top face cut to an annulus, and the edges.
    const top = z + PG.rimH;
    out.push(upright("rim", [0, 0, z], () => {
      const h = PG.rimH, wall = G.disc(0, h, PG.r, FT, P);
      return wall.shades.map((d, i) => (d ? `<path class="iso-shade" data-shade="${i}" d="${d}"/>` : "")).join("")
        + `<path class="iso-top" fill-rule="evenodd" d="${G.circleOf(FT, h, PG.r, P)}${G.circleOf(FT, h, PG.glass - 0.4, P)}"/>`
        + L(wall.crease, { tone: "faint" }) + L(G.circleOf(FT, h, PG.glass - 0.4, P), { tone: "lo" }) + L(wall.outline, { tone: "mid" });
    }));
    out.push(L(Object.values(C.ANGLES).map((a) => k.pathOf([at(polar(PG.glass + 0.4, a, top)), at(polar(PG.r - 0.2, a, top))])).join(""), { tone: "lo" }));
    return out.join("");
  }

  // The spirit level on the rim's front: double entry reads every page as balanced, its bubble always home.
  // It stands on the rim, so it sorts with the pucks and threads of its page, not under them.
  const vialAt = (z) => polar((PG.glass + PG.r) / 2, C.VIAL.angle, z + PG.rimH);
  function vial(z, wobble) {
    const out = [];
    const top = z + PG.rimH;
    const va = C.VIAL.angle, VL = C.VIAL;
    const tan = [-Math.sin(va * RAD), Math.cos(va * RAD), 0];
    const rad = [Math.cos(va * RAD), Math.sin(va * RAD), 0];
    const mid = vialAt(z);
    const FC = G.frameOf(add(mid, mul(-(VL.len / 2 + 1.4), tan)), tan, Z, rad);
    out.push(S(G.prismOf(FC, [[0, -2.2], [0.9, -2.2], [0.9, 2.2], [0, 2.2]], 0, VL.len + 2.8, P), { tone: "mid", crease: "faint" }));
    const vc = add(mid, [0, 0, 0.9 + VL.radius]);
    const FVL = G.frameOf(add(vc, mul(-VL.len / 2, tan)), tan, Z, rad);
    const L0 = VL.len, R0 = VL.radius;
    const capsule = [[0, 0.3], [0.3, R0 * 0.62, 1], [0.8, R0 * 0.9, 1], [1.5, R0, 1], [L0 - 1.5, R0, 1], [L0 - 0.8, R0 * 0.9, 1], [L0 - 0.3, R0 * 0.62, 1], [L0, 0.3]];
    // The two index marks are etched round the glass and run out at its limb.
    out.push(S(G.solidOf(capsule, FVL, P), { tone: "mid", inner: L(G.arcOf(FVL, L0 / 2 - 2, R0, P) + G.arcOf(FVL, L0 / 2 + 2, R0, P), { tone: "lo", free: true }) }));
    const b = add(vc, add(mul(wobble, tan), [0, 0, R0 * 0.9]));
    out.push(`<path style="${PAINT.bubbleIn}" d="${k.pathOf(Array.from({ length: 18 }, (_, i) => at(add(b, add(mul(1.5 * Math.cos((i / 18) * TAU), tan), mul(0.75 * Math.sin((i / 18) * TAU), rad))))), true)}"/>`);
    return out.join("");
  }

  // --- the spindle: tapered from the deck to the crown -------------------------------------------
  const SP = C.SPINDLE;
  const z0 = C.DECK.z1 + 7;
  const spR = (z) => SP.r0 + (SP.r1 - SP.r0) * Math.min(1, Math.max(0, (z - z0) / (C.CROWN - z0)));
  const spindle = (za, zb) => (zb - za < 0.05 ? "" : once(`spindle${n2(za)}:${n2(zb)}`, () => S(G.solidOf([[za, spR(za)], [zb, spR(zb)]], FT, P), { tone: "mid" })));

  // --- the tower: eyelets, pages bottom to top, each level's pucks, threads and spindle by depth ---
  function tower(st) {
    const out = [];
    const levels = st.pages.map((p, i) => ({ p, z: p.z ?? C.pageZ(i), opacity: p.opacity ?? 1 }));
    const fade = (svg, o) => (o < 1 ? `<g opacity="${n2(o)}">${svg}</g>` : svg);
    // Every debt's thread starts at an eyelet in the deck: its source.
    const first = levels[0];
    const items0 = [];
    for (const debt of (first ? first.p.ledger : [])) {
      const e = spot(debt, C.DECK.z1);
      const isA = debt.lineage === "a";
      out.push(upright("eyelet", e, () => `<path style="fill:var(--anatomy-face);stroke:var(--anatomy-mid);stroke-width:.6px" d="${ring([0, 0, 0], 1.8)}"/>` + D([at([0, 0, 0])], { size: 0.6, tone: "hi" })));
      const to = spot(debt, glassTop(first.z));
      items0.push({ d: depth(mul(0.5, add(e, to))), svg: fade(`<path style="${isA ? PAINT.threadA : PAINT.thread}" d="${k.pathOf([at(e), at(to)])}"/>`, first.opacity) });
    }
    items0.push({ d: depth([0, 0, (z0 + (first ? first.z : z0 + 6)) / 2]), svg: spindle(z0, first ? first.z : z0 + 6) });
    items0.sort((a, b) => a.d - b.d).forEach((it) => out.push(it.svg));
    levels.forEach((lv, i) => {
      const gTop = glassTop(lv.z);
      const below = levels[i - 1];
      const vacant = below ? below.p.ledger.filter((e) => !lv.p.ledger.some((f) => f.lineage === e.lineage)) : [];
      out.push(fade(upright("hub", [0, 0, lv.z - 1.2], () => S(G.disc(0, 1.2, 3.6, FT, P), { tone: "mid" })) + page(lv.z, { vacant, ping: lv.p.ping || 0 }), lv.opacity));
      const items = [{ d: depth(add(vialAt(lv.z), [0, 0, 2])), svg: fade(vial(lv.z, lv.p.wobble || 0), lv.opacity) }];
      const above = levels[i + 1];
      for (const debt of lv.p.ledger) {
        const c = spot(debt, gTop);
        const isA = debt.lineage === "a";
        const next = above && above.p.ledger.find((e) => e.lineage === debt.lineage);
        const seal = isA && lv.p.receipt;
        items.push({ d: depth(add(c, [0, 0, 2])), svg: fade(puck(debt, c, { isA, seal, knot: isA && !!next }), lv.opacity) });
        if (next) {
          // The thread from this puck's crown to the same debt's puck on the page above, through its glass.
          const from = add(c, [0, 0, stackHeight(debt.budget)]);
          const to = spot(next, glassTop(above.z));
          items.push({ d: depth(mul(0.5, add(from, to))), svg: fade(`<path style="${isA ? PAINT.threadA : PAINT.thread}" d="${k.pathOf([at(from), at(to)])}"/>`, Math.min(lv.opacity, above.opacity)) });
        }
      }
      const z1 = above ? above.z - 1.2 : C.CROWN;
      items.push({ d: depth([0, 0, (gTop + z1) / 2]), svg: spindle(lv.z + PG.rimH, z1) });
      items.sort((a, b) => a.d - b.d).forEach((it) => out.push(it.svg));
    });
    if (!levels.length) out.push(spindle(z0 + 6, C.CROWN));
    // The crown: a cap, a short cone and a bead.
    out.push(once("crown", () => {
      const cz = C.CROWN + 1.6;
      return S(G.disc(C.CROWN, C.CROWN + 1.6, 5.2, FT, P, { bevel: 0.5 }), { tone: "mid" })
        + S(G.solidOf([[cz, 2.4], [cz + 0.8, 2.1, 1], [cz + 2.6, 1.1, 1], [cz + 5.4, 0.55, 1], [cz + 7, 0.4]], FT, P, { smooth: { slope: (q) => -0.42 * Math.exp(-(q - cz) / 2.6), radius: (q) => 0.4 + 2 * Math.exp(-(q - cz) / 2.6) } }), { tone: "mid" })
        + S(G.sphereOf([0, 0, cz + 8], 1.2, P), { tone: "hi" });
    }));
    return out.join("");
  }

  // --- the controls on the deck's front arc ----------------------------------------------------
  const deckTop = C.DECK.z1;
  const slot = (name, r = C.ARC) => C.FRONT + C.SLOTS[name];
  const onArc = (name, r = C.ARC, z = deckTop) => polar(r, slot(name), z);
  const outward = (name) => [Math.cos(slot(name) * RAD), Math.sin(slot(name) * RAD), 0];
  const tangent = (name) => [-Math.sin(slot(name) * RAD), Math.cos(slot(name) * RAD), 0];
  function lever(name, pull) {
    // At rest it leans in toward the tower; pulling swings it out toward the viewer.
    const base = onArc(name, C.ARC, deckTop + 3.6);
    const ang = (-14 + 42 * pull) * RAD;
    const dir = add(mul(Math.cos(ang), Z), mul(Math.sin(ang), outward(name)));
    const tip = add(base, mul(17, dir));
    const out = [];
    out.push(S(G.disc(-3, 3, 2.4, G.frameAlong(base, tangent(name)), P), { tone: "mid" }));
    out.push(S(G.disc(0, 17, 0.95, G.frameAlong(base, dir), P), { tone: "mid" }));
    out.push(upright("tip" + (pull > 0.02), add(tip, mul(2, dir)), () => S(G.sphereOf([0, 0, 0], 2.8, P), { tone: "hi", lit: pull > 0.02 })));
    return out.join("");
  }
  const BEAD = { half: 15.5, step: 4.2 };
  function beads(slide, pair, lamps) {
    const c0 = onArc("beads", C.ARC, deckTop + 1.6);
    const t = tangent("beads");
    const along = (s) => add(c0, mul(s, t));
    const left = Array.from({ length: pair[0] }, (_, i) => -BEAD.half + 2.4 + BEAD.step * (i + 0.5));
    const right = Array.from({ length: pair[1] }, (_, i) => BEAD.half - 2.4 - BEAD.step * (pair[1] - i - 0.5));
    if (slide > 0) right[0] += (-BEAD.half + 2.4 + BEAD.step * (pair[0] + 0.5) - right[0]) * slide;
    // Seen end-on the groove lines up its beads, the centre pin and both lamps, so they share one sort.
    const items = [...left, ...right].map((s) => ({ d: depth(along(s)), svg: upright("bead", along(s), () => S(G.sphereOf([0, 0, 0], 1.9, P), { tone: "hi" })) }));
    const pin = onArc("beads");
    items.push({ d: depth(add(pin, [0, 0, 1.7])), svg: upright("pin", pin, () => S(k.cylinder(0, 0, 0.8, 0, 3.4, P, 12), { tone: "mid" })) });
    [[-1, lamps[0]], [1, lamps[1]]].forEach(([side, on]) => {
      // A prime lamp at each end of the groove.
      const c = add(polar(C.ARC, slot("beads"), deckTop), mul(side * (BEAD.half + 2.6), t));
      const lamp = upright("lamp" + on, c, () => S(G.disc(0, 1, 1.8, FT, P), { tone: on ? "hi" : "mid" }) + (on ? `<path style="${PAINT.lampOn}" d="${G.circleOf(FT, 1, 1.8, P)}"/>` : ""));
      items.push({ d: depth(add(c, [0, 0, 0.5])), svg: lamp });
    });
    return items.sort((a, b) => a.d - b.d).map((it) => it.svg).join("");
  }
  function key(name, turned) {
    const c = onArc(name);
    // At rest the bow faces the front; home, it has turned a quarter and stands edge-on.
    const a = Math.atan2(HV[1], HV[0]) + (turned * Math.PI) / 2;
    const u = [Math.cos(a), Math.sin(a), 0];
    return upright("shaft", [c[0], c[1], c[2] + 1.8], () => S(G.disc(0, 1.6, 1.05, FT, P), { tone: "mid" }))
      + S(G.prismOf(G.frameOf([c[0], c[1], c[2] + 3.4], cross(Z, u), Z, u), G.stadium(2.1, 2.1, 3, 18).map(([x, y]) => [x + 1.2, y]), -0.4, 0.4, P), { tone: "hi", lit: turned > 0.98 });
  }

  // --- the deck: feet, the graphite disc, the boss, and everything flat or low on its top ---------
  // The deck is graphite: its own token set, inline so it holds wherever the SVG is shown. The glass and
  // the metal controls keep the page's tokens, so they stand light on the dark deck.
  const GRAPHITE = [
    "--anatomy-paper:#76767a", "--anatomy-face:#7c7c80", "--anatomy-top:#808084",
    "--anatomy-shade-0:#5c5c60", "--anatomy-shade-1:#646468", "--anatomy-shade-2:#6c6c70", "--anatomy-shade-3:#747478",
    "--anatomy-hi:#2a2a2d", "--anatomy-mid:#47474b", "--anatomy-lo:#5a5a5e", "--anatomy-faint:#69696d", "--anatomy-dot:#ececee",
  ].join(";");
  function deck() {
    const { DECK, FEET, FRONT } = C;
    const out = [once("halo", () => `<path class="iso-halo" d="${k.haloOf({ x: -DECK.r, y: -DECK.r, w: DECK.r * 2, d: DECK.r * 2, r: DECK.r }, 0, 6, P)}"/>`), `<g style="${GRAPHITE}">`];
    // Three feet under the rim, far to near; the deck covers whatever of them it overhangs.
    [FRONT + 60, FRONT - 60, FRONT + 180].map((a) => polar(FEET.r, a, 0)).sort((a, b) => depth(a) - depth(b))
      .forEach((c) => out.push(upright("foot", c, () => S(k.cylinder(0, 0, FEET.radius, 0, FEET.h, P, 24), { tone: "lo" }))));
    // The deck: a disc with a chamfered top edge, a groove outside the control arc, a bolt circle.
    out.push(once("deck", () => {
      const profile = [[DECK.z0, DECK.r - 2], [DECK.z0 + 1.2, DECK.r], [DECK.z1 - 1.4, DECK.r], [DECK.z1, DECK.r - 1.6]];
      return S(G.solidOf(profile, FT, P), { tone: "mid", inner: L(G.arcOf(FT, DECK.z0 + 4.2, DECK.r, P), { tone: "faint" }) })
        + L(G.circleOf(FT, DECK.z1, DECK.r - 3.6, P), { tone: "faint" }) + L(G.circleOf(FT, DECK.z1, C.ARC - 6.5, P), { tone: "faint" });
    }));
    out.push(D(G.dotsOf(FT, DECK.z1, DECK.r - 2, 36, P, { all: true, phase: 0.13 }), { size: 0.38 }));
    // Lever gates: a slot running outward under each lever.
    for (const name of ["transfer", "act"]) {
      const o = outward(name), t = tangent(name), c = onArc(name);
      const quad = [[-1.4, -5], [1.4, -5], [1.4, 7], [-1.4, 7]].map(([u, v]) => at([c[0] + u * t[0] + v * o[0], c[1] + u * t[1] + v * o[1], deckTop]));
      out.push(`<path style="${PAINT.dark}" d="${k.pathOf(quad, true)}"/>`, L(k.pathOf(quad, true), { tone: "lo" }));
    }
    // The bead groove, along the arc's tangent at the front.
    const c = onArc("beads"), t = tangent("beads"), o = outward("beads");
    const groove = [[-BEAD.half, -2.6], [BEAD.half, -2.6], [BEAD.half, 2.6], [-BEAD.half, 2.6]].map(([u, v]) => at([c[0] + u * t[0] + v * o[0], c[1] + u * t[1] + v * o[1], deckTop]));
    out.push(`<path style="${PAINT.dark}" d="${k.pathOf(groove, true)}"/>`, L(k.pathOf(groove, true), { tone: "lo" }));
    // The boss the spindle stands in.
    out.push(once("boss", () => S(G.disc(DECK.z1, DECK.z1 + 3, 15, FT, P, { bevel: 0.6 }), { tone: "mid" })));
    out.push(D(G.dotsOf(FT, DECK.z1 + 3, 12, 8, P, { all: true }), { size: 0.4 }));
    out.push(once("collar", () => S(G.disc(DECK.z1 + 3, DECK.z1 + 7, 7.5, FT, P), { tone: "mid", inner: L(G.arcOf(FT, DECK.z1 + 5, 7.5, P), { tone: "faint" }) })));
    out.push("</g>");
    // Key barrels: low enough that nothing on the tower ever passes under them on screen.
    for (const name of ["receipt", "successor"]) {
      const k0 = onArc(name);
      out.push(upright("barrel", k0, () => S(k.cylinder(0, 0, 3.8, 0, 1.8, P, 28, 0.3), { tone: "mid" }) + L(k.ring(0, 0, 2.5, 1.8, P, 24), { tone: "lo" })));
    }
    return out.join("");
  }

  // The standing controls sit on the arc outside the pages and the threads, so each one is wholly in
  // front of the tower or wholly behind it, by which side of the axis it is on; where it crosses over, at
  // the tower's flank, the two never overlap on screen and the swap shows nothing.
  const STANDING = { "lever-transfer": "transfer", "lever-act": "act", beads: "beads", "key-receipt": "receipt", "key-successor": "successor" };
  const order = () => [["tower", depth([0, 0, 0])], ...Object.entries(STANDING).map(([part, name]) => [part, depth(onArc(name))])]
    .sort((a, b) => a[1] - b[1]).map(([part]) => part);

  return { PAINT, view, deck, tower, lever, beads, key, order, onArc, outward, tangent, slot, polar, BEAD, deckTop };
}

const LIVE = makeLive(k, G, P, C);

// The drawing at rest shows the whole run the tour plays, ending settled.
const RUN = ["transfer", "carry", "act", "carry"];
const REST_PAGES = RUN.reduce((pages, event) => [...pages, M.nextPage(pages[pages.length - 1], event)], [M.firstPage()]);
const REST = { pages: REST_PAGES };
const REST_PARTS = {
  tower: LIVE.tower(REST),
  "lever-transfer": LIVE.lever("transfer", 0),
  "lever-act": LIVE.lever("act", 0),
  beads: LIVE.beads(0, [3, 3], [true, true]),
  "key-receipt": LIVE.key("receipt", 1),
  "key-successor": LIVE.key("successor", 1),
};

const svg = k.figureSvg({
  width: WIDTH,
  height: HEIGHT,
  className: "wt-svg",
  label:
    "A tower of glass pages on a spindle above a round deck, one page per tick. Each debt is a puck on every page, joined page to page by a taut thread that starts at an eyelet in the deck. Debt A's thread is cinnabar. A transfer moves A from the outer lane to the inner one, so its thread bends while its ring stays. The target-six action slides a bead from 2 + 4 to 3 + 3 and pays A's ring; that page carries a cinnabar seal, the terminal receipt, and the page above has no A, so A's thread stops at the seal. The spirit level in every page's rim stays level throughout.",
  body: [
    `<g data-part="deck">${LIVE.deck()}</g>`,
    ...LIVE.order().map((part) => `<g data-part="${part}">${REST_PARTS[part]}</g>`),
  ],
});

const CSS = `
.iso-stage{outline:none;touch-action:pan-y;cursor:grab}
.iso-stage.turning,.iso-stage.turning [data-part]{cursor:grabbing}
.iso-stage:focus-visible{box-shadow:0 0 0 1px var(--anatomy-mid)}
.wt-svg [data-part="tower"],.wt-svg [data-part^="lever"],.wt-svg [data-part="beads"]{cursor:pointer}
[data-figure="whole-ledger-tower"] .iso-swatch[data-mark="red"] path{stroke:var(--cinnabar,#c8372d)}
@media (max-width:560px){.wt-svg.iso-svg{width:106%;max-width:none;margin:0 -3%}[data-figure="whole-ledger-tower"] .iso-plate-corner[data-corner="hint"]{display:none}[data-figure="whole-ledger-tower"] .iso-plate-corner[data-corner="readout"]{left:0;white-space:normal;text-align:right}}
`;

const COPY = {
  en: {
    title: "This is no migration",
    hint: "Drag to turn · levers: transfer · act",
    keys: ["Red thread: debt A through every page; the seal is its terminal receipt, the red ring its empty place on the next page", "Outer and inner track: bearers P and Q; one ring per unit of budget", "Spirit level on each page: double entry, level every time"],
    refs: ["Theorem 6.2", "Proposition 5.2", "settlement type (44)"],
    caption: [
      "A tower of glass pages: each page is the whole ledger at one tick, and the tower grows a page per tick.",
      "A debt is a puck with one ring per unit of budget, on the same bearing on every page. A taut thread runs from its eyelet in the deck, where its source is, up through every page: four threads, four debts that no page turn can lose. Debt A’s thread is the red one. The outer track of each page belongs to bearer P, the inner track to bearer Q.",
      "The spirit level at the front of each page is the double-entry reading: every posting debits and credits the same amount, so whenever a page lands its bubble swings and settles back in the middle.",
      ["Left lever: transfer. ", "Debt A moves from bearer P on the outer lane to bearer Q on the inner one. Its thread bends inward and its ring rides on: same debt, b(f) = b(e), legal and unpaid, however often it is pulled."],
      ["Right lever: the target-six action. ", "4 is not prime, a bead slides, and 2 + 4 becomes 3 + 3, which to double entry is one more balanced unit moved across. On the next page A’s ring is gone, a strict payment from 1 to 0. Both sides are prime, so that page carries a cinnabar seal, the terminal receipt, and the first key turns."],
      "Settlement waits for the page above. The source’s continuation no longer activates A, so its place on that page stays empty, ringed in red; its thread stops at the seal, and the second key turns. B, C and D keep rising.",
      "A level page was never the evidence.",
    ],
    aria: "Whole-ledger tower: drag or ← → to turn it, T transfers debt A to the other bearer, A runs the target-six action, Space adds a page",
    labels: { page: "page", receipt: ["receipt —", "receipt ✓"], next: ["next: A", "next: no A"], settled: "settled", archived: "A closed", dr: "Dr", cr: "Cr" },
  },
  zh: {
    title: "这次不是迁账",
    hint: "拖动转塔 · 左杆迁账 · 右杆行动",
    keys: ["红线：债 A 穿过每一页；朱印是它的终回执，红圈是它在下一页留下的空位", "外圈、内圈：承担者 P、Q；每环一单位预算", "页前水平仪：复式记账，每页都平"],
    refs: ["定理 6.2", "命题 5.2", "结清类型 (44)"],
    caption: [
      "一座玻璃页叠成的塔：每一页是某一拍时的整本账，每走一拍，塔长高一页。",
      "每笔债是一枚圆盘，预算有几单位就叠几环，在每一页都占同一个方位。一根绷紧的线从它在台座上的线眼——它的来源——出发，一页一页穿上去：四根线就是四笔债，翻哪一页都丢不掉。红的那根是债 A。每页外圈的轨道属于承担者 P，内圈属于承担者 Q。",
      "每页正前方的水平仪是复式记账的读法：每笔分录借贷同额，所以每落下一页，气泡晃一晃，又回到正中。",
      ["左拉杆：迁账。", "把债 A 从外圈的承担者 P 搬到内圈的承担者 Q：线向内折了一下，环照样跟着走——同一笔债，b(f) = b(e)，合法，但没付款，拉多少次都一样。"],
      ["右拉杆：目标六行动。", "4 不是素数，拨过一颗珠，2 + 4 成了 3 + 3；在复式眼里，这又是一笔平衡的等额挪动。下一页上 A 的环没了，预算从 1 严格降到 0。两侧都是素数，这一页压上一枚朱印——终回执，第一把钥匙转动。"],
      "结清还要看塔上再高一层：源的接续不再激活 A，它在那一页的位置空着，圈着一道红圈；线停在朱印上，第二把钥匙才转。B、C、D 继续往上长。",
      "页页都平，从来不是证据。",
    ],
    aria: "整账塔：拖动或 ← → 转动，T 把债 A 迁给另一个承担者，A 执行目标六行动，空格加一页",
    labels: { page: "页", receipt: ["终回执 —", "终回执 ✓"], next: ["下一页仍有 A", "下一页无 A"], settled: "结清", archived: "A 已了结", dr: "借", cr: "贷" },
  },
};

const readoutOf = (pages, labels, settledFlag) => {
  const p = pages[pages.length - 1];
  const a = p.ledger.find((e) => e.lineage === "a");
  const n = p.postings.length;
  const head = a ? `A@${a.bearer} b ${a.budget}` : `${labels.archived}`;
  const receipt = pages.some((q) => q.receipt);
  const tail = receipt ? ` · ${labels.receipt[1]}${a ? "" : ` · ${labels.next[1]}`}` : ` · ${labels.receipt[0]}`;
  return `${labels.page} ${pages.length} · ${head} · ${labels.dr} ${n} = ${labels.cr} ${n}${tail}${settledFlag ? ` · ${labels.settled}` : ""}`;
};

const bodyOf = (lang) => {
  const copy = COPY[lang];
  return `<div data-figure="whole-ledger-tower" data-labels='${JSON.stringify(copy.labels)}'>${k.plateHtml({
    fig: "Fig 6.2",
    title: copy.title,
    hint: copy.hint,
    readout: readoutOf(REST_PAGES, copy.labels, true),
    keys: [
      { mark: "red", label: copy.keys[0] },
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
const latheSource = `const LATHE = (() => {\n${strip("../kit/lathe.mjs").replace(/^import .*$/gm, "")}\nreturn { disc, ringBand, frameOf, frameAlong, pointOf, prismOf, stadium, sphereOf, circleOf, arcOf, dotsOf, solidOf, viewOf };\n})();`;
const modelSource = `const MODEL = (() => {\n${strip("model.mjs")}\nreturn { firstPage, nextPage, settled, successorHas, A };\n})();`;

const live = `
const P = ${JSON.stringify(P)};
const WIDTH = ${WIDTH};
const C = ${JSON.stringify(C, (key, value) => (typeof value === "function" ? undefined : value))};
C.pageZ = (i) => C.PAGES.z0 + C.PAGES.gap * i;
C.TOP = C.pageZ(C.PAGES.count - 1);
const kit = { iso, depthOf, pathOf, solidSvg, lineSvg, dotsSvg, ring, cylinder, haloOf };
const LIVE = (${makeLive.toString()})(kit, LATHE, P, C);
const readoutOf = ${readoutOf.toString()};
const root = document.querySelector('[data-figure="whole-ledger-tower"]');
const labels = JSON.parse(root.dataset.labels);
const stage = root.querySelector(".iso-stage");
const readout = root.querySelector("[data-readout]");
const parts = {};
for (const node of stage.querySelectorAll("[data-part]")) parts[node.dataset.part] = node;
const still = matchMedia("(prefers-reduced-motion: reduce)");
const smooth = (f) => { const t = Math.min(1, Math.max(0, f)); return t * t * (3 - 2 * t); };
const N = C.PAGES.count;

function fresh() {
  return { pages: [MODEL.firstPage()], pull: { transfer: 0, act: 0 }, pair: [2, 4], slide: 0, lamps: [true, false], keys: [0, 0], flag: 0, settledFlag: false };
}
const RUN = ${JSON.stringify(["transfer", "carry", "act", "carry"])};
function full() {
  const s = fresh();
  for (const event of RUN) s.pages.push(MODEL.nextPage(s.pages[s.pages.length - 1], event));
  return { ...s, pair: [3, 3], lamps: [true, true], keys: [1, 1], flag: 1, settledFlag: true };
}
let st = full();
let queue = [], task = null, touring = !still.matches, visible = false, frame = 0, last = 0, idle = 0;
const TOUR = [["wait", 3.2], ["reset"], ["wait", 1.2], ["page", "transfer"], ["wait", 1.2], ["page", "carry"], ["wait", 0.9], ["page", "act"], ["wait", 1.4], ["page", "carry"], ["wait", 2]];
let tourAt = 0;
// The turn: yaw in degrees from the front. A drag turns it under the finger, a flick spins on and slows,
// and while the tour runs the machine sways gently either side of its front so the threads show their depth.
const SWAY = { amp: 16, period: 19 };
let yaw = 0, spin = 0, swayT = 0, press = null, quiet = 0, drawnYaw = null, layout = "";

function say() {
  const text = readoutOf(st.pages, labels, st.settledFlag);
  if (readout.textContent !== text) readout.textContent = text;
}
function draw() {
  LIVE.view(yaw);
  if (drawnYaw !== yaw) parts.deck.innerHTML = LIVE.deck();
  parts.tower.innerHTML = LIVE.tower(st);
  parts["lever-transfer"].innerHTML = LIVE.lever("transfer", st.pull.transfer);
  parts["lever-act"].innerHTML = LIVE.lever("act", st.pull.act);
  parts.beads.innerHTML = LIVE.beads(st.slide, st.pair, st.lamps);
  parts["key-receipt"].innerHTML = LIVE.key("receipt", st.keys[0]);
  parts["key-successor"].innerHTML = LIVE.key("successor", st.keys[1]);
  const order = LIVE.order();
  if (order.join() !== layout) { layout = order.join(); for (const part of order) parts.deck.parentNode.appendChild(parts[part]); }
  drawnYaw = yaw;
  say();
}
const wrap = (a) => a - 360 * Math.round(a / 360);
function turn(dt) {
  if (press && press.moved) return;
  if (Math.abs(spin) > 2) { yaw += spin * dt; spin *= Math.exp(-3 * dt); return; }
  spin = 0;
  if (!touring) return;
  // Back to the sway the short way round, however far a spin carried it.
  swayT += dt;
  yaw = wrap(yaw);
  const target = SWAY.amp * Math.sin((2 * Math.PI * swayT) / SWAY.period);
  yaw += (target - yaw) * (1 - Math.exp(-1.4 * dt));
}
const last2 = () => st.pages[st.pages.length - 1];
const prev2 = (i) => st.pages[i - 1];
function begin([kind, arg]) {
  task = { kind, arg, t: 0 };
  if (kind === "page") {
    const prev = last2();
    const next = MODEL.nextPage(prev, arg);
    task.next = next;
    // A full tower sinks a page into its base before the new one lands.
    task.sink = st.pages.length >= N;
    task.lever = next.event === "transfer" ? "transfer" : next.event === "act" ? "act" : null;
  }
}
function stepTask(dt) {
  task.t += dt;
  const t = task.t;
  if (task.kind === "wait") { if (t >= task.arg) task = null; return; }
  if (task.kind === "reset") {
    // The pages lift off from the top down; the first page settles back.
    const n = st.pages.length;
    st.pages.forEach((p, i) => { const u = smooth((t - (n - 1 - i) * 0.12) / 0.5); p.opacity = 1 - u; p.z = C.pageZ(i) + 14 * u; });
    if (t >= 0.5 + n * 0.12 + 0.1) { st = fresh(); st.pages[0].opacity = 0; task.back = task.back || t; }
    if (task.back) { const u = smooth((t - task.back) / 0.6); st.pages[0].opacity = u; st.pages[0].z = C.pageZ(0) + 14 * (1 - u); if (u >= 1) { delete st.pages[0].opacity; delete st.pages[0].z; task = null; } }
    return;
  }
  if (task.kind === "page") {
    const L0 = task.lever ? 0.45 : 0;
    if (task.lever) st.pull[task.lever] = Math.sin(Math.min(1, t / L0 / 2) * Math.PI);
    // The action slides one bead across before its page is written.
    if (task.lever === "act") {
      st.slide = smooth(t / L0);
      if (t >= L0 && !task.acted) { task.acted = true; st.pair = task.next.pair; st.slide = 0; st.lamps = st.pair.map((n) => [2, 3, 5].includes(n)); }
    }
    if (t < L0) return;
    const u = t - L0;
    if (!task.added) {
      task.added = true;
      if (task.sink) st.pages.shift();
      st.pages.push({ ...task.next, opacity: 0, z: C.pageZ(st.pages.length) + 16 });
    }
    const i = st.pages.length - 1;
    const page = st.pages[i];
    const v = smooth(u / 0.7);
    page.opacity = v;
    page.z = C.pageZ(i) + 16 * (1 - v);
    // On landing the new page's level swings and settles home: double entry balances every page.
    const landed = u - 0.7;
    page.wobble = landed > 0 ? 2.6 * Math.sin(landed * 12) * Math.exp(-landed * 4) : 0;
    if (landed >= 0 && !task.landed) {
      task.landed = true;
      if (task.lever) st.pull[task.lever] = 0;
      // The keys: the first turns on the receipt page, the second when the page above has no A.
      const prev = st.pages[i - 1];
      if (page.receipt) task.key = 0;
      else if (prev && prev.receipt && !MODEL.successorHas(page.ledger, MODEL.A)) task.key = 1;
    }
    if (task.key !== undefined && landed >= 0 && !task.keyDone) {
      st.keys[task.key] = smooth(landed / 0.35);
      if (task.key === 1) page.ping = Math.min(1, landed / 0.9);
      if (landed >= (task.key === 1 ? 0.9 : 0.4)) {
        task.keyDone = true;
        if (task.key === 1) st.settledFlag = MODEL.settled({ receipt: prev2(i).receipt, successor: page.ledger, debt: MODEL.A });
      }
    }
    if (landed >= 0.95 && (task.key === undefined || task.keyDone)) {
      delete page.opacity; delete page.z; page.wobble = 0;
      task = null;
    }
    return;
  }
}
function nextTask() {
  if (queue.length) return queue.shift();
  if (!touring) return null;
  return TOUR[tourAt++ % TOUR.length];
}
let drawn = null;
function tick(time) {
  const dt = last ? Math.min((time - last) / 1000, 1 / 30) : 1 / 60;
  last = time;
  if (!task) { const n = nextTask(); if (n) begin(n); }
  const moving = task && task.kind !== "wait";
  if (task) stepTask(dt);
  turn(dt);
  if (moving || drawn !== st || drawnYaw !== yaw) { draw(); drawn = st; }
  const busy = touring || task || queue.length || spin;
  frame = visible && busy ? requestAnimationFrame(tick) : 0;
}
const run = () => { if (!frame && visible && !still.matches) { last = 0; frame = requestAnimationFrame(tick); } };
const hold = () => { touring = false; clearTimeout(idle); idle = setTimeout(() => { touring = !still.matches; tourAt = 0; queue = [["reset"]]; run(); }, 12000); };
function request(event) {
  hold();
  // A pause gives way at once; after a settlement the tower starts over before the new page.
  if (task && task.kind === "wait") task = null;
  const pending = queue.length || task ? null : st;
  if ((pending || st).settledFlag && !queue.some((q) => q[0] === "reset")) queue.push(["reset"]);
  queue.push(["page", event]);
  if (still.matches) { while (queue.length) { begin(queue.shift()); let guard = 0; while (task && guard++ < 2000) stepTask(1 / 30); } draw(); return; }
  run();
}
// Drag sideways to turn: the pages' rim follows the pointer. A press that stays put is still a click.
const degPerPx = () => 180 / Math.PI / (C.PAGES.r * P.scale * (stage.getBoundingClientRect().width / WIDTH));
const show = () => { if (still.matches || !frame) draw(); run(); };
stage.addEventListener("pointerdown", (event) => {
  if (event.button !== 0) return;
  press = { id: event.pointerId, x: event.clientX, yaw, moved: false, trail: [[event.timeStamp, event.clientX]] };
});
stage.addEventListener("pointermove", (event) => {
  if (!press || event.pointerId !== press.id) return;
  const dx = event.clientX - press.x;
  if (!press.moved) {
    if (Math.abs(dx) < 6) return;
    press.moved = true; spin = 0; hold();
    stage.setPointerCapture(event.pointerId);
    stage.classList.add("turning");
  }
  yaw = press.yaw + dx * degPerPx();
  press.trail.push([event.timeStamp, event.clientX]);
  while (press.trail.length > 2 && event.timeStamp - press.trail[0][0] > 90) press.trail.shift();
  show();
});
const release = (event) => {
  if (!press || event.pointerId !== press.id) return;
  if (press.moved) {
    const [t0, x0] = press.trail[0];
    const span = (event.timeStamp - t0) / 1000;
    spin = !still.matches && span > 0.01 ? Math.max(-720, Math.min(720, ((event.clientX - x0) / span) * degPerPx())) : 0;
    quiet = event.timeStamp;
    stage.classList.remove("turning");
    run();
  }
  press = null;
};
stage.addEventListener("pointerup", release);
stage.addEventListener("pointercancel", release);
stage.addEventListener("click", (event) => {
  if (event.timeStamp - quiet < 80) return;
  const part = event.target.closest("[data-part]");
  if (!part) return;
  const name = part.dataset.part;
  if (name === "lever-transfer") request("transfer");
  else if (name === "lever-act" || name === "beads") request("act");
  else if (name === "tower") request("carry");
});
stage.addEventListener("keydown", (event) => {
  const key = event.key.toLowerCase();
  if (key === "t") request("transfer");
  else if (key === "a") request("act");
  else if (key === " " || key === "arrowup") request("carry");
  else if (key === "arrowleft" || key === "arrowright") {
    // A quarter-ish turn per press: the spin coasts 30° and stops.
    const way = key === "arrowleft" ? -1 : 1;
    hold();
    if (still.matches) { yaw = wrap(yaw + 30 * way); draw(); } else { spin += 90 * way; run(); }
  }
  else return;
  event.preventDefault();
});
// The kit's turn hook, so drive.mjs can turn and orbit this figure like an engine-built one; it holds the tour.
window.__isoTurn = { set: (value) => { hold(); spin = 0; yaw = Number(value); draw(); }, get: () => yaw };
new IntersectionObserver((entries) => { visible = entries[entries.length - 1].isIntersecting; if (visible) run(); }, { rootMargin: "120px 0px" }).observe(stage);
say();
`;

const script = `{\n${kitSource}\n${latheSource}\n${modelSource}\n${live}\n}`.replace(/<\/(script)/gi, "<\\/$1");
if (fragment) {
  const outDir = join(HERE, "../../src/generated");
  mkdirSync(outDir, { recursive: true });
  writeFileSync(join(outDir, "whole-ledger-tower.json"), JSON.stringify({ html: { zh: bodyOf("zh"), en: bodyOf("en") }, css: CSS, script }));
  console.log("wrote src/generated/whole-ledger-tower.json");
} else {
  mkdirSync(join(HERE, "out"), { recursive: true });
  const name = theme === "light" ? "whole-ledger-tower-light.html" : "whole-ledger-tower.html";
  const lang = process.argv.includes("--zh") ? "zh" : "en";
  writeFileSync(join(HERE, "out", name), k.pageHtml({ title: COPY[lang].title, theme, body: `<style>${CSS}</style>${bodyOf(lang)}`, script, width: 760 }));
  console.log("wrote out/" + name);
}
