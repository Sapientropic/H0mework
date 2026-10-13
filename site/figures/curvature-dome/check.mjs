// Checks the figure's model against Theorem 1.2 and §§7–11 of the paper: that the published
// pieces of the five-term tensor add up to the published table, that the dome's stamps are
// decided by strict enclosures, and that those stamps alone force the inertia (2, 1, 0).
import { B, B_INT, G_REM, GERSHGORIN, HALF_S, K_C, KG0, MIXED, QC, S_N, TABLE, directionOf, enclosure, lens, quadratic, stamps, terms, verdict } from "./model.mjs";

let failures = 0, checks = 0;
const ok = (condition, message) => {
  checks++;
  if (!condition) {
    failures++;
    if (failures < 20) console.error("FAIL", message);
  }
};
const near = (a, b, message, tol = 1e-12) => ok(Math.abs(a - b) <= tol, `${message}: ${a} vs ${b}`);
// A published decimal is an outward rounding to `places` digits of the value it encloses.
const outwardLo = (published, value, places = 6) => ok(published <= value + 1e-12 && value - published < 10 ** -places + 1e-12, `outward lo ${published} for ${value}`);
const outwardHi = (published, value, places = 6) => ok(published >= value - 1e-12 && published - value < 10 ** -places + 1e-12, `outward hi ${published} for ${value}`);

// (7.19): the ball's measure μ(B) = B³/(6π²).
const mu = B ** 3 / (6 * Math.PI ** 2);
ok(mu > 2.6685289152662e-16 && mu < 2.6685289152663e-16, `μ(B) = ${mu}`);

// (10.7): the three central values are affine in the integers b_i (one common ℓ_R and g).
const v = KG0;
const slope12 = (v[1] - v[0]) / Number(B_INT[1] - B_INT[0]);
const slope13 = (v[2] - v[0]) / Number(B_INT[2] - B_INT[0]);
near(slope12 / slope13, 1, "(10.7) central values share ℓ_R and g", 1e-8);
ok(v[0] < 0 && v[1] > 0 && v[2] < 0, "K_G0 signs (−, +, −)");

// §11.1: quantum legs plus contact = ½S_N widened by ‖K_C‖, outward to 10 decimals in 10⁻²⁰.
near(HALF_S[0] * 2, S_N[0], "half of (7.20)");
near(QC[0], HALF_S[0] - K_C, "§11.1 lower end", 1e-10);
near(QC[1], HALF_S[1] + K_C, "§11.1 upper end", 1e-10);

// §1.2 table, raw: K_G0 ± G_REM plus the quantum/contact interval, rounded outward.
for (let i = 0; i < 3; i++) {
  const [lo, hi] = TABLE.raw[i];
  outwardLo(lo, KG0[i] - G_REM + QC[0]);
  outwardHi(hi, KG0[i] + G_REM + QC[1]);
  // The model's enclosure on the axis is the same interval before rounding.
  const e = [0, 0, 0];
  e[i] = 1;
  const [mlo, mhi] = enclosure("five", e);
  near(mlo, KG0[i] - G_REM + QC[0], `axis ${i + 1} lo`);
  near(mhi, KG0[i] + G_REM + QC[1], `axis ${i + 1} hi`);
  ok(lo <= mlo && hi >= mhi, `table encloses the model on e${i + 1}`);
}
// (11.3)–(11.4): each Gershgorin row contains the diagonal interval widened by two mixed bounds.
for (const sector of ["raw", "conn"]) for (let i = 0; i < 3; i++) {
  const [lo, hi] = TABLE[sector][i];
  outwardLo(GERSHGORIN[sector][i][0], lo - 2 * MIXED[sector], 5.7);
  outwardHi(GERSHGORIN[sector][i][1], hi + 2 * MIXED[sector], 5.7);
}
// Inertia by the paper's route: the widened rows avoid zero, two below and one above.
for (const sector of ["raw", "conn"]) {
  const rows = GERSHGORIN[sector];
  ok(rows.every(([lo, hi]) => lo > 0 || hi < 0), `${sector} rows avoid zero`);
  ok(rows.filter(([, hi]) => hi < 0).length === 2 && rows.filter(([lo]) => lo > 0).length === 1, `${sector} Gershgorin (2, 1, 0)`);
}
// raw = mean + connected: each raw interval lies inside the sum of the other two; mean's e2 crosses 0.
for (let i = 0; i < 3; i++) {
  ok(TABLE.mean[i][0] + TABLE.conn[i][0] <= TABLE.raw[i][0] && TABLE.raw[i][1] <= TABLE.mean[i][1] + TABLE.conn[i][1], `raw ⊆ mean + conn on e${i + 1}`);
}
ok(TABLE.mean[1][0] < 0 && TABLE.mean[1][1] > 0, "mean's second axis contains zero");

// Every unit direction: the enclosure's width is fixed, and it contains the table's mixed-entry
// enclosure's centre band (both are strict, so they must overlap).
const sphere = [];
for (let i = 0; i < 4000; i++) {
  // Fibonacci points on the unit sphere.
  const z = 1 - (2 * (i + 0.5)) / 4000, r = Math.sqrt(1 - z * z), a = i * Math.PI * (3 - Math.sqrt(5));
  sphere.push([r * Math.cos(a), z, r * Math.sin(a)]);
}
for (const n of sphere) {
  const [lo, hi] = enclosure("five", n);
  near(hi - lo, 2 * G_REM + QC[1] - QC[0], "enclosure width");
  // The table route: Σ n_i² [lo_i, hi_i] ± 2m Σ|n_i n_j|.
  let tlo = 0, thi = 0, cross = 0;
  for (let i = 0; i < 3; i++) { tlo += n[i] * n[i] * TABLE.raw[i][0]; thi += n[i] * n[i] * TABLE.raw[i][1]; }
  for (const [i, j] of [[0, 1], [0, 2], [1, 2]]) cross += 2 * MIXED.raw * Math.abs(n[i] * n[j]);
  ok(Math.max(lo, tlo - cross) <= Math.min(hi, thi + cross), "two strict routes overlap");
  ok(lo >= tlo - 1e-12 && hi <= thi + 1e-12 + cross, "the five-term route is the tighter one");
  // The quantum legs alone read negative in every direction.
  ok(verdict("quantum", n) === -1, "quantum legs alone are negative");
  const t = terms("five", n);
  near(t.G + t.Q + t.C, (lo + hi) / 2 - (QC[0] + QC[1]) / 2 + (HALF_S[0] + HALF_S[1]) / 2, "terms add to the enclosure's centre", 1e-12);
}

// The dome: n and −n read the same, so the upper hemisphere carries every direction.
const dome = stamps();
ok(dome.length === 224, `stamp count ${dome.length}`);
for (const { n } of dome) near(Math.hypot(...n), 1, "unit stamp");
const ring = (j) => dome.filter((stamp) => stamp.ring === j);
// The horizon ring is the e1–e3 plane: dark all round. With the zenith lit, that is (2, 1, 0):
// nᵀKn < 0 on a whole plane and > 0 on a line leaves no room for any other inertia.
ok(ring(0).every(({ n }) => verdict("five", n) === -1), "horizon all negative");
ok(verdict("five", [0, 1, 0]) === 1, "zenith positive");
// And not only on the sampled ring: on the e1–e3 plane nᵀK_G0n ≤ K_G0,1, far below zero.
ok(KG0[0] + G_REM + QC[1] < 0 && KG0[2] + G_REM + QC[1] < 0, "the whole e1–e3 plane is negative");
// Rings at 30° and below are dark, 50° and above lit; the 40° ring is split, lit toward ±e1
// (|K11| < |K33| lowers the boundary there), dark toward ±e3, with a few undecided between.
for (let j = 0; j <= 3; j++) ok(ring(j).every(({ n }) => verdict("five", n) === -1), `ring ${j} dark`);
for (let j = 5; j <= 9; j++) ok(ring(j).every(({ n }) => verdict("five", n) === 1), `ring ${j} lit`);
const forty = ring(4).map(({ n, az }) => ({ az, v: verdict("five", n) }));
ok(forty[0].v === 1 && forty[Math.round(forty.length / 4)].v === -1, "40° lit beside e1, dark beside e3");
ok(forty.some(({ v }) => v === -1) && forty.some(({ v }) => v === 0), "40° ring has dark and undecided stamps");
ok(forty.filter(({ v }) => v === 0).length === 4, "four undecided stamps, one per quadrant");
for (const { n } of dome) ok(verdict("quantum", n) === -1, "quantum stamps dark");
// The boundary on the e1 and e3 meridians: tan² el = |K_ii| / K22 at the centre.
const boundary = (i) => (Math.atan(Math.sqrt(-KG0[i] / KG0[1])) * 180) / Math.PI;
ok(boundary(0) > 37 && boundary(0) < 38.5 && boundary(2) > 41 && boundary(2) < 42, `cone ${boundary(0)}° / ${boundary(2)}°`);
near(quadratic(directionOf(0, 0)), KG0[0], "direction e1", 1e-15);

// (8.1): the intersection of two unit balls at separation u is two caps of height 1 − u/2.
for (let i = 0; i <= 40; i++) {
  const u = (i / 40) * 2, h = 1 - u / 2;
  const caps = (2 * Math.PI * h * h * (3 - h)) / 3;
  near(lens(u) * (4 * Math.PI) / 3, caps, `lens u=${u}`, 1e-12);
  // Slicing along the axis as a second route: x runs over [u − 1, 1].
  let sum = 0;
  const steps = 4000;
  for (let k = 0; k < steps; k++) {
    const x = u - 1 + ((k + 0.5) / steps) * (2 - u);
    sum += Math.PI * Math.min(1 - x * x, 1 - (x - u) ** 2) * ((2 - u) / steps);
  }
  near(sum, caps, `lens slicing u=${u}`, 2e-5);
}
// The cusp: the one-sided slopes at u = 0 are ∓3/4 of the ball, not zero.
near((lens(1e-7) - lens(0)) / 1e-7, -0.75, "lens slope at 0⁺", 1e-6);

if (failures) {
  console.error(`${failures} of ${checks} checks failed`);
  process.exit(1);
}
const counts = [1, 0, -1].map((s) => dome.filter(({ n }) => verdict("five", n) === s).length);
console.log(`model check passed: ${checks} checks; stamps lit/undecided/dark ${counts.join("/")}, cone ${boundary(0).toFixed(1)}°–${boundary(2).toFixed(1)}°`);
