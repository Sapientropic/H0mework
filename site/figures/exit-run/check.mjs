// Checks the sand table's model against Theorem 5.1, Propositions 5.2–5.3 and Theorem 1.3.
import { CAPACITY, QUEUE, SOURCES, appended, bundleOf, capacityOf, edgesOf, effective, kindOf, reachedOf, servedOf } from "./model.mjs";

let failures = 0;
const expect = (ok, message) => { if (!ok) { failures++; console.error("FAIL", message); } };

// Theorem 5.1 and the canonical instance: one feasible action, capacity exactly 1, two of three items served.
expect(capacityOf(SOURCES.whole) === 1, "complete source: K = 1");
expect(edgesOf(SOURCES.whole).every(([c]) => c === "leave"), "every feasible edge starts at leave");
expect(servedOf(SOURCES.whole).length === CAPACITY && QUEUE - CAPACITY === 1, "two served, one pending");
for (const name of Object.keys(SOURCES)) expect((capacityOf(SOURCES[name]) > 0) === (edgesOf(SOURCES[name]).length > 0), `K > 0 iff an exit exists: ${name}`);

// Proposition 5.2: three distinct sources, all reading 0; no function of K recovers the source.
const zeros = ["link", "path", "capture"];
expect(zeros.every((name) => capacityOf(SOURCES[name]) === 0), "three zeros");
expect(new Set(zeros.map((name) => JSON.stringify(SOURCES[name]))).size === 3 && new Set(zeros.map(kindOf)).size === 3, "the three zeros are distinct sources with distinct kinds");
// Two ones: both capacities 1, the complete bundle non-empty for one and empty for the other.
expect(capacityOf(SOURCES.whole) === 1 && capacityOf(SOURCES.single) === 1, "two ones");
expect(bundleOf(SOURCES.whole) && !bundleOf(SOURCES.single), "complete vs single-service bundle");
expect(reachedOf(SOURCES.capture).length === 0 && reachedOf(SOURCES.path).length === 0, "full-domain readout (0, ∅) on both capture and path");

// Proposition 5.3: the repair matrix; one effective repair per failure, and they differ.
expect(effective(SOURCES.capture, "uncapture") && !effective(SOURCES.capture, "restorePath"), "capture: only uncapture repairs");
expect(effective(SOURCES.path, "restorePath") && !effective(SOURCES.path, "uncapture"), "path: only restorePath repairs");
expect(effective(SOURCES.link, "relink") && !effective(SOURCES.link, "uncapture") && !effective(SOURCES.link, "restorePath"), "link: only relink repairs");

// Theorem 1.3: capacity stays 1 while the frontier keeps the old image and adds one outside it.
let frontier = [];
for (let depth = 0; depth < 40; depth++) {
  const next = appended(frontier);
  const old = new Set(frontier.map((g) => g.occurrence));
  expect(frontier.every((g, i) => next[i] === g) && !old.has(next.at(-1).occurrence) && next.length === frontier.length + 1, `strict frontier step at ${depth}`);
  expect(capacityOf(SOURCES.whole) === 1, "capacity reading unchanged");
  frontier = next;
}

if (failures) process.exit(1);
console.log("model check passed: K 1 on the complete and single-service sources, 0 on link, path and capture; repair matrix; 40 strict frontier steps");
