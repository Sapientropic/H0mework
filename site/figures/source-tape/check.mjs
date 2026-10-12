// Checks the figure's model against Theorem 3.9 on every shipped tree and both κ.
import { KAPPAS, TREES, budget, fold, prog, punch, read, remaining } from "./model.mjs";

const same = (a, b) => JSON.stringify(a) === JSON.stringify(b);
let failures = 0;
const expect = (ok, message) => {
  if (!ok) {
    failures++;
    console.error("FAIL", message);
  }
};

for (const kappa of Object.keys(KAPPAS)) {
  const programs = TREES.map((tree) => prog(tree, kappa).map(punch));
  TREES.forEach((tree, index) => {
    const tokens = prog(tree, kappa);
    expect(remaining(tokens) === budget(tree), `r(prog T${index + 1}) = β under κ=${kappa}`);
    expect(same(read(programs[index]), tree), `read(prog T${index + 1}) = T under κ=${kappa}`);
  });
  const keys = programs.map((rows) => JSON.stringify(rows.map((holes) => [...holes].sort())));
  expect(new Set(keys).size === TREES.length, `prog injective on shipped trees under κ=${kappa}`);
}
expect(new Set(TREES.map((tree) => fold(tree, "zero"))).size === 1, "κ ≡ 0 reads every tree as δ₀");
TREES.forEach((tree, index) => {
  const zero = prog(tree, "zero").map(punch).map((holes) => [...holes].filter((name) => name !== "map"));
  const size = prog(tree, "size").map(punch).map((holes) => [...holes].filter((name) => name !== "map"));
  expect(same(zero, size), `T${index + 1}: tapes differ only in the map channel`);
});
expect(read([new Set(["feed"])]) === null, "a lone empty list is not a whole-tree program");

if (failures) process.exit(1);
console.log(`model check passed: ${TREES.length} trees × ${Object.keys(KAPPAS).length} κ; β = ${TREES.map(budget).join(", ")}`);
