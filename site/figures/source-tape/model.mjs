// Truth model for the source-tape figure: Definition 3.8 and Theorem 3.9 of
// "The State Is Not the History, the Source Is" (papers/first-release, source-process-core).
// Every number and every hole the figure shows is computed here.

export const ROOTS = ["a", "b", "c"];

// A rooted tree occ(a; T1..Tk) is [label, [children]].
export const TREES = [
  ["a", []],
  ["a", [["b", []]]],
  ["a", [["b", []], ["c", []]]],
  ["a", [["b", [["c", []]]], ["a", []]]],
  ["c", [["a", [["b", []], ["c", []]]], ["b", []]]],
];

// Two constructor functions κ : Root → List(C) → C with C = ℤ.
export const KAPPAS = {
  zero: () => 0, // κ ≡ 0, Theorem 3.9(4)
  size: (_label, values) => 1 + values.reduce((sum, value) => sum + value, 0),
};

export const fold = (tree, kappa) => KAPPAS[kappa](tree[0], tree[1].map((child) => fold(child, kappa)));

// prog_κ and kids_κ, written as the expression's prefix tokens:
//   prog(occ(a; Ts)) = bilinear_{lift κ}(var a, kids Ts)
//   kids([])         = const δ_[]
//   kids(T :: Ts)    = bilinear_{lift cons}(prog T, kids Ts)
export function prog(tree, kappa) {
  return [{ kind: "bilinear", map: "kappa", kappa }, { kind: "var", label: tree[0] }, ...kids(tree[1], kappa)];
}
function kids(trees, kappa) {
  if (!trees.length) return [{ kind: "const" }];
  return [{ kind: "bilinear", map: "cons" }, ...prog(trees[0], kappa), ...kids(trees.slice(1), kappa)];
}

// Remaining count r: var 1, const 0, each bilinear node 1 (Proposition 3.7).
export const costOf = (token) => (token.kind === "const" ? 0 : 1);
export const remaining = (tokens) => tokens.reduce((sum, token) => sum + costOf(token), 0);

// Tree budget β, from syntax alone.
export const budget = (tree) => 2 + budgetKids(tree[1]);
const budgetKids = (trees) => (trees.length ? budget(trees[0]) + budgetKids(trees.slice(1)) + 1 : 0);

// Tape channels across the tape (y order, back to front). Channel "map" carries
// which bilinear map a node holds; the syntax-only reader has no pin over it.
export const CHANNELS = ["cost", "bilinear", "cons", "feed", "map", "label-hi", "label-lo"];
export const READ_CHANNELS = CHANNELS.filter((name) => name !== "map" && name !== "feed");

export function punch(token) {
  const holes = new Set(["feed"]);
  if (costOf(token)) holes.add("cost");
  if (token.kind === "bilinear") holes.add("bilinear");
  if (token.map === "cons") holes.add("cons");
  if (token.map === "kappa" && token.kappa === "size") holes.add("map");
  if (token.kind === "var") {
    const code = ROOTS.indexOf(token.label) + 1;
    if (code & 2) holes.add("label-hi");
    if (code & 1) holes.add("label-lo");
  }
  return holes;
}

// The syntax-only reader: it sees only READ_CHANNELS and never evaluates.
// Returns the tree, or null when the rows are not a whole-tree program.
export function read(rows) {
  const tokens = rows.map((holes) => {
    const has = (name) => holes.has(name);
    if (has("bilinear")) return { kind: "bilinear", cons: has("cons") };
    if (has("cost")) return { kind: "var", label: ROOTS[(has("label-hi") ? 2 : 0) + (has("label-lo") ? 1 : 0) - 1] };
    return { kind: "const" };
  });
  let at = 0;
  const tree = () => {
    const node = tokens[at++];
    if (!node || node.kind !== "bilinear" || node.cons) throw new Error("expected bilinear root node");
    const label = tokens[at++];
    if (!label || label.kind !== "var" || !label.label) throw new Error("expected root variable");
    return [label.label, list()];
  };
  const list = () => {
    const node = tokens[at++];
    if (node?.kind === "const") return [];
    if (node?.kind !== "bilinear" || !node.cons) throw new Error("expected cons or empty list");
    return [tree(), ...list()];
  };
  try {
    const result = tree();
    return at === tokens.length ? result : null;
  } catch {
    return null;
  }
}

export function figureData(kappa) {
  return TREES.map((tree) => {
    const tokens = prog(tree, kappa);
    return {
      tree,
      rows: tokens.map((token) => [...punch(token)]),
      cost: tokens.map(costOf),
      budget: budget(tree),
      value: fold(tree, kappa),
    };
  });
}
