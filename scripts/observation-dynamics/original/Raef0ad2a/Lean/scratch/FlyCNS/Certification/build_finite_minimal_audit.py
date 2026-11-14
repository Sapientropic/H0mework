"""Independent kernel controls and complete frozen finite-model provenance."""

import ast
from hashlib import sha256
import json
from pathlib import Path
import re
import sys

HERE = Path(__file__).resolve().parent
OWNED = HERE.parent
OUT = HERE / ".cache" / "finite-minimal-audit"
PREFIX = "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.FlyCNS.FiniteMinimalModel."
EXPECTED = "aa2805aa54f6d53fdaf457ba3e227bd4e8c970bb8e84da750e22bbda7f80fafa"
UPSTREAM = "e1b1921b9599ef3bb630f6937af2cccabc920d421ff031cfafe0aa9840c3d298"
CANDIDATE = OWNED / "SourceFiniteMinimalModel.lean"
ROOTS = [PREFIX + match.group(1) for match in re.finditer(
    r"^(?:def|theorem|structure|abbrev|inductive)\s+([A-Za-z][A-Za-z0-9_.]*)",
    CANDIDATE.read_text(), re.MULTILINE)]

CONTROLS = r'''
namespace FlyCNSFiniteMinimalCertification
open SaturationMonoid.ResponsibilityLifecycle
open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.FlyCNS
open FiniteMinimalModel

-- A complete four-state, two-letter source; no desired partition is supplied.
def action (letter : Fin 2) (state : Fin 4) : Fin 4 :=
  if letter = 0 then if state = 0 then 1 else if state = 1 then 2 else 3 else 0
abbrev observationType (reader : Fin 2) : Type := if reader = 0 then Bool else Nat
abbrev chain : Source where
  stateCount := 4
  letterCount := 2
  readerCount := 2
  Output := observationType
  outputEq := fun reader => by unfold observationType; split_ifs <;> infer_instance
  initial := 0
  autonomous := 0
  reader := 0
  action := action
  read := fun reader => by
    unfold observationType
    split_ifs
    · exact fun state => state == 3
    · exact fun _ => 7
abbrev blind : Source where
  stateCount := 4
  letterCount := 2
  readerCount := 1
  Output := fun _ => Nat
  outputEq := fun _ => inferInstance
  initial := 0
  autonomous := 0
  reader := 0
  action := action
  read := fun _ _ => 7
def additional : AdditionalReadout blind where
  Output := Bool
  outputEq := inferInstance
  read state := state == 3

example : Nonempty (State chain) := ⟨chain.initial⟩
example : chain.stateCount = 4 ∧ chain.letterCount = 2 ∧ chain.readerCount = 2 := by decide
example : chain.Output 0 = Bool ∧ chain.Output 1 = Nat := ⟨rfl, rfl⟩
example : sameReads chain 1 2 := by decide
example : (1, 2) ∈ initialPairs chain := by decide
example : (1, 2) ∉ refine chain (initialPairs chain) := by decide
example : (0, 1) ∈ refine chain (initialPairs chain) := by decide
example : (0, 1) ∉ refine chain (refine chain (initialPairs chain)) := by decide
example : (initialPairs chain).card = 10 := by decide
example : (refine chain (initialPairs chain)).card < (initialPairs chain).card := by decide
example : (kernel chain).card = 4 := by decide
example : refine chain (kernel chain) = kernel chain := kernel_fixed chain
example : (1, 2) ∉ kernel chain := by decide
example : ¬ FutureSame chain 1 2 := by
  intro same
  have future := same [0] 0
  change false = true at future
  cases future
example : encode chain 1 ≠ encode chain 2 := by
  intro same
  have future := (encode_kernel chain 1 2).1 same [0] 0
  change false = true at future
  cases future
example : [code chain 0, code chain 1, code chain 2, code chain 3] = [0, 1, 2, 3] := by decide
example : [code blind 0, code blind 1, code blind 2, code blind 3] = [0, 0, 0, 0] := by decide
example : (kernel blind).card = 16 := by decide
example : encode blind 0 = encode blind 3 := by decide
example : code chain 0 ≠ code chain 1 := by decide
example : next chain 0 (encode chain 1) = encode chain 2 := by decide
example : read chain 0 (next chain 0 (encode chain 2)) = chain.read 0 3 := by
  rw [next_commutes, read_commutes]
  rfl
example : read chain 1 (run chain [0, 0] (encode chain 0)) = chain.read 1 2 := by
  rw [every_future_reader_commutes]
  rfl
example : execute chain [0, 1] 0 = 0 := by decide
example : execute chain [1, 0] 0 = 1 := by decide
example : execute chain [0, 1] 0 ≠ execute chain [1, 0] 0 := by decide
example : (settle chain 0 (initialPairs chain)) = initialPairs chain := rfl
example : refine chain (settle chain 1 (initialPairs chain)) ≠ settle chain 1 (initialPairs chain) := by decide
example (fuel : Nat) (pairs : Finset (Pair chain)) (enough : pairs.card ≤ fuel) :
    refine chain (settle chain fuel pairs) = settle chain fuel pairs := settle_fixed chain fuel pairs enough

-- Current-only coding passes now but cannot implement the original next.
def coarse (state : State chain) : Bool := chain.read 0 state
example : coarse 1 = coarse 2 := by decide
example : ¬ Function.FactorsThrough (fun state : State chain => chain.read 0 (execute chain [0] state)) coarse := by
  intro factors
  have future := factors (show coarse 1 = coarse 2 by decide)
  change false = true at future
  cases future
example : ¬ (∃ candidateRead : Unit → Bool, ∀ state : State chain,
    candidateRead () = chain.read 0 state) := by
  rintro ⟨candidateRead, reads⟩
  have first := reads 0
  have second := reads 3
  have incompatible := first.symm.trans second
  change false = true at incompatible
  cases incompatible
example : Function.FactorsThrough (encode chain) (fun state : State chain => state) :=
  minimal chain id action chain.read (fun _ _ => rfl) (fun _ _ => rfl)
example : ∃! factor : Model chain → Bool, ∀ state,
    factor (encode chain state) = chain.read 0 (execute chain [0, 0] state) :=
  every_future_reader_unique_factorization chain [0, 0] 0

-- A new current signature that agrees now must be closed over every future.
example : encode blind 0 = encode blind 1 ∧ additional.read 0 = additional.read 1 := by decide
example : (0, 1) ∈ refinementInitial blind additional := by decide
example : additional.read (execute blind [0] 0) = additional.read (execute blind [0] 1) := by decide
example : additional.read (execute blind [0, 0] 0) ≠ additional.read (execute blind [0, 0] 1) := by decide
example : (0, 1) ∉ refinedKernel blind additional := by decide
example : refinedKernel blind additional = kernel (adjoin blind additional) :=
  incremental_matches_recomputed_minimum blind additional
example : (refinedKernel blind additional).card = 4 := by decide
example : encode (adjoin blind additional) 0 ≠ encode (adjoin blind additional) 1 :=
  actual_future_escape_separates blind additional 0 1 [0, 0] (by decide)
example : [code (adjoin blind additional) 0, code (adjoin blind additional) 1,
    code (adjoin blind additional) 2, code (adjoin blind additional) 3] = [0, 1, 2, 3] := by decide
example : (adjoin blind additional).action = blind.action := rfl
example : (adjoin blind additional).autonomous = blind.autonomous := rfl
example : (adjoin blind additional).initial = blind.initial := rfl
example (left right : State blind) :
    encode (adjoin blind additional) left = encode (adjoin blind additional) right ↔
      encode blind left = encode blind right ∧ ∀ word,
        additional.read (execute blind word left) = additional.read (execute blind word right) :=
  refined_model_future_exact blind additional left right
example (word : List (Letter chain)) (reader : Fin chain.readerCount) (state : State chain) :
    read chain reader (run chain word (encode chain state)) = chain.read reader (execute chain word state) :=
  every_future_reader_commutes chain word reader state

-- The full raw source field contract excludes zero inventories.
example (source : Source) : 0 < source.stateCount := Nat.lt_of_le_of_lt (Nat.zero_le _) source.initial.isLt
example (source : Source) : 0 < source.letterCount := Nat.lt_of_le_of_lt (Nat.zero_le _) source.autonomous.isLt
example (source : Source) : 0 < source.readerCount := Nat.lt_of_le_of_lt (Nat.zero_le _) source.reader.isLt
example (source : Source) (letter : Letter source) (state : State source) :
    (source.action letter state).val < source.stateCount := (source.action letter state).isLt

-- Existing fixed-process consumption retains exact inventory inverses.
open SaturationMonoid.NoIslandNoMagic.Consciousness.Representation
variable {N : WorldRelationNetwork} (process : SourceNativeLivingRootProcess N)
variable {Intervention : Type} (intervention : Intervention → process.State → process.State)
variable (system : IndependentConsumerSystem process.State)
variable {states letters readers : Nat}
variable (stateInventory : ConstructivePresentation (Fin states) process.State)
variable (letterInventory : ConstructivePresentation (Fin letters) (WholeRepresentation.Letter (Intervention := Intervention)))
variable (readerInventory : ConstructivePresentation (Fin readers) system.Consumer)
variable (reader : Fin readers) (readerEq : (consumer : system.Consumer) → DecidableEq (system.Output consumer))
example (word : List (Fin letters)) (state : Fin states) :
    stateInventory.forward (execute
        (fromProcess process intervention system stateInventory letterInventory readerInventory reader readerEq) word state) =
      WholeRepresentation.execute process intervention (word.map letterInventory.forward) (stateInventory.forward state) :=
  fromProcess_decoded_word process intervention system stateInventory letterInventory readerInventory reader readerEq word state
example (left right : process.State) :
    encode (fromProcess process intervention system stateInventory letterInventory readerInventory reader readerEq)
        (stateInventory.backward left) =
      encode (fromProcess process intervention system stateInventory letterInventory readerInventory reader readerEq)
        (stateInventory.backward right) ↔
      WholeRepresentation.modelPoint process intervention system left =
        WholeRepresentation.modelPoint process intervention system right :=
  computed_matches_source_future_model process intervention system stateInventory letterInventory readerInventory reader readerEq left right
example (runtime : LivingRuntimeState process) : type_of%
    (computed_model_and_actual_root_factorizes process intervention system
      stateInventory letterInventory readerInventory reader readerEq runtime) :=
  computed_model_and_actual_root_factorizes process intervention system
    stateInventory letterInventory readerInventory reader readerEq runtime
end FlyCNSFiniteMinimalCertification
'''

# Reuse the already audited type-and-value traversal, not another dependency policy.
tree = ast.parse((HERE / "build_dynamic_refinement_audit.py").read_text())
declaration = next(node for node in tree.body if isinstance(node, ast.Assign) and
                   any(isinstance(target, ast.Name) and target.id == "DEPENDENCIES" for target in node.targets))
DEPENDENCIES = ast.literal_eval(declaration.value).replace(
    "#dynamic_dependencies ", "#finite_minimal_dependencies ").replace(
    "DYNAMIC_", "FINITE_MINIMAL_").replace("FlyCNSDynamicCertification", "FlyCNSFiniteMinimalCertification")


def freeze():
    assert sha256(CANDIDATE.read_bytes()).hexdigest() == EXPECTED
    assert sha256((OWNED / "SourceRepresentation.lean").read_bytes()).hexdigest() == UPSTREAM


freeze()
if sys.argv[1:] == ["--runtime"]:
    OUT.mkdir(parents=True, exist_ok=True)
    target = OUT / "FiniteMinimalExecution.lean"
    source = CONTROLS.split("example : Nonempty", 1)[0]
    run = r'''
#eval do
  let rawStates := List.finRange 4
  let oldCodes := rawStates.map fun state => (code chain state).val
  let blindCodes := rawStates.map fun state => (code blind state).val
  let newCodes := rawStates.map fun state => (code (adjoin blind additional) state).val
  let nextCodes := rawStates.map fun state => (next chain 0 (encode chain state)).val.val
  let result := Lean.Json.mkObj [
    ("schema", Lean.toJson "flycns-finite-minimal-independent-execution/v1"),
    ("chain_codes", Lean.toJson oldCodes),
    ("blind_codes", Lean.toJson blindCodes),
    ("adjoined_codes", Lean.toJson newCodes),
    ("chain_autonomous_next_codes", Lean.toJson nextCodes),
    ("kernel_card", Lean.toJson (kernel chain).card),
    ("incremental_equals_recomputed", Lean.toJson (decide
      (refinedKernel blind additional = kernel (adjoin blind additional))))]
  IO.println result.compress
end FlyCNSFiniteMinimalCertification
'''
    target.write_text("import scratch.FlyCNS.SourceFiniteMinimalModel\nimport Lean\n"
                      "set_option autoImplicit false\n" + source + run)
    print(target)
elif sys.argv[1:] == ["--summarize"]:
    log = (OUT / "audit.log").read_text()
    assert "error:" not in log and "warning:" not in log
    entries, sizes = {}, {}
    for line in log.splitlines():
        if line.startswith("FINITE_MINIMAL_DEP\t"):
            _, root, name, user, module, kind = line.split("\t")
            entries.setdefault(root, []).append(dict(name=name, user=user, module=module, kind=kind))
        elif line.startswith("FINITE_MINIMAL_DONE\t"):
            _, root, count = line.split("\t")
            sizes[root] = int(count)
    assert set(entries) == set(sizes) == set(ROOTS)
    roots = {}
    for root, rows in entries.items():
        assert len(rows) == sizes[root] == len({row["name"] for row in rows})
        axioms = sorted({row["name"] for row in rows if row["kind"] == "axiom"})
        assert set(axioms) <= {"propext", "Classical.choice", "Quot.sound"}
        roots[root.removeprefix(PREFIX)] = dict(closure=sizes[root], axioms=axioms)
    summary = dict(schema="flycns-finite-minimal-full-type-value-audit/v1", candidate_sha256=EXPECTED,
                   representation_sha256=UPSTREAM, fresh_trust=0, warning_as_error=True,
                   independent_kernel_controls=CONTROLS.count("example "), checked_roots=len(ROOTS),
                   dependency_operator="ConstantInfo.getUsedConstantsAsSet: type + value",
                   unsafe_check="ConstantInfo.isUnsafe for every reached checked declaration", roots=roots)
    (OUT / "dependencies.json").write_text(json.dumps(entries, indent=2) + "\n")
    (HERE / "finite-minimal-audit-summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps({key: value for key, value in summary.items() if key != "roots"}))
else:
    OUT.mkdir(parents=True, exist_ok=True)
    target = OUT / "FiniteMinimalAudit.lean"
    checks = "\n".join(f"#print axioms {root}\n#finite_minimal_dependencies {root}" for root in ROOTS)
    target.write_text("import scratch.FlyCNS.SourceFiniteMinimalModel\n"
                      "import SaturationMonoid.LivingLawMaterialDependencyAuditTool\n"
                      "set_option autoImplicit false\nset_option maxHeartbeats 2000000\n" + CONTROLS + "\n" + DEPENDENCIES + "\n" + checks + "\n")
    print(target)
    print(f"kernel_controls={CONTROLS.count('example ')}; closures={len(ROOTS)}")
