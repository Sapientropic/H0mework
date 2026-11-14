"""Independent frozen dynamic-refinement kernel and type/value audit."""

from hashlib import sha256
import json
from pathlib import Path
import re
import sys

HERE = Path(__file__).resolve().parent
OWNED = HERE.parent
OUT = HERE / ".cache" / "dynamic-refinement-audit"
PREFIX = "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.FlyCNS.BodyFullDynamicRefinement."
EXPECTED = {
    "BodyFullDynamicRefinement.lean": "06409e689fffd99b5ca6bff30ee43ee3cc7968b8b2c8ce1ff71c2a549b14c6d2",
    "full_dynamic_refinement.py": "e695cf792da4d216060f2264efee0d28b7fa8f57b428d562a5492d597aa69a29",
}
UPSTREAM = {
    "SourceBodyFullIO.lean": "994f26f8b180a133ad273f7bc472b4569c6c70125d197eec42f6c5450b19d5f4",
    "BodyFullPackedIO.lean": "67201db7740f2e1fee74e75eb9113071487158291c03c3b71faf8ce9e61a1c76",
}
ROOTS = [PREFIX + match.group(1) for match in re.finditer(
    r"^(?:def|theorem|structure|abbrev|inductive)\s+([A-Za-z][A-Za-z0-9_.]*)",
    (OWNED / "BodyFullDynamicRefinement.lean").read_text(), re.MULTILINE)]

CONTROLS = r'''
namespace FlyCNSDynamicCertification
open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.FlyCNS
open BodyFullDynamicRefinement BodyFullPackedIO RepresentationIO
open SaturationMonoid.NoIslandNoMagic.Consciousness.Representation

variable (material : BodyFullIO.Material)
def literal : WordImage := ⟨⟨#[0, 255, 128, 0]⟩, 128, 1, 4⟩
def image : Image material := ⟨Vector.replicate material.count literal,
  Vector.replicate 4 ⟨#[]⟩, ⟨#[]⟩, 0⟩
def laterVisit : Image material := { image material with visit := 1 }
def laterHeader : Image material := { image material with header := ⟨#[1]⟩ }
def widerWord : Image material := { image material with words :=
    (Vector.replicate material.count { literal with width := 8 }) }
def changedBytes : Image material := { image material with words :=
    (Vector.replicate material.count { literal with bytes := ⟨#[0, 254, 128, 0]⟩ }) }

example : coordinateRead (.visit : Coordinate material) (image material) = .visit 0 := rfl
example : coordinateRead (.visit : Coordinate material) (laterVisit material) = .visit 1 := rfl
example : coordinateRead (.visit : Coordinate material) (image material) ≠
    coordinateRead .visit (laterVisit material) := by
  change Datum.visit 0 ≠ Datum.visit 1
  decide
example : coordinateRead (.header : Coordinate material) (image material) ≠
    coordinateRead .header (laterHeader material) := by
  change Datum.bytes ⟨#[]⟩ ≠ Datum.bytes ⟨#[1]⟩
  decide
example (field : Fin material.count) :
    coordinateRead (.word field) (image material) ≠ coordinateRead (.word field) (widerWord material) := by
  simp [coordinateRead, image, widerWord, literal, Vector.get]
example (field : Fin material.count) :
    coordinateRead (.word field) (image material) ≠ coordinateRead (.word field) (changedBytes material) := by
  simp [coordinateRead, image, changedBytes, literal, Vector.get]
example : (.visit : Coordinate material) ∈ sourceBasis material := by simp [sourceBasis]
example : (.header : Coordinate material) ∉ sourceBasis material := by simp [sourceBasis]
example (field : Fin 4) : (.backend field : Coordinate material) ∉ sourceBasis material := by simp [sourceBasis]
example : view ([] : List (Coordinate material)) (image material) = [] := rfl
example : view [.visit] (image material) = [.visit 0] := rfl
example : view [.visit] (image material) ≠ view [.visit] (laterVisit material) := by
  change [Datum.visit 0] ≠ [Datum.visit 1]
  decide
example : view [.visit] (image material) = view [.visit] (widerWord material) := rfl
example : view [.visit] (image material) = view [.visit] (laterHeader material) := rfl
example : findOrigin ([] : List (Coordinate material)) (image material) (laterVisit material)
    [] (fun _ member => False.elim (by simp at member)) = none := rfl
example : (findOrigin ([] : List (Coordinate material)) (image material) (laterVisit material)
    [.visit] (by intro value member; simp only [List.mem_singleton] at member; subst value; simp [sourceBasis])).map
      (fun origin => origin.coordinate) = some .visit := by
  simp [findOrigin, coordinateRead, image, laterVisit]
example : findOrigin [.visit] (image material) (laterVisit material)
    [.visit] (by intro value member; simp only [List.mem_singleton] at member; subst value; simp [sourceBasis]) = none := by
  simp [findOrigin]
example : findOrigin ([] : List (Coordinate material)) (image material) (image material)
    [.visit] (by intro value member; simp only [List.mem_singleton] at member; subst value; simp [sourceBasis]) = none := by
  simp [findOrigin]
example (old added : List (Coordinate material)) :
    (view (old ++ added) (image material)).take old.length = view old (image material) :=
  view_append_old old added _
example (old added : List (Coordinate material)) (left right : Image material)
    (same : view (old ++ added) left = view (old ++ added) right) : view old left = view old right :=
  refined_preserves_old_kernel old added left right same
example (plan : List (Coordinate material)) : FaceKernelExactAt (viewConsumers plan) (view plan) :=
  view_kernel_exact plan
example (plan : List (Coordinate material)) :
    refinedFace (view plan) (sourceCoordinateReadout .visit) (image material) ≠
      refinedFace (view plan) (sourceCoordinateReadout .visit) (laterVisit material) :=
  source_coordinate_adjoin_does_not_merge plan .visit _ _ (by
    change Datum.visit 0 ≠ Datum.visit 1
    decide)
example (plan : List (Coordinate material)) :
    FaceKernelExactAt ((viewConsumers plan).adjoin (sourceCoordinateReadout .visit))
      (refinedFace (view plan) (sourceCoordinateReadout .visit)) := adjoined_source_coordinate_exact plan .visit

variable (root : BodyFullIO.IORoot)
example (branch : Branch root) (plan : List (Coordinate root.fixedSource.material)) :
    detectEscape root plan branch branch = none := by simp [detectEscape]
example (plan : List (Coordinate root.fixedSource.material)) (current : BodyFullIO.Current root.fixedSource.material) :
    (represent root plan current).image = capture current := representation_complete root plan current
example {plan : List (Coordinate root.fixedSource.material)} {left right : Branch root}
    (escape : EscapeAt root plan left right) :
    ¬ Function.FactorsThrough (futureView root plan).read (beforeView root plan) :=
  actual_future_cannot_factor root escape
example {plan : List (Coordinate root.fixedSource.material)} {left right : Branch root}
    (escape : EscapeAt root plan left right) :
    view escape.nextPlan (capture left.1) ≠ view escape.nextPlan (capture right.1) :=
  escape_nextPlan_separates root escape
example {plan : List (Coordinate root.fixedSource.material)} {left right : Branch root}
    (escape : EscapeAt root plan left right) (packet : Packet root.fixedSource.material) :
    (refineRepresentation root escape packet).image = unpack packet := rfl
example {before : Representation root} (step : StepAt root before) :
    step.next.image = capture step.actual.generated.next := execute_whole_current root step
example {before : Representation root} (step : StepAt root before) :
    capture step.actual.generated.occurrence.1 = before.image := execute_source_support root step
example {before : Representation root} (first : StepAt root before) (second : StepAt root first.next) :
    second.actual.decoded.current = first.actual.generated.next := continuation_current root first second
example {before : Representation root} (first : StepAt root before) (second : StepAt root first.next)
    (reader : BodyFullIO.Current root.fixedSource.material → Nat) :
    reader second.actual.decoded.current = reader first.actual.generated.next :=
  continuation_every_reader root reader first second
example (before : Representation root) : (TraceAt.done before : TraceAt root before 0).final = before := rfl
example {before : Representation root} {fuel : Nat} (trace : TraceAt root before fuel) :
    trace.final.residual = trace.packed.final := finite_autonomous_words_exact root trace
end FlyCNSDynamicCertification
'''

DEPENDENCIES = r'''
open Lean Elab Command
elab "#dynamic_dependencies " identifier:ident : command => do
  let root ← liftCoreM <| resolveGlobalConstNoOverload identifier
  let env ← getEnv
  let mut pending : List Name := [root]
  let mut visited : NameSet := {}
  while !pending.isEmpty do
    let name := pending.head!
    pending := pending.tail!
    if !visited.contains name then
      visited := visited.insert name
      let some info := env.checked.get.find? name
        | throwError "missing checked dependency {name}"
      if info.isUnsafe then throwError "unsafe dependency {root} -> {name}"
      let userName := privateToUserName name
      let userString := userName.toString
      let moduleName := (env.getModuleFor? name).map toString |>.getD "<local>"
      if userString.startsWith "FlyCNSDynamicCertification" || userString.contains "sorryAx" ||
          moduleName.contains "Certification" || moduleName.contains "Controls" then
        throwError "control or sorry dependency {root} -> {name}"
      let kind := match info with
        | .axiomInfo _ => "axiom"
        | .defnInfo _ => "def"
        | .thmInfo _ => "theorem"
        | .opaqueInfo _ => "opaque"
        | .quotInfo _ => "quotient"
        | _ => "type"
      if kind == "axiom" && name != ``propext && name != ``Classical.choice && name != ``Quot.sound then
        throwError "unauthorized axiom {root} -> {name}"
      logInfo m!"DYNAMIC_DEP\t{root}\t{name}\t{userName}\t{moduleName}\t{kind}"
      pending := info.getUsedConstantsAsSet.toArray.toList ++ pending
  logInfo m!"DYNAMIC_DONE\t{root}\t{visited.toArray.size}"
'''


def freeze():
    for name, expected in (EXPECTED | UPSTREAM).items():
        assert sha256((OWNED / name).read_bytes()).hexdigest() == expected, name


freeze()
if sys.argv[1:] == ["--summarize"]:
    log = (OUT / "audit.log").read_text()
    assert "error:" not in log and "warning:" not in log
    entries, sizes = {}, {}
    for line in log.splitlines():
        if line.startswith("DYNAMIC_DEP\t"):
            _, root, name, user, module, kind = line.split("\t")
            entries.setdefault(root, []).append(dict(name=name, user=user, module=module, kind=kind))
        elif line.startswith("DYNAMIC_DONE\t"):
            _, root, count = line.split("\t")
            sizes[root] = int(count)
    assert set(entries) == set(sizes) == set(ROOTS)
    roots = {}
    for root, rows in entries.items():
        assert len(rows) == sizes[root] == len({row["name"] for row in rows})
        axioms = sorted({row["name"] for row in rows if row["kind"] == "axiom"})
        assert set(axioms) <= {"propext", "Classical.choice", "Quot.sound"}
        roots[root.removeprefix(PREFIX)] = dict(closure=sizes[root], axioms=axioms)
    assert (OUT / "candidate.log").read_bytes() == b""
    summary = dict(schema="flycns-dynamic-refinement-full-type-value-audit/v1", frozen_candidate_sha256=EXPECTED,
                   frozen_upstream_sha256=UPSTREAM, fresh_trust=0, warning_as_error=True,
                   independent_kernel_controls=CONTROLS.count("example "), checked_roots=len(ROOTS),
                   dependency_operator="ConstantInfo.getUsedConstantsAsSet: type + value",
                   unsafe_check="ConstantInfo.isUnsafe for every reached checked declaration", roots=roots)
    (OUT / "dependencies.json").write_text(json.dumps(entries, indent=2) + "\n")
    (HERE / "dynamic-refinement-audit-summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps({key: value for key, value in summary.items() if key != "roots"}))
else:
    OUT.mkdir(parents=True, exist_ok=True)
    target = OUT / "DynamicRefinementAudit.lean"
    checks = "\n".join(f"#print axioms {root}\n#dynamic_dependencies {root}" for root in ROOTS)
    target.write_text("import scratch.FlyCNS.BodyFullDynamicRefinement\n"
                      "import SaturationMonoid.LivingLawMaterialDependencyAuditTool\n"
                      "set_option autoImplicit false\n" + CONTROLS + "\n" + DEPENDENCIES + "\n" + checks + "\n")
    print(target)
    print(f"kernel_controls={CONTROLS.count('example ')}; closures={len(ROOTS)}")
