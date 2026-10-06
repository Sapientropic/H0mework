import H0mework.Versions.AE.Physics.Bell.ReadoutAnchors
import Lean.Util.FoldConsts

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.Bell.AnchorsCertification

open ProofFreeRicherAnholonomicSource StageNineHolonomicField Stage9C.Revision
open ReadoutIdentification ReadoutAnchors

noncomputable section

theorem generalBornProbe (family : SettingFamily) (a outcome : Bool) (r : BlochProbe) :
    0 ≤ r.probability (family.alice a) outcome ∧
    (∑ x : Bool, r.probability (family.alice a) x) = 1 ∧
    (∑ x : Bool, sign x * r.probability (family.alice a) x) = r.response (family.alice a) :=
  ⟨r.probability_nonnegative _ _, r.probability_normalized _, r.probability_mean _⟩

theorem generalRecovery (family : SettingFamily) (regular : Regular family)
    (r₀ r₁ : BlochProbe) (independent : determinant r₀ r₁ ≠ 0) :
    reconstruct family.recovered r₀ r₁ (r₀.response (family.alice false))
      (r₁.response (family.alice false)) = familyCoordinates family :=
  reconstruct_eq family regular r₀ r₁ independent

theorem generalSameLawAnchored (original other : SettingFamily) (regular : Regular original)
    (same : SameLaw other original) (r₀ r₁ : BlochProbe)
    (independent : determinant r₀ r₁ ≠ 0)
    (first : r₀.response (other.alice false) = r₀.response (original.alice false))
    (second : r₁.response (other.alice false) = r₁.response (original.alice false)) :
    other = original :=
  same_law_two_probes_unique original other regular same r₀ r₁ independent first second

theorem generalOriginalOccurrence (original other : SettingFamily) (regular : Regular original)
    (same : SameLaw other original) (r₀ r₁ : BlochProbe)
    (independent : determinant r₀ r₁ ≠ 0)
    (first : r₀.response (other.alice false) = r₀.response (original.alice false))
    (second : r₁.response (other.alice false) = r₁.response (original.alice false))
    (point : BasePoint) (plus a b x y : Bool) :
    other = original ∧
    other.sourceProbability point plus a b x y = original.sourceProbability point plus a b x y ∧
    other.currentProbability point plus a b x y = original.currentProbability point plus a b x y ∧
    other.nextProbability point plus a b x y = original.nextProbability point plus a b x y :=
  anchored_same_occurrence original other regular same r₀ r₁ independent first second point plus a b x y

theorem generalSplitLawAnchored (original other : SettingFamily)
    (ax bx az bz s₀ s₁ : Bool) (regular : RegularAt original ax bx az bz)
    (same : SameLaw other original) (r₀ r₁ : BlochProbe)
    (independent : splitDeterminant original.recovered ax bx az bz s₀ s₁ r₀ r₁ ≠ 0)
    (first : r₀.response (other.alice s₀) = r₀.response (original.alice s₀))
    (second : r₁.response (other.alice s₁) = r₁.response (original.alice s₁)) :
    other = original :=
  same_law_split_probes_unique original other ax bx az bz s₀ s₁ regular same r₀ r₁ independent first second

theorem generalSourceSplitRecovery (family : SettingFamily) (ax bx az bz s₀ s₁ : Bool)
    (regular : RegularAt family ax bx az bz) (r₀ r₁ : BlochProbe)
    (independent : splitDeterminant family.recovered ax bx az bz s₀ s₁ r₀ r₁ ≠ 0) :
    reconstructSplit family.recovered ax bx az bz s₀ s₁ r₀ r₁
      (r₀.response (family.alice s₀)) (r₁.response (family.alice s₁)) = familyCoordinates family :=
  reconstruct_split_eq family ax bx az bz s₀ s₁ regular r₀ r₁ independent

theorem generalSignedScaleRecovery (family : SettingFamily) (s t : ℝ)
    (valid : AdmissibleScales family s t) (ax bx az bz s₀ s₁ : Bool)
    (regular : RegularAt (scaledFamily family s t valid) ax bx az bz)
    (r₀ r₁ : BlochProbe)
    (independent : splitDeterminant (scaledFamily family s t valid).recovered ax bx az bz s₀ s₁ r₀ r₁ ≠ 0) :
    reconstructSplit family.recovered ax bx az bz s₀ s₁ r₀ r₁
      (r₀.response ((scaledFamily family s t valid).alice s₀))
      (r₁.response ((scaledFamily family s t valid).alice s₁)) =
      familyCoordinates (scaledFamily family s t valid) := by
  have law := (same_law_iff_identified _ _).mp (scaled_same_law family s t valid)
  have recovered : (scaledFamily family s t valid).recovered = family.recovered := by
    rw [SettingFamily.recovered_eq_identified, family.recovered_eq_identified, law]
  rw [← recovered]
  exact generalSourceSplitRecovery _ ax bx az bz s₀ s₁ regular r₀ r₁ independent

def xProbe : BlochProbe := ⟨1, 0, by norm_num⟩
def zProbe : BlochProbe := ⟨0, 1, by norm_num⟩
def minusXProbe : BlochProbe := ⟨-1, 0, by norm_num⟩

theorem independentProbes : determinant xProbe zProbe = 1 := by
  norm_num [determinant, xProbe, zProbe]

theorem oppositeProbeSingular : determinant xProbe minusXProbe = 0 := by
  norm_num [determinant, xProbe, minusXProbe]

def xEffect : CompactReadoutEffect :=
  ⟨0, 1 / 4, 0, by norm_num, by norm_num, by norm_num, by norm_num⟩
def zEffect : CompactReadoutEffect :=
  ⟨0, 0, 1 / 4, by norm_num, by norm_num, by norm_num, by norm_num⟩
def diagonalEffect : CompactReadoutEffect :=
  ⟨0, 1 / 4, 1 / 4, by norm_num, by norm_num, by norm_num, by norm_num⟩
def poleFamily : SettingFamily :=
  ⟨fun a => if a then xEffect else zEffect, fun _ => diagonalEffect⟩

theorem splitPoleRegular : RegularAt poleFamily true false false false := by
  norm_num [RegularAt, poleFamily, xEffect, zEffect, diagonalEffect]

theorem splitPoleDeterminant :
    splitDeterminant poleFamily.recovered true false false false true false xProbe zProbe = 1 := by
  rw [poleFamily.recovered_eq_identified]
  norm_num [splitDeterminant, coefficientX, coefficientZ, relativeX, relativeZ,
    SettingFamily.identified, poleFamily, xEffect, zEffect, diagonalEffect, xProbe, zProbe]

theorem splitPoleRecovery :
    reconstructSplit poleFamily.recovered true false false false true false xProbe zProbe
      (xProbe.response (poleFamily.alice true)) (zProbe.response (poleFamily.alice false)) =
      familyCoordinates poleFamily :=
  generalSourceSplitRecovery _ _ _ _ _ _ _ splitPoleRegular _ _ (by rw [splitPoleDeterminant]; norm_num)

theorem originalLedger :
    HEq Runtime.event.wholeLedgerWriteBack (SpinPair.generatedEvolution Runtime.event.occurrence) :=
  sameOccurrenceIdentification.activation.wholeLedger

theorem originalAnswerNext :
    Runtime.answerAndNext.nextCurrent = SpinPair.livingRoot.generatedNextCurrentAt Runtime.visit :=
  sameOccurrenceIdentification.activation.answerNext

end
end SaturationMonoid.PhysicsCore.Stage10.Bell.AnchorsCertification

open Lean Elab Command in
set_option maxHeartbeats 0 in
run_cmd do
  let env := (← getEnv).setExporting false
  let paidText ← match (← IO.getEnv "BELL_ANCHORS_PAID_NAMES") with
    | some paidPath => IO.FS.readFile paidPath
    | none => pure "[]"
  let paidJson ← ofExcept (Json.parse paidText)
  let paidArray ← ofExcept paidJson.getArr?
  let mut paid : NameSet := {}
  for entry in paidArray do
    let spelling ← ofExcept entry.getStr?
    paid := paid.insert spelling.toName
  let candidates : Array Name := #[`H0mework.Versions.AE.Physics.Bell.ReadoutAnchors]
  let ownerOf := fun name : Name =>
    match env.getModuleIdxFor? name with
    | some index => env.allImportedModuleNames[index.toNat]!
    | none => env.mainModule
  let mut own : Array Name := #[]
  let mut compilerOnly : Array Name := #[]
  for module in candidates do
    let some candidateIndex := env.getModuleIdx? module | throwError "candidate module absent: {module}"
    for (name, moduleIndex) in env.const2ModIdx.toList do
      if moduleIndex == candidateIndex then
        if (env.find? name).isSome then own := own.push name
        else compilerOnly := compilerOnly.push name
  let consumerPrefix := `SaturationMonoid.PhysicsCore.Stage10.Bell.AnchorsCertification
  let consumers := env.constants.toList.toArray.filterMap fun (name, _) =>
    if consumerPrefix.isPrefixOf name then some name else none
  if own.isEmpty || consumers.isEmpty then throwError "empty candidate or independent consumer"
  let mut pending := own ++ consumers
  let mut index := 0
  let mut seen : NameSet := {}
  for name in pending do seen := seen.insert name
  let mut closure : Array Json := #[]
  let mut boundaries : Array Json := #[]
  while index < pending.size do
    let name := pending[index]!
    index := index + 1
    let some info := env.find? name | throwError "missing dependency: {name}"
    let kind := match info with
      | .axiomInfo _ => "axiom"
      | .defnInfo value => if value.safety == .safe then "definition" else "unsafe-definition"
      | .thmInfo _ => "theorem"
      | .opaqueInfo _ => "opaque"
      | .quotInfo _ => "quotient"
      | .inductInfo _ => "inductive"
      | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor"
    let dependencies := info.getUsedConstantsAsSet.toList.toArray
    let entry := Json.mkObj [("name", .str name.toString),
      ("module", .str (ownerOf name).toString), ("kind", .str kind),
      ("dependencies", .arr (dependencies.map fun dependency => .str dependency.toString))]
    if paid.contains name then boundaries := boundaries.push entry
    else
      closure := closure.push entry
      for dependency in dependencies do
        if !seen.contains dependency then
          seen := seen.insert dependency
          pending := pending.push dependency
  let publicNames : Array Name := #[
    `SaturationMonoid.PhysicsCore.Stage10.Bell.ReadoutAnchors.reconstruct_eq,
    `SaturationMonoid.PhysicsCore.Stage10.Bell.ReadoutAnchors.same_law_two_probes_unique,
    `SaturationMonoid.PhysicsCore.Stage10.Bell.ReadoutAnchors.reconstruct_split_eq,
    `SaturationMonoid.PhysicsCore.Stage10.Bell.ReadoutAnchors.same_law_split_probes_unique,
    `SaturationMonoid.PhysicsCore.Stage10.Bell.ReadoutAnchors.regular_at_scale_relation,
    `SaturationMonoid.PhysicsCore.Stage10.Bell.AnchorsCertification.generalSourceSplitRecovery,
    `SaturationMonoid.PhysicsCore.Stage10.Bell.AnchorsCertification.generalOriginalOccurrence,
    `SaturationMonoid.PhysicsCore.Stage10.Bell.AnchorsCertification.splitPoleDeterminant,
    `SaturationMonoid.PhysicsCore.Stage10.Bell.AnchorsCertification.oppositeProbeSingular]
  let mut mouths : Array Json := #[]
  for name in publicNames do
    let some info := env.find? name | throwError "missing public mouth: {name}"
    let pretty ← liftTermElabM <| Meta.ppExpr info.type
    mouths := mouths.push (Json.mkObj [("name", .str name.toString), ("type", .str pretty.pretty)])
  let report := Json.mkObj [
    ("candidate_modules", .arr (candidates.map fun name => .str name.toString)),
    ("imported_modules", .arr (env.allImportedModuleNames.map fun name => .str name.toString)),
    ("owned_declarations", .arr (own.map fun name => .str name.toString)),
    ("compiler_only_module_symbols", .arr (compilerOnly.map fun name => .str name.toString)),
    ("independent_consumers", .arr (consumers.map fun name => .str name.toString)),
    ("dependency_delta", .arr closure), ("paid_boundary", .arr boundaries),
    ("public_mouths", .arr mouths)]
  logInfo m!"BELL_ANCHORS_KERNEL_AUDIT|{report.compress}"
