import H0mework.Versions.AE.Physics.Bell.ReadoutDetectorFiber
import Lean.Util.FoldConsts

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.Bell.DetectorCertification

open ProofFreeRicherAnholonomicSource StageNineHolonomicField Stage9C.Revision
open ReadoutDetectorFiber

noncomputable section

theorem generalCompleteFiber (effect : CompactReadoutEffect) (d k : ℝ)
    (positive : 0 < effect.gain) :
    Fiber effect d k ↔ Rates d k ∧ ∃ atom : CompactReadoutEffect, Realizes effect d k atom :=
  fiber_iff_decomposition effect d k positive

theorem generalGeneratedAtomicResponse (effect : CompactReadoutEffect) (d k : ℝ)
    (fiber : Fiber effect d k) (positive : 0 < effect.gain) :
    Realizes effect d k (inverseAtom effect d k fiber (fiber.factor_positive positive)) :=
  inverse_atom_realizes effect d k fiber (fiber.factor_positive positive)

theorem generalJointDetectorAtomicBound (effect atom : CompactReadoutEffect) (d k : ℝ)
    (rates : Rates d k) (realizes : Realizes effect d k atom) (positive : 0 < effect.gain) :
    intrinsicLower effect ≤ efficiency d k * maxAtomic atom :=
  efficiency_atomic_lower effect atom d k rates realizes positive

theorem generalIndividualBounds (effect atom : CompactReadoutEffect) (d k : ℝ)
    (rates : Rates d k) (realizes : Realizes effect d k atom) (positive : 0 < effect.gain) :
    intrinsicLower effect ≤ efficiency d k ∧ intrinsicLower effect ≤ maxAtomic atom :=
  individual_lower effect atom d k rates realizes positive

theorem generalPolarityFreeDomain (effect atom : CompactReadoutEffect) (d k B G : ℝ)
    (rates : Rates d k) (realizes : Realizes effect d k atom)
    (positive : 0 < G) (gain : G ≤ effect.gain) (bias : |effect.mu| ≤ B) :
    domainLower B G ≤ efficiency d k * maxAtomic atom ∧ d ≤ (1 + B - G) / 2 :=
  domain_microhardware_bounds effect atom d k B G rates realizes positive gain bias

theorem generalForwardAreaBound (effect atom : CompactReadoutEffect) (d k B G areaSquared : ℝ)
    (rates : Rates d k) (realizes : Realizes effect d k atom)
    (positive : 0 < G) (gain : G ≤ effect.gain) (bias : |effect.mu| ≤ B)
    (forward : maxAtomic atom ≤ 7 * areaSquared / 4) :
    4 * domainLower B G / 7 ≤ efficiency d k * areaSquared :=
  domain_area_bound effect atom d k B G areaSquared rates realizes positive gain bias forward

theorem generalUniqueInverse (effect atom : CompactReadoutEffect) (d k : ℝ)
    (fiber : Fiber effect d k) (positive : 0 < k) (realizes : Realizes effect d k atom) :
    inverseAtom effect d k fiber positive = atom :=
  inverse_atom_unique effect atom d k fiber positive realizes

theorem generalRawResponseCap (effect atom : CompactReadoutEffect) (d k B cap : ℝ)
    (rates : Rates d k) (realizes : Realizes effect d k atom) (bias : |effect.mu| ≤ B)
    (nonnegative : 0 ≤ cap) (bounded : cap ≤ 1)
    (productCap : efficiency d k * maxAtomic atom ≤ cap) :
    effect.gain ≤ min 1 ((1 + B) * cap / (2 - cap)) :=
  raw_product_cap_gain effect atom d k B cap rates realizes bias nonnegative bounded productCap

theorem generalRawPulseAreaCap (effect atom : CompactReadoutEffect)
    (d k B etaUpper areaSquared areaUpper : ℝ)
    (rates : Rates d k) (realizes : Realizes effect d k atom)
    (background : d < 1) (bias : |effect.mu| ≤ B)
    (etaNonnegative : 0 ≤ etaUpper) (etaBounded : etaUpper ≤ 1)
    (etaCap : efficiency d k ≤ etaUpper) (areaNonnegative : 0 ≤ areaUpper)
    (areaCap : areaSquared ≤ areaUpper) (forward : maxAtomic atom ≤ 7 * areaSquared / 4) :
    effect.gain ≤ min 1 ((1 + B) * (etaUpper * min 1 (7 * areaUpper / 4)) /
      (2 - etaUpper * min 1 (7 * areaUpper / 4))) :=
  raw_detector_area_cap effect atom d k B etaUpper areaSquared areaUpper rates realizes
    background bias etaNonnegative etaBounded etaCap areaNonnegative areaCap forward

theorem generalRawSourceCurrentNext (atom second : CompactReadoutEffect) (d k : ℝ)
    (rates : Rates d k) (point : BasePoint) (plus x y : Bool) :
    effectSourceWeight (detectorEffect atom d k rates) second plus point x y =
      effectJointPolynomial (detectorEffect atom d k rates) second plus x y ∧
    effectRuntimeProbability (detectorEffect atom d k rates) second plus point x y =
      effectJointPolynomial (detectorEffect atom d k rates) second plus x y ∧
    effectNextProbability (detectorEffect atom d k rates) second plus point x y =
      effectJointPolynomial (detectorEffect atom d k rates) second plus x y :=
  ⟨(sameOccurrenceReadoutEffectPrediction.effectSourceBorn _ _ _ _ _ _).trans
      (sameOccurrenceReadoutEffectPrediction.effectJoint _ _ _ _ _),
    (sameOccurrenceReadoutEffectPrediction.effectCurrentBorn _ _ _ _ _ _).trans
      (sameOccurrenceReadoutEffectPrediction.effectJoint _ _ _ _ _),
    (sameOccurrenceReadoutEffectPrediction.effectNextBorn _ _ _ _ _ _).trans
      (sameOccurrenceReadoutEffectPrediction.effectJoint _ _ _ _ _)⟩

def pureAtomicEffect : CompactReadoutEffect :=
  ⟨0, 1, 0, by norm_num, by norm_num, by norm_num, by norm_num⟩

theorem pureAtomicGain : pureAtomicEffect.gain = 1 := by
  norm_num [CompactReadoutEffect.gain, pureAtomicEffect]

theorem positiveRates : Rates (1 / 10 : ℝ) (4 / 5 : ℝ) :=
  ⟨by norm_num, by norm_num, by norm_num⟩

def positiveEffect : CompactReadoutEffect :=
  detectorEffect pureAtomicEffect (1 / 10) (4 / 5) positiveRates

theorem positiveEffectGain : positiveEffect.gain = 4 / 5 := by
  rw [realizes_gain positiveEffect pureAtomicEffect (1 / 10) (4 / 5)
    (by norm_num) (detector_effect_realizes _ _ _ positiveRates), pureAtomicGain, mul_one]

theorem nonemptyPositiveFiber : Fiber positiveEffect (1 / 10) (4 / 5) :=
  (generalCompleteFiber _ _ _ (by rw [positiveEffectGain]; norm_num)).mpr
    ⟨positiveRates, pureAtomicEffect, detector_effect_realizes _ _ _ positiveRates⟩

theorem positiveResponseRejectsZeroFactor : ¬ Fiber positiveEffect (1 / 10) 0 := by
  intro fiber
  have contradiction := fiber.factor_positive (by rw [positiveEffectGain]; norm_num)
  exact (lt_irrefl 0) contradiction

theorem zeroRates : Rates (1 / 3 : ℝ) 0 := ⟨by norm_num, by norm_num, by norm_num⟩

theorem zeroFactorHiddenAtom (original other : CompactReadoutEffect) :
    Realizes (detectorEffect original (1 / 3) 0 zeroRates) (1 / 3) 0 other := by
  apply (zero_factor_iff _ _ _).mpr
  change (1 - 2 * (1 / 3 : ℝ) - 0 * (1 + original.mu) = 1 - 2 * (1 / 3 : ℝ)) ∧
    (-0 * original.u = 0) ∧ (-0 * original.z = 0)
  simp

theorem originalLedger :
    HEq Runtime.event.wholeLedgerWriteBack (SpinPair.generatedEvolution Runtime.event.occurrence) :=
  sameOccurrenceReadoutEffectPrediction.activation.wholeLedger

theorem originalAnswerNext :
    Runtime.answerAndNext.nextCurrent = SpinPair.livingRoot.generatedNextCurrentAt Runtime.visit :=
  sameOccurrenceReadoutEffectPrediction.activation.answerNext

end
end SaturationMonoid.PhysicsCore.Stage10.Bell.DetectorCertification

open Lean Elab Command in
set_option maxHeartbeats 0 in
run_cmd do
  let env := (← getEnv).setExporting false
  let paidText ← match (← IO.getEnv "BELL_DETECTOR_PAID_NAMES") with
    | some paidPath => IO.FS.readFile paidPath
    | none => pure "[]"
  let paidJson ← ofExcept (Json.parse paidText)
  let paidArray ← ofExcept paidJson.getArr?
  let mut paid : NameSet := {}
  for entry in paidArray do
    let spelling ← ofExcept entry.getStr?
    paid := paid.insert spelling.toName
  let candidates : Array Name := #[`H0mework.Versions.AE.Physics.Bell.ReadoutDetectorFiber]
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
  let consumerPrefix := `SaturationMonoid.PhysicsCore.Stage10.Bell.DetectorCertification
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
    `SaturationMonoid.PhysicsCore.Stage10.Bell.ReadoutDetectorFiber.fiber_iff_decomposition,
    `SaturationMonoid.PhysicsCore.Stage10.Bell.ReadoutDetectorFiber.efficiency_atomic_lower,
    `SaturationMonoid.PhysicsCore.Stage10.Bell.ReadoutDetectorFiber.domain_microhardware_bounds,
    `SaturationMonoid.PhysicsCore.Stage10.Bell.ReadoutDetectorFiber.domain_area_bound,
    `SaturationMonoid.PhysicsCore.Stage10.Bell.ReadoutDetectorFiber.raw_product_cap_gain,
    `SaturationMonoid.PhysicsCore.Stage10.Bell.ReadoutDetectorFiber.raw_detector_area_cap,
    `SaturationMonoid.PhysicsCore.Stage10.Bell.ReadoutDetectorFiber.inverse_atom_unique,
    `SaturationMonoid.PhysicsCore.Stage10.Bell.DetectorCertification.generalCompleteFiber,
    `SaturationMonoid.PhysicsCore.Stage10.Bell.DetectorCertification.generalRawSourceCurrentNext,
    `SaturationMonoid.PhysicsCore.Stage10.Bell.DetectorCertification.generalRawPulseAreaCap,
    `SaturationMonoid.PhysicsCore.Stage10.Bell.DetectorCertification.generalUniqueInverse,
    `SaturationMonoid.PhysicsCore.Stage10.Bell.DetectorCertification.nonemptyPositiveFiber,
    `SaturationMonoid.PhysicsCore.Stage10.Bell.DetectorCertification.zeroFactorHiddenAtom]
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
  logInfo m!"BELL_DETECTOR_KERNEL_AUDIT|{report.compress}"
