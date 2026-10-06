import H0mework.Versions.AE.Physics.Bell.ReadoutPulseRealization
import Lean.Util.FoldConsts

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.Bell.PulseCertification

open ProofFreeRicherAnholonomicSource StageNineHolonomicField Stage9C.Revision
open ReadoutDetectorFiber ReadoutPulseRealization

noncomputable section

theorem generalNativeFeasibility (effect : CompactReadoutEffect) (spectrum : Spectrum) :
    Feasible effect spectrum ↔ Rates (background effect spectrum) (factor effect spectrum) :=
  feasible_iff_rates effect spectrum

theorem generalSquaredCoordinates (effect : CompactReadoutEffect) (spectrum : Spectrum) :
    Feasible effect spectrum ↔
      (effect.u ^ 2 + effect.z ^ 2) * (spectrum.bright + spectrum.dark) ^ 2 ≤
        (1 - effect.mu) ^ 2 * spectrum.gap ^ 2 ∧
      (effect.u ^ 2 + effect.z ^ 2) * (2 - spectrum.bright - spectrum.dark) ^ 2 ≤
        (1 + effect.mu) ^ 2 * spectrum.gap ^ 2 :=
  feasible_iff_squared effect spectrum

theorem generalWholeResponseBox (effect : CompactReadoutEffect) (worst actual : Spectrum)
    (feasible : Feasible effect worst) (bright : worst.bright ≤ actual.bright)
    (dark : actual.dark ≤ worst.dark) : Feasible effect actual :=
  feasible_monotone effect worst actual feasible bright dark

theorem generalGeneratedRates (effect : CompactReadoutEffect) (spectrum : Spectrum)
    (positive : 0 < effect.gain) (feasible : Feasible effect spectrum) :
    Rates (background effect spectrum) (factor effect spectrum) ∧
    0 < factor effect spectrum ∧ background effect spectrum < 1 ∧
    0 < efficiency (background effect spectrum) (factor effect spectrum) ∧
      efficiency (background effect spectrum) (factor effect spectrum) ≤ 1 :=
  ⟨realizationRates effect spectrum feasible, factor_positive effect spectrum positive,
    realization_background_lt_one effect spectrum positive feasible,
    realization_efficiency effect spectrum positive feasible⟩

theorem generalFaithfulAtomicResponse (effect : CompactReadoutEffect) (spectrum : Spectrum)
    (positive : 0 < effect.gain) :
    Realizes effect (background effect spectrum) (factor effect spectrum)
      (atomicEffect spectrum (realizationAxis effect positive)) :=
  pulse_realizes effect spectrum positive

theorem generalGeneratedEffectEquality (effect : CompactReadoutEffect) (spectrum : Spectrum)
    (positive : 0 < effect.gain) (feasible : Feasible effect spectrum) :
    realizedEffect effect spectrum positive feasible = effect :=
  realized_effect_eq effect spectrum positive feasible

theorem generalDistinctRealizers (effect : CompactReadoutEffect) (first second : Spectrum)
    (positive : 0 < effect.gain) (firstFeasible : Feasible effect first)
    (secondFeasible : Feasible effect second) (different : first ≠ second) :
    atomicEffect first (realizationAxis effect positive) ≠
      atomicEffect second (realizationAxis effect positive) ∧
    realizedEffect effect first positive firstFeasible = effect ∧
      realizedEffect effect second positive secondFeasible = effect :=
  two_spectra_same_effect effect first second positive firstFeasible secondFeasible different

theorem generalSameSourceCurrentNext (effect second : CompactReadoutEffect) (spectrum : Spectrum)
    (positive : 0 < effect.gain) (feasible : Feasible effect spectrum)
    (point : BasePoint) (plus x y : Bool) :
    effectSourceWeight (realizedEffect effect spectrum positive feasible) second plus point x y =
      effectSourceWeight effect second plus point x y ∧
    effectRuntimeProbability (realizedEffect effect spectrum positive feasible) second plus point x y =
      effectRuntimeProbability effect second plus point x y ∧
    effectNextProbability (realizedEffect effect spectrum positive feasible) second plus point x y =
      effectNextProbability effect second plus point x y := by
  rw [realized_effect_eq]
  exact ⟨rfl, rfl, rfl⟩

theorem generalBothSidesFullProbability (first second : CompactReadoutEffect)
    (firstSpectrum secondSpectrum : Spectrum) (firstPositive : 0 < first.gain)
    (secondPositive : 0 < second.gain) (firstFeasible : Feasible first firstSpectrum)
    (secondFeasible : Feasible second secondSpectrum) (plus x y : Bool) :
    effectProbability (realizedEffect first firstSpectrum firstPositive firstFeasible)
      (realizedEffect second secondSpectrum secondPositive secondFeasible) plus x y =
      effectProbability first second plus x y := by
  rw [realized_effect_eq, realized_effect_eq]

def controlEffect : CompactReadoutEffect :=
  ⟨0, 1 / 2, 0, by norm_num, by norm_num, by norm_num, by norm_num⟩

theorem controlGain : controlEffect.gain = 1 / 2 := by
  have norm : controlEffect.gain ^ 2 = (1 / 4 : ℝ) := by
    rw [CompactReadoutEffect.gain_sq]
    norm_num [controlEffect]
  nlinarith only [norm, controlEffect.gain_nonnegative]

def firstSpectrum : Spectrum := ⟨3 / 4, 1 / 4, by norm_num, by norm_num, by norm_num⟩
def secondSpectrum : Spectrum := ⟨9 / 10, 1 / 10, by norm_num, by norm_num, by norm_num⟩
def weakSpectrum : Spectrum := ⟨1 / 4, 0, by norm_num, by norm_num, by norm_num⟩

theorem firstFeasible : Feasible controlEffect firstSpectrum := by
  constructor <;> rw [controlGain] <;> norm_num [firstSpectrum, Spectrum.gap, controlEffect]

theorem secondFeasible : Feasible controlEffect secondSpectrum := by
  constructor <;> rw [controlGain] <;> norm_num [secondSpectrum, Spectrum.gap, controlEffect]

theorem differentSpectra : firstSpectrum ≠ secondSpectrum := by
  intro same
  have upper := congrArg Spectrum.bright same
  norm_num [firstSpectrum, secondSpectrum] at upper

theorem nonemptyDistinctRealizers :
    atomicEffect firstSpectrum (realizationAxis controlEffect (by rw [controlGain]; norm_num)) ≠
      atomicEffect secondSpectrum (realizationAxis controlEffect (by rw [controlGain]; norm_num)) ∧
    realizedEffect controlEffect firstSpectrum (by rw [controlGain]; norm_num) firstFeasible = controlEffect ∧
    realizedEffect controlEffect secondSpectrum (by rw [controlGain]; norm_num) secondFeasible = controlEffect :=
  generalDistinctRealizers _ _ _ (by rw [controlGain]; norm_num) firstFeasible secondFeasible differentSpectra

theorem weakSpectrumRejected : ¬ Feasible controlEffect weakSpectrum := by
  intro feasible
  have gap := feasible_gap_lower controlEffect weakSpectrum feasible
  rw [controlGain] at gap
  norm_num [weakSpectrum, Spectrum.gap] at gap

theorem originalLedger :
    HEq Runtime.event.wholeLedgerWriteBack (SpinPair.generatedEvolution Runtime.event.occurrence) :=
  sameOccurrenceReadoutEffectPrediction.activation.wholeLedger

theorem originalAnswerNext :
    Runtime.answerAndNext.nextCurrent = SpinPair.livingRoot.generatedNextCurrentAt Runtime.visit :=
  sameOccurrenceReadoutEffectPrediction.activation.answerNext

end
end SaturationMonoid.PhysicsCore.Stage10.Bell.PulseCertification

open Lean Elab Command in
set_option maxHeartbeats 0 in
run_cmd do
  let env := (← getEnv).setExporting false
  let paidText ← match (← IO.getEnv "BELL_PULSE_PAID_NAMES") with
    | some paidPath => IO.FS.readFile paidPath
    | none => pure "[]"
  let paidJson ← ofExcept (Json.parse paidText)
  let paidArray ← ofExcept paidJson.getArr?
  let mut paid : NameSet := {}
  for entry in paidArray do
    let spelling ← ofExcept entry.getStr?
    paid := paid.insert spelling.toName
  let candidates : Array Name := #[`H0mework.Versions.AE.Physics.Bell.ReadoutPulseRealization]
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
  let consumerPrefix := `SaturationMonoid.PhysicsCore.Stage10.Bell.PulseCertification
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
    `SaturationMonoid.PhysicsCore.Stage10.Bell.ReadoutPulseRealization.feasible_iff_rates,
    `SaturationMonoid.PhysicsCore.Stage10.Bell.ReadoutPulseRealization.feasible_iff_squared,
    `SaturationMonoid.PhysicsCore.Stage10.Bell.ReadoutPulseRealization.feasible_monotone,
    `SaturationMonoid.PhysicsCore.Stage10.Bell.ReadoutPulseRealization.pulse_realizes,
    `SaturationMonoid.PhysicsCore.Stage10.Bell.ReadoutPulseRealization.realized_effect_eq,
    `SaturationMonoid.PhysicsCore.Stage10.Bell.ReadoutPulseRealization.atomic_effect_injective,
    `SaturationMonoid.PhysicsCore.Stage10.Bell.ReadoutPulseRealization.two_spectra_same_effect,
    `SaturationMonoid.PhysicsCore.Stage10.Bell.PulseCertification.generalSameSourceCurrentNext,
    `SaturationMonoid.PhysicsCore.Stage10.Bell.PulseCertification.generalBothSidesFullProbability,
    `SaturationMonoid.PhysicsCore.Stage10.Bell.PulseCertification.nonemptyDistinctRealizers,
    `SaturationMonoid.PhysicsCore.Stage10.Bell.PulseCertification.weakSpectrumRejected]
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
  logInfo m!"BELL_PULSE_KERNEL_AUDIT|{report.compress}"
