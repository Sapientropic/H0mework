import H0mework.Versions.AB.Chemistry.LAlaninePropagation.InstalledNativeElectronicRuntime

/-! # The actual thermal pair target in the original root's next ledger row -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Root
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Installation
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Propagation.Producer
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Propagation.Runtime
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Preparation
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Source
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Producer
open scoped ComplexOrder

noncomputable section

def thermalSourceStanding (time : ℚ) : NativeElectronicStandingAt time :=
  (sourceEntryAt (Root.emitted (.nativeElectronicCurrent time))).2

/-- No replacement target: this is the compiler-selected whole-ledger entry. -/
def thermalTargetStanding (time : ℚ) : NativeElectronicStandingAt (time + nativeClockStep) :=
  (nativeCompiledSourceRow (.nativeElectronicCurrent time)).targetEntry.2

theorem thermalTarget_receives_actual_update (time : ℚ) :
    (thermalTargetStanding time).thermalHistory =
      collisionHistoryUpdate time (thermalSourceStanding time).density
        (thermalSourceStanding time).thermalHistory := by
  rfl

theorem thermalTarget_carries_when_inactive (time : ℚ) (inactive : time ≠ collisionCurrentTime) :
    (thermalTargetStanding time).thermalHistory = (thermalSourceStanding time).thermalHistory := by
  rw [thermalTarget_receives_actual_update]
  exact collisionHistoryUpdate_carries _ _ _ inactive

theorem collisionSource_has_no_prefilled_target :
    (thermalSourceStanding collisionCurrentTime).thermalHistory = none :=
  (thermalSourceStanding collisionCurrentTime).thermalHistoryExact.trans collisionHistoryAt_current

theorem collisionTarget_receives_material :
    (thermalTargetStanding collisionCurrentTime).thermalHistory =
      some (collideCurrent (thermalSourceStanding collisionCurrentTime).density) := by
  rw [thermalTarget_receives_actual_update]
  simp only [collisionHistoryUpdate, ↓reduceIte]

theorem collisionTarget_eq_source_material :
    (thermalTargetStanding collisionCurrentTime).thermalHistory = some sourceCollisionMaterial := by
  rw [collisionTarget_receives_material, NativeElectronicStandingAt.density_eq_source]
  rfl

/-- Extract the whole material pair from the actual written target. -/
def actualCollisionTarget : ThermalCollisionMaterial :=
  (thermalTargetStanding collisionCurrentTime).thermalHistory.get
    (by rw [collisionTarget_eq_source_material]; rfl)

theorem actualCollisionTarget_eq_source : actualCollisionTarget = sourceCollisionMaterial := by
  unfold actualCollisionTarget
  simp only [collisionTarget_eq_source_material, Option.get_some]

theorem actualCollisionTarget_receives_installed_effect :
    actualCollisionTarget = thermalCollisionEffectAt
      (.nativeElectronicCurrent collisionCurrentTime) ⟨rfl⟩ := by
  rw [actualCollisionTarget_eq_source]
  change sourceCollisionMaterial =
    collideCurrent (thermalSourceStanding collisionCurrentTime).density
  exact congrArg collideCurrent (thermalSourceStanding collisionCurrentTime).density_eq_source.symm

theorem actualCollisionTarget_provenance :
    actualCollisionTarget.occurrenceTime = collisionCurrentTime ∧
    actualCollisionTarget.electronicArtifact = Propagation.Source.sourceArtifactSha256 ∧
    actualCollisionTarget.receivedDensity = (thermalSourceStanding collisionCurrentTime).density ∧
    actualCollisionTarget.preparedSystem = systemCurrent ∧
    actualCollisionTarget.preparedBath = bathCurrent ∧
    actualCollisionTarget.inverseTemperature = inverseTemperature ∧
    actualCollisionTarget.exchangeCosine = exchangeCosine ∧
    actualCollisionTarget.exchangeSine = exchangeSine := by
  rw [actualCollisionTarget_eq_source, NativeElectronicStandingAt.density_eq_source]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem actualCollisionTarget_full_output :
    actualCollisionTarget.joint = generatedJoint ∧
    actualCollisionTarget.system = generatedSystem ∧
    actualCollisionTarget.bath = generatedBath := by
  rw [actualCollisionTarget_eq_source]
  exact ⟨sourceCollisionMaterial_joint, sourceCollisionMaterial_system, sourceCollisionMaterial_bath⟩

theorem actualCollisionTarget_positive_normalized :
    actualCollisionTarget.joint.PosSemidef ∧ actualCollisionTarget.joint.trace = 1 ∧
    actualCollisionTarget.system.PosSemidef ∧ actualCollisionTarget.system.trace = 1 ∧
    actualCollisionTarget.bath.PosSemidef ∧ actualCollisionTarget.bath.trace = 1 := by
  rw [actualCollisionTarget_full_output.1, actualCollisionTarget_full_output.2.1,
    actualCollisionTarget_full_output.2.2]
  exact ⟨generatedJoint_posSemidef, generatedJoint_trace, generatedSystem_posSemidef,
    generatedSystem_trace, generatedBath_posSemidef, generatedBath_trace⟩

theorem actualCollisionTarget_heat_balance :
    (Collision.energy energyHamiltonian actualCollisionTarget.system -
      Collision.energy energyHamiltonian actualCollisionTarget.preparedSystem) +
    (Collision.energy energyHamiltonian actualCollisionTarget.bath -
      Collision.energy energyHamiltonian actualCollisionTarget.preparedBath) = 0 := by
  rw [actualCollisionTarget_eq_source]
  exact generatedHeat_conserved

theorem thermalProjection_exact (stage : LAlanineStage)
    (active : thermalProjectionActiveAt stage) :
    baseProjectionLaw.outcomeAt .thermalCollision (Root.emitted stage) =
      (.inl ⟨active, thermalCollisionEffectAt stage active⟩ :
        SourceNativeProjectionFiberAt baseProjectionLaw .thermalCollision (Root.emitted stage)) := by
  cases stage <;> cases active
  rename_i time active
  have classified : baseProjectionLaw.classify .thermalCollision
      (Root.emitted (.nativeElectronicCurrent time)) =
      .inl (⟨active⟩ : thermalProjectionActiveAt (.nativeElectronicCurrent time)) := by
    let : Decidable (time = collisionCurrentTime) := Classical.propDecidable _
    change (if h : time = collisionCurrentTime then Sum.inl (PLift.up h)
      else Sum.inr (PLift.up h)) = _
    rw [dif_pos active]
    rfl
  unfold SourceNativeProjectionLaw.outcomeAt
  rw [classified]
  rfl

def thermalRuntimeFace (runtime : LivingRuntimeState electronicRuntimeProcess) :
    electronicRuntimeFacade.FaceAt runtime := siblingInstallation.embed .thermalCollision

theorem thermalRuntimeEffect_is_installed (runtime : LivingRuntimeState electronicRuntimeProcess)
    (active : thermalProjectionActiveAt runtime.state.current) :
    HEq (electronicRuntimeFacade.readoutAt runtime (thermalRuntimeFace runtime))
      (.inl ⟨active, thermalCollisionEffectAt runtime.state.current active⟩ :
        SourceNativeProjectionFiberAt baseProjectionLaw .thermalCollision
          (Root.emitted runtime.state.current)) :=
  (siblingInstallation.outcome_heq (Root.emitted runtime.state.current) .thermalCollision).trans
    (heq_of_eq (thermalProjection_exact runtime.state.current active))

theorem thermalRuntimeFace_factorizes (runtime : LivingRuntimeState electronicRuntimeProcess) :
    type_of% (electronicRuntimeFacade.readoutAt_factorizes runtime (thermalRuntimeFace runtime)) :=
  electronicRuntimeFace_factorizes runtime (thermalRuntimeFace runtime)

theorem thermal_firstNative_active :
    Nonempty (thermalProjectionActiveAt electronicRuntimeFirstNative.state.current) :=
  ⟨⟨rfl⟩⟩

theorem thermal_secondNative_inactive :
    IsEmpty (thermalProjectionActiveAt electronicRuntimeSecondNative.state.current) := by
  constructor
  rintro ⟨active⟩
  change collisionCurrentTime + nativeClockStep = collisionCurrentTime at active
  have hp := nativeClockStep_positive
  linarith

theorem thermalTarget_literalNext (time : ℚ) :
    (thermalTargetStanding time).timeStamp = time + nativeClockStep :=
  (thermalTargetStanding time).timeStampExact

theorem collisionRow_claim_lineage_budget :
    type_of% (nativeRow_claim_lineage_budget (.nativeElectronicCurrent collisionCurrentTime) PUnit.unit) :=
  nativeRow_claim_lineage_budget _ PUnit.unit

theorem collisionRow_wholeLedger :
    (sourceRow (Root.emitted (.nativeElectronicCurrent collisionCurrentTime))).CommutesWithWorld :=
  nativeRow_commutes_with_wholeLedger _

theorem thermal_offLattice_no_history :
    (thermalTargetStanding (collisionCurrentTime + nativeClockStep / 2)).thermalHistory = none := by
  rw [(thermalTargetStanding _).thermalHistoryExact]
  simp [collisionHistoryAt, offLattice_next_not_held]

theorem thermal_no_free_bath_reset :
    (thermalTargetStanding (collisionCurrentTime + nativeClockStep)).thermalHistory =
      (thermalSourceStanding (collisionCurrentTime + nativeClockStep)).thermalHistory := by
  apply thermalTarget_carries_when_inactive
  have hp := nativeClockStep_positive
  intro he
  linarith

theorem thermal_no_fresh_collision_at_second_current :
    (thermalTargetStanding (collisionCurrentTime + nativeClockStep)).thermalHistory ≠
      some (collideCurrent (thermalSourceStanding (collisionCurrentTime + nativeClockStep)).density) := by
  have held := (holdsCollision_next (collisionCurrentTime + nativeClockStep)).mpr
    (Or.inr collision_next_held)
  have stored : (thermalTargetStanding (collisionCurrentTime + nativeClockStep)).thermalHistory =
      some sourceCollisionMaterial := by
    rw [(thermalTargetStanding _).thermalHistoryExact]
    simp [collisionHistoryAt, held]
  intro reset
  have materialEq := Option.some.inj (stored.symm.trans reset)
  have densityEq := congrArg ThermalCollisionMaterial.receivedDensity materialEq
  change Propagation.Dynamics.densityEvolution Propagation.Source.electronicSource
      (collisionCurrentTime : ℝ) =
    (thermalSourceStanding (collisionCurrentTime + nativeClockStep)).density at densityEq
  rw [NativeElectronicStandingAt.density_eq_source, Rat.cast_add] at densityEq
  exact nativeElectronicStep_changes (collisionCurrentTime : ℝ) densityEq.symm

structure SourceInstalledLAlanineThermalCollisionCrown : Prop where
  previousNativeRuntime : SourceInstalledLAlanineNativeElectronicRuntimeCrown
  sourceNoPrefilledTarget : type_of% collisionSource_has_no_prefilled_target
  actualRowUpdate : ∀ time, type_of% (thermalTarget_receives_actual_update time)
  sameInstalledMaterial : type_of% actualCollisionTarget_receives_installed_effect
  actualMaterialProvenance : type_of% actualCollisionTarget_provenance
  fullMaterialTarget : type_of% actualCollisionTarget_full_output
  positiveNormalizedTarget : type_of% actualCollisionTarget_positive_normalized
  heatConservation : type_of% actualCollisionTarget_heat_balance
  entropyProduction : type_of% collisionPopulation_clausius
  sameWholeLedger : type_of% collisionRow_wholeLedger
  sameClaimLineageBudget : type_of% collisionRow_claim_lineage_budget
  literalNext : ∀ time, type_of% (thermalTarget_literalNext time)
  completeFaceCoverage : ∀ runtime, type_of% (thermalRuntimeFace_factorizes runtime)
  installedEffect : ∀ runtime active, type_of% (thermalRuntimeEffect_is_installed runtime active)
  firstNativeActive : type_of% thermal_firstNative_active
  noRepeatedActivation : type_of% thermal_secondNative_inactive
  noFreeBathReset : type_of% thermal_no_free_bath_reset
  noFreshCollision : type_of% thermal_no_fresh_collision_at_second_current
  offLatticeNoReceipt : type_of% thermal_offLattice_no_history

theorem sourceInstalledLAlanineThermalCollision_crown : SourceInstalledLAlanineThermalCollisionCrown where
  previousNativeRuntime := sourceInstalledLAlanineNativeElectronicRuntime_crown
  sourceNoPrefilledTarget := collisionSource_has_no_prefilled_target
  actualRowUpdate := thermalTarget_receives_actual_update
  sameInstalledMaterial := actualCollisionTarget_receives_installed_effect
  actualMaterialProvenance := actualCollisionTarget_provenance
  fullMaterialTarget := actualCollisionTarget_full_output
  positiveNormalizedTarget := actualCollisionTarget_positive_normalized
  heatConservation := actualCollisionTarget_heat_balance
  entropyProduction := collisionPopulation_clausius
  sameWholeLedger := collisionRow_wholeLedger
  sameClaimLineageBudget := collisionRow_claim_lineage_budget
  literalNext := thermalTarget_literalNext
  completeFaceCoverage := thermalRuntimeFace_factorizes
  installedEffect := thermalRuntimeEffect_is_installed
  firstNativeActive := thermal_firstNative_active
  noRepeatedActivation := thermal_secondNative_inactive
  noFreeBathReset := thermal_no_free_bath_reset
  noFreshCollision := thermal_no_fresh_collision_at_second_current
  offLatticeNoReceipt := thermal_offLattice_no_history

end

end LAlanine40K2025.Thermal.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
