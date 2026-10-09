import H0mework.Versions.R9c73a630.Chemistry.LAlanineThermalRuntime.InstalledQuantumThermalLedger

/-! # The actual whole-ledger pair current receives the timed Hamiltonian step -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Root
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Installation
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Propagation.Runtime
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Source
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Producer
open Propagation.Interface Propagation.Producer Preparation Collision
open scoped ComplexOrder

noncomputable section

theorem timedPairInitial_held : HoldsCollision timedPairInitialTime := collision_next_held

theorem timedPairTarget_receives_actual_update (time : ℚ) :
    (thermalTargetStanding time).currentPair =
      timedPairCurrentUpdate time (thermalTargetStanding time).thermalHistory
        (thermalSourceStanding time).currentPair := rfl

theorem timedPair_initial_receives_collision :
    (thermalTargetStanding collisionCurrentTime).currentPair = some actualCollisionTarget.joint := by
  rw [timedPairTarget_receives_actual_update, timedPairCurrentUpdate, if_pos rfl,
    collisionTarget_eq_source_material, Option.map_some, actualCollisionTarget_eq_source]

theorem timedPair_no_prefilled_current :
    (thermalSourceStanding collisionCurrentTime).currentPair = none :=
  (thermalSourceStanding collisionCurrentTime).currentPairExact.trans timedPairCurrentAt_before

def actualTimedPairCurrent (time : ℚ) (held : HoldsCollision time) : JointMatrix Basis :=
  (thermalSourceStanding time).heldPair held

def actualTimedPairTarget (time : ℚ) (held : HoldsCollision time) : JointMatrix Basis :=
  (thermalTargetStanding time).heldPair ((holdsCollision_next time).mpr (Or.inr held))

theorem actualTimedPairCurrent_eq_source (time : ℚ) (held : HoldsCollision time) :
    actualTimedPairCurrent time held = rememberedJoint (timedPairAge time : ℝ) :=
  (thermalSourceStanding time).heldPair_exact held

theorem actualTimedPairTarget_eq_source (time : ℚ) (held : HoldsCollision time) :
    actualTimedPairTarget time held =
      rememberedJoint ((timedPairAge time : ℝ) + (nativeClockStep : ℝ)) := by
  unfold actualTimedPairTarget
  rw [NativeElectronicStandingAt.heldPair_exact, timedPairAge_next, Rat.cast_add]

theorem actualTimedPairCurrent_is_held (time : ℚ) (held : HoldsCollision time) :
    (thermalSourceStanding time).currentPair = some (actualTimedPairCurrent time held) :=
  (Option.some_get _).symm

theorem actualTimedPairTarget_is_held (time : ℚ) (held : HoldsCollision time) :
    (thermalTargetStanding time).currentPair = some (actualTimedPairTarget time held) :=
  (Option.some_get _).symm

theorem actualTimedPairTarget_is_next_current (time : ℚ) (held : HoldsCollision time) :
    actualTimedPairTarget time held = actualTimedPairCurrent (time + nativeClockStep)
      ((holdsCollision_next time).mpr (Or.inr held)) :=
  congrArg (fun standing : NativeElectronicStandingAt (time + nativeClockStep) =>
    standing.heldPair ((holdsCollision_next time).mpr (Or.inr held))) (Subsingleton.elim _ _)

/-- The equation is recovered from the writer on its actual received pair, not from the orbit readout. -/
theorem actualTimedPairTarget_generated (time : ℚ) (held : HoldsCollision time) :
    actualTimedPairTarget time held = timedPairNativeStep (actualTimedPairCurrent time held) := by
  have written := timedPairTarget_receives_actual_update time
  rw [actualTimedPairTarget_is_held time held, actualTimedPairCurrent_is_held time held,
    timedPairCurrentUpdate_receives time (held_not_initializing time held)] at written
  exact Option.some.inj written

theorem actualTimedPair_initial_current :
    actualTimedPairCurrent timedPairInitialTime timedPairInitial_held = actualCollisionTarget.joint := by
  rw [actualTimedPairCurrent_eq_source timedPairInitialTime timedPairInitial_held]
  simp only [timedPairAge, sub_self, Rat.cast_zero, rememberedJoint_initial,
    actualCollisionTarget_full_output.1]

theorem actualTimedPair_positive_normalized (time : ℚ) (held : HoldsCollision time) :
    (actualTimedPairCurrent time held).PosSemidef ∧ (actualTimedPairCurrent time held).trace = 1 ∧
    (actualTimedPairTarget time held).PosSemidef ∧ (actualTimedPairTarget time held).trace = 1 := by
  rw [actualTimedPairCurrent_eq_source, actualTimedPairTarget_eq_source]
  exact ⟨rememberedJoint_posSemidef _, rememberedJoint_trace _,
    rememberedJoint_posSemidef _, rememberedJoint_trace _⟩

theorem actualTimedPairTarget_positive_normalized (time : ℚ) (held : HoldsCollision time) :
    (actualTimedPairTarget time held).PosSemidef ∧ (actualTimedPairTarget time held).trace = 1 :=
  (actualTimedPair_positive_normalized time held).2.2

theorem timedPairTarget_receives_installed_effect (time : ℚ) (held : HoldsCollision time) :
    actualTimedPairTarget time held =
      (timedPairEffectAt (.nativeElectronicCurrent time) ⟨held⟩).targetJoint :=
  actualTimedPairTarget_generated time held

theorem timedPairTarget_history_immutable (time : ℚ) (held : HoldsCollision time) :
    (thermalTargetStanding time).thermalHistory = (thermalSourceStanding time).thermalHistory :=
  thermalTarget_carries_when_inactive time (held_not_initializing time held)

theorem timedPairTarget_literal_next (time : ℚ) :
    (thermalTargetStanding time).timeStamp = time + nativeClockStep :=
  (thermalTargetStanding time).timeStampExact

theorem timedPairRow_wholeLedger (time : ℚ) :
    (sourceRow (Root.emitted (.nativeElectronicCurrent time))).CommutesWithWorld :=
  nativeRow_commutes_with_wholeLedger _

theorem timedPairRow_claim_lineage_budget (time : ℚ) :
    type_of% (nativeRow_claim_lineage_budget (.nativeElectronicCurrent time) PUnit.unit) :=
  nativeRow_claim_lineage_budget _ PUnit.unit

theorem timedPairProjection_exact (stage : LAlanineStage) (active : timedPairProjectionActiveAt stage) :
    baseProjectionLaw.outcomeAt .timedPairEvolution (Root.emitted stage) =
      (.inl ⟨active, timedPairEffectAt stage active⟩ :
        SourceNativeProjectionFiberAt baseProjectionLaw .timedPairEvolution (Root.emitted stage)) := by
  cases stage <;> cases active
  rename_i time active
  have classified : baseProjectionLaw.classify .timedPairEvolution
      (Root.emitted (.nativeElectronicCurrent time)) =
      .inl (⟨active⟩ : timedPairProjectionActiveAt (.nativeElectronicCurrent time)) := by
    let : Decidable (HoldsCollision time) := Classical.propDecidable _
    change (if h : HoldsCollision time then Sum.inl (PLift.up h) else Sum.inr (PLift.up h)) = _
    rw [dif_pos active]
    rfl
  unfold SourceNativeProjectionLaw.outcomeAt
  rw [classified]
  rfl

def timedPairRuntimeFace (runtime : LivingRuntimeState electronicRuntimeProcess) :
    electronicRuntimeFacade.FaceAt runtime := siblingInstallation.embed .timedPairEvolution

theorem timedPairRuntimeFace_factorizes (runtime : LivingRuntimeState electronicRuntimeProcess) :
    type_of% (electronicRuntimeFacade.readoutAt_factorizes runtime (timedPairRuntimeFace runtime)) :=
  electronicRuntimeFace_factorizes runtime (timedPairRuntimeFace runtime)

theorem timedPairRuntimeEffect_is_installed (runtime : LivingRuntimeState electronicRuntimeProcess)
    (active : timedPairProjectionActiveAt runtime.state.current) :
    HEq (electronicRuntimeFacade.readoutAt runtime (timedPairRuntimeFace runtime))
      (.inl ⟨active, timedPairEffectAt runtime.state.current active⟩ :
        SourceNativeProjectionFiberAt baseProjectionLaw .timedPairEvolution
          (Root.emitted runtime.state.current)) :=
  (siblingInstallation.outcome_heq (Root.emitted runtime.state.current) .timedPairEvolution).trans
    (heq_of_eq (timedPairProjection_exact runtime.state.current active))

theorem timedPair_firstNative_inactive :
    IsEmpty (timedPairProjectionActiveAt electronicRuntimeFirstNative.state.current) :=
  ⟨fun active => collision_not_already_held active.down⟩

theorem timedPair_secondNative_active :
    Nonempty (timedPairProjectionActiveAt electronicRuntimeSecondNative.state.current) :=
  ⟨⟨collision_next_held⟩⟩

theorem timedPairRuntimeNext_current (runtime : LivingRuntimeState electronicRuntimeProcess)
    (active : timedPairProjectionActiveAt runtime.state.current) :
    runtime.tick.next.state.current =
      .nativeElectronicCurrent (timedPairEffectAt runtime.state.current active).targetTime := by
  change nextStage runtime.state.current = _
  generalize runtime.state.current = stage at active ⊢
  cases stage <;> cases active
  rfl

theorem timedPairRuntimeNext_active (runtime : LivingRuntimeState electronicRuntimeProcess)
    (active : timedPairProjectionActiveAt runtime.state.current) :
    Nonempty (timedPairProjectionActiveAt runtime.tick.next.state.current) := by
  change Nonempty (timedPairProjectionActiveAt (nextStage runtime.state.current))
  generalize runtime.state.current = stage at active ⊢
  cases stage <;> cases active
  rename_i time held
  exact ⟨⟨(holdsCollision_next time).mpr (Or.inr held)⟩⟩

theorem timedPair_offLattice_no_current :
    (thermalTargetStanding (collisionCurrentTime + nativeClockStep / 2)).currentPair = none := by
  rw [(thermalTargetStanding _).currentPairExact]
  simp only [timedPairCurrentAt, if_neg offLattice_next_not_held]

structure SourceInstalledLAlanineTimedPairCrown : Prop where
  previousQuantumThermal : SourceInstalledLAlanineQuantumThermalCrown
  initialReceivesActualCollision : type_of% timedPair_initial_receives_collision
  noPrefilledPair : type_of% timedPair_no_prefilled_current
  actualReceivedUpdate : ∀ time, type_of% (timedPairTarget_receives_actual_update time)
  actualGeneratedTarget : ∀ time held, type_of% (actualTimedPairTarget_generated time held)
  nextCurrentReceives : ∀ time held, type_of% (actualTimedPairTarget_is_next_current time held)
  actualCurrentInvariant : ∀ time held, type_of% (actualTimedPairCurrent_eq_source time held)
  actualTargetInvariant : ∀ time held, type_of% (actualTimedPairTarget_eq_source time held)
  fullPositiveNormalized : ∀ time held, type_of% (actualTimedPair_positive_normalized time held)
  immutableCollisionHistory : ∀ time held, type_of% (timedPairTarget_history_immutable time held)
  installedTarget : ∀ time held, type_of% (timedPairTarget_receives_installed_effect time held)
  sameWholeLedger : ∀ time, type_of% (timedPairRow_wholeLedger time)
  sameClaimLineageBudget : ∀ time, type_of% (timedPairRow_claim_lineage_budget time)
  literalNext : ∀ time, type_of% (timedPairTarget_literal_next time)
  completeFaceCoverage : ∀ runtime, type_of% (timedPairRuntimeFace_factorizes runtime)
  installedEffect : ∀ runtime active, type_of% (timedPairRuntimeEffect_is_installed runtime active)
  noPrematureEvolution : type_of% timedPair_firstNative_inactive
  sealedFirstPairCurrent : type_of% timedPair_secondNative_active
  continuedActivation : ∀ runtime active, type_of% (timedPairRuntimeNext_active runtime active)
  exactRuntimeNext : ∀ runtime active, type_of% (timedPairRuntimeNext_current runtime active)
  offLatticeNoPair : type_of% timedPair_offLattice_no_current

theorem sourceInstalledLAlanineTimedPair_crown : SourceInstalledLAlanineTimedPairCrown where
  previousQuantumThermal := sourceInstalledLAlanineQuantumThermal_crown
  initialReceivesActualCollision := timedPair_initial_receives_collision
  noPrefilledPair := timedPair_no_prefilled_current
  actualReceivedUpdate := timedPairTarget_receives_actual_update
  actualGeneratedTarget := actualTimedPairTarget_generated
  nextCurrentReceives := actualTimedPairTarget_is_next_current
  actualCurrentInvariant := actualTimedPairCurrent_eq_source
  actualTargetInvariant := actualTimedPairTarget_eq_source
  fullPositiveNormalized := actualTimedPair_positive_normalized
  immutableCollisionHistory := timedPairTarget_history_immutable
  installedTarget := timedPairTarget_receives_installed_effect
  sameWholeLedger := timedPairRow_wholeLedger
  sameClaimLineageBudget := timedPairRow_claim_lineage_budget
  literalNext := timedPairTarget_literal_next
  completeFaceCoverage := timedPairRuntimeFace_factorizes
  installedEffect := timedPairRuntimeEffect_is_installed
  noPrematureEvolution := timedPair_firstNative_inactive
  sealedFirstPairCurrent := timedPair_secondNative_active
  continuedActivation := timedPairRuntimeNext_active
  exactRuntimeNext := timedPairRuntimeNext_current
  offLatticeNoPair := timedPair_offLattice_no_current

end

end LAlanine40K2025.Thermal.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
