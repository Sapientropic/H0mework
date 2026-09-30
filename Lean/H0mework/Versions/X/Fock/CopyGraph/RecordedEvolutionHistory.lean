import H0mework.Versions.X.Fock.CopyGraph.RecordedEvolutionSource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceRecordedEvolution

open SourceGeneratedAcquisitionMeasure SourceGeneratedAcquisitionContinuation SourceGeneratedJointClockGraph
open SourceGeneratedRuntimeHistoryProbability SourceGeneratedActionWords.Fock SourceGeneratedActionWords.Fock.Dynamic
open SourceOwnedObservationHistory
open SourceCopyProgram (Index)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
attribute [local instance] SourceCompleteGraph.completeUniform SourceCompleteGraph.completeMeasurable
  SourceCompleteGraph.completeBorel SourceCompleteGraph.completeT2 SourceFiniteCompleteGraph.windowMeasurable

def recovery (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    (steps : Nat) → SourceJointClockGraph.Carrier → FieldSpace (inventoryBound runtime + steps) (inventoryBound runtime + steps)
  | 0 => SourceColumnForcing.recovery runtime index
  | steps + 1 => step (inventoryBound runtime + steps)
      (SourceGraphLoss.advancedIndex (inventoryBound runtime) index steps) (recovery runtime index steps)

theorem seed_original (model : Nat) (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (target : SourceJointClockGraph.Carrier) :
    recovery runtime index 0 target = SourceCompleteGraph.recovery model runtime index 0 target := by
  change SourceColumnForcing.recovery runtime index target = _
  rw [SourceColumnForcing.recovery_source, SourceNormalInverse.recovery_source,
    SourceFiniteCompleteGraph.recovery_model model]
  rfl

theorem recovery_original (model : Nat) (runtime : LivingRuntimeState process)
    (index : Index (inventoryBound runtime)) (steps : Nat) (target : SourceJointClockGraph.Carrier) :
    recovery runtime index steps target = SourceCompleteGraph.recovery model runtime index steps target := by
  induction steps generalizing target with
  | zero => exact seed_original model runtime index target
  | succ steps previous =>
    have same : recovery runtime index steps = (SourceCompleteGraph.recovery model runtime index steps :
        SourceJointClockGraph.Carrier → FieldSpace (inventoryBound runtime + steps) (inventoryBound runtime + steps)) := funext previous
    rw [recovery, same, SourceCompleteGraph.recovery, SourceCompleteGraph.recovery_canonical]
    exact step_original model _ _ target

def residual (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (steps : Nat) (target : SourceJointClockGraph.Carrier) : SourceJointClockGraph.Carrier :=
  target - SourceCopyGraph.action (inventoryBound runtime + steps)
    (SourceGraphLoss.advancedIndex (inventoryBound runtime) index steps)
    (fieldRead (inventoryBound runtime + steps) (inventoryBound runtime + steps) (recovery runtime index steps target))

def birth (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (steps : Nat) (target : SourceJointClockGraph.Carrier) : SourceJointClockGraph.Carrier :=
  let h := innovation (inventoryBound runtime + steps)
    (SourceGraphLoss.advancedIndex (inventoryBound runtime) index steps) (recovery runtime index steps)
  (inner ℂ h target / ((‖h‖ ^ 2 : ℝ) : ℂ)) • h

theorem residual_original (model : Nat) (runtime : LivingRuntimeState process)
    (index : Index (inventoryBound runtime)) (steps : Nat) (target : SourceJointClockGraph.Carrier) :
    residual runtime index steps target = SourceCompleteGraph.residual model runtime index steps target := by
  unfold residual SourceCompleteGraph.residual
  rw [recovery_original model]

theorem birth_original (model : Nat) (runtime : LivingRuntimeState process)
    (index : Index (inventoryBound runtime)) (steps : Nat) (target : SourceJointClockGraph.Carrier) :
    birth runtime index steps target = SourceCompleteGraph.birthMap model runtime index steps target := by
  have same : recovery runtime index steps = (SourceCompleteGraph.recovery model runtime index steps :
      SourceJointClockGraph.Carrier → FieldSpace (inventoryBound runtime + steps) (inventoryBound runtime + steps)) :=
    funext (recovery_original model runtime index steps)
  rw [birth, SourceCompleteGraph.birthMap, same, SourceCompleteGraph.recovery_canonical,
    ← SourceCompleteGraph.old_read_original]
  simp only [innovation_original, ContinuousLinearMap.smulRight_apply, smul_apply]
  rw [div_eq_mul_inv, mul_comm]
  rfl

theorem history_energy (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (steps : Nat) (target : SourceJointClockGraph.Carrier) :
    ‖residual runtime index steps target‖ ^ 2 +
      ∑ stage ∈ Finset.range steps, ‖birth runtime index stage target‖ ^ 2 =
        ‖residual runtime index 0 target‖ ^ 2 := by
  simp_rw [residual_original 0, birth_original 0]
  exact SourceCompleteGraph.history_energy 0 runtime index steps target

theorem field_recovery (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (value : FieldSpace (inventoryBound runtime + steps) (inventoryBound runtime + steps)) :
    recovery runtime index steps (SourceCopyGraph.action (inventoryBound runtime + steps)
      (SourceGraphLoss.advancedIndex (inventoryBound runtime) index steps)
      (fieldRead (inventoryBound runtime + steps) (inventoryBound runtime + steps) value)) = value := by
  rw [recovery_original 0]
  exact SourceCompleteGraph.history_field_recovery 0 runtime index steps value

theorem innovation_nonzero (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :
    innovation (inventoryBound runtime + steps) (SourceGraphLoss.advancedIndex (inventoryBound runtime) index steps)
      (recovery runtime index steps) ≠ 0 := by
  have same : recovery runtime index steps = (SourceCompleteGraph.recovery 0 runtime index steps :
      SourceJointClockGraph.Carrier → FieldSpace (inventoryBound runtime + steps) (inventoryBound runtime + steps)) :=
    funext (recovery_original 0 runtime index steps)
  rw [same, SourceCompleteGraph.recovery_canonical, ← SourceCompleteGraph.old_read_original,
    innovation_original, SourceGraphRecurrence.innovation_canonical]
  exact SourceGraphBirth.innovation_ne_zero _ _ _

theorem boundary_nonzero (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :
    residual runtime index steps SourceCompleteGraph.boundary ≠ 0 := by
  rw [residual_original 0]
  exact SourceCompleteGraph.history_boundary_nonzero 0 runtime index steps

theorem old_pulse_recovered (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    residual runtime index 1 (SourceGraphGrowth.pulse (inventoryBound runtime) index) = 0 := by
  rw [residual_original 0]
  exact SourceCompleteGraph.old_pulse_preserved 0 runtime index

end
end SourceRecordedEvolution
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
