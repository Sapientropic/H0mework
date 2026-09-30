import H0mework.Fock.CopyComplete.Step

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCompleteGraph

open SourceGeneratedAcquisitionMeasure SourceGeneratedAcquisitionContinuation SourceGeneratedJointClockGraph
open SourceGeneratedRuntimeHistoryProbability SourceGeneratedActionWords.Fock SourceGeneratedActionWords.Fock.Dynamic
open SourceOwnedObservationHistory
open SourceCopyProgram (Index)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
attribute [local instance] completeUniform completeMeasurable completeBorel completeT2

def recovery (model : Nat) (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    (steps : Nat) → SourceJointClockGraph.Carrier →L[ℂ]
      FieldSpace (inventoryBound runtime + steps) (inventoryBound runtime + steps)
  | 0 => SourceConditionalGraphDecoder.fieldDecode (inventoryBound runtime) (inventoryBound runtime) index
      (Hilbert.read model (inventoryBound runtime))
  | steps + 1 => step model (inventoryBound runtime + steps)
      (SourceGraphLoss.advancedIndex (inventoryBound runtime) index steps) (recovery model runtime index steps)

theorem recovery_canonical (model : Nat) (runtime : LivingRuntimeState process)
    (index : Index (inventoryBound runtime)) (steps : Nat) :
    recovery model runtime index steps = SourceConditionalGraphDecoder.fieldDecode
      (inventoryBound runtime + steps) (inventoryBound runtime + steps)
      (SourceGraphLoss.advancedIndex (inventoryBound runtime) index steps) (Hilbert.read model (inventoryBound runtime + steps)) := by
  induction steps with
  | zero => rfl
  | succ steps previous => rw [recovery, previous, step_canonical]; rfl

def residual (model : Nat) (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (steps : Nat) (value : SourceJointClockGraph.Carrier) : SourceJointClockGraph.Carrier :=
  value - SourceCopyGraph.action (inventoryBound runtime + steps)
    (SourceGraphLoss.advancedIndex (inventoryBound runtime) index steps)
    (fieldRead (inventoryBound runtime + steps) (inventoryBound runtime + steps) (recovery model runtime index steps value))

def birthMap (model : Nat) (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (steps : Nat) : SourceJointClockGraph.Carrier →L[ℂ] SourceJointClockGraph.Carrier :=
  let h := SourceGraphRecurrence.innovationFromPrevious (inventoryBound runtime + steps)
    (SourceGraphLoss.advancedIndex (inventoryBound runtime) index steps) (read model) (recovery model runtime index steps)
  ((((‖h‖ ^ 2 : ℝ) : ℂ)⁻¹) • innerSL ℂ h).smulRight h

theorem residual_canonical (model : Nat) (runtime : LivingRuntimeState process)
    (index : Index (inventoryBound runtime)) (steps : Nat) (value : SourceJointClockGraph.Carrier) :
    residual model runtime index steps value = SourceConditionalGraphDecoder.residual
      (inventoryBound runtime + steps) (inventoryBound runtime + steps)
      (SourceGraphLoss.advancedIndex (inventoryBound runtime) index steps) (Hilbert.read model (inventoryBound runtime + steps)) value := by
  rw [residual, recovery_canonical]
  have original := SourceConditionalGraphDecoder.original_reconstruction
    (inventoryBound runtime + steps) (inventoryBound runtime + steps)
    (SourceGraphLoss.advancedIndex (inventoryBound runtime) index steps) (Hilbert.read model (inventoryBound runtime + steps)) value
  exact (eq_sub_iff_add_eq.mpr ((add_comm _ _).trans original)).symm

theorem birth_map_canonical (model : Nat) (runtime : LivingRuntimeState process)
    (index : Index (inventoryBound runtime)) (steps : Nat) :
    birthMap model runtime index steps = SourceGraphBirth.update (inventoryBound runtime + steps)
      (SourceGraphLoss.advancedIndex (inventoryBound runtime) index steps) (read model) := by
  rw [birthMap, recovery_canonical, ← old_read_original, SourceGraphRecurrence.innovation_canonical]
  rfl

theorem energy_step (model : Nat) (runtime : LivingRuntimeState process)
    (index : Index (inventoryBound runtime)) (steps : Nat) (value : SourceJointClockGraph.Carrier) :
    ‖residual model runtime index (steps + 1) value‖ ^ 2 + ‖birthMap model runtime index steps value‖ ^ 2 =
      ‖residual model runtime index steps value‖ ^ 2 := by
  have newer : residual model runtime index (steps + 1) value = SourceGraphGrowth.newResidual
      (inventoryBound runtime + steps) (SourceGraphLoss.advancedIndex (inventoryBound runtime) index steps) (read model) value := by
    rw [residual_canonical]
    rfl
  have older : residual model runtime index steps value = SourceGraphGrowth.oldResidual
      (inventoryBound runtime + steps) (SourceGraphLoss.advancedIndex (inventoryBound runtime) index steps) (read model) value := by
    rw [residual_canonical]
    rfl
  rw [newer, older, birth_map_canonical]
  have original := source_growth_energy model (inventoryBound runtime + steps)
    (SourceGraphLoss.advancedIndex (inventoryBound runtime) index steps) value
  with_reducible exact original

theorem history_energy (model : Nat) (runtime : LivingRuntimeState process)
    (index : Index (inventoryBound runtime)) (steps : Nat) (value : SourceJointClockGraph.Carrier) :
    ‖residual model runtime index steps value‖ ^ 2 +
        ∑ stage ∈ Finset.range steps, ‖birthMap model runtime index stage value‖ ^ 2 =
      ‖residual model runtime index 0 value‖ ^ 2 := by
  induction steps with
  | zero => simp only [Finset.range_zero, Finset.sum_empty, add_zero]
  | succ steps previous =>
    rw [Finset.sum_range_succ]
    have localLaw := energy_step model runtime index steps value
    linarith only [previous, localLaw]

theorem history_field_recovery (model : Nat) (runtime : LivingRuntimeState process)
    (index : Index (inventoryBound runtime)) (steps : Nat)
    (value : FieldSpace (inventoryBound runtime + steps) (inventoryBound runtime + steps)) :
    recovery model runtime index steps
      (SourceCopyGraph.action (inventoryBound runtime + steps)
        (SourceGraphLoss.advancedIndex (inventoryBound runtime) index steps)
        (fieldRead (inventoryBound runtime + steps) (inventoryBound runtime + steps) value)) = value := by
  rw [recovery_canonical]
  exact field_recovery model _ _ _ value

end
end SourceCompleteGraph
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
