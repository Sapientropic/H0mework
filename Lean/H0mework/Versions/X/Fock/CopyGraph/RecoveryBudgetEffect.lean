import H0mework.Versions.X.Fock.CopyGraph.RecoveryBudgetComplete

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyRecoveryBudget

open SourceGeneratedAcquisitionContinuation SourceGeneratedJointClockGraph
open SourceCopyProgram (Index)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
attribute [local instance] SourceCopyCofinal.finiteComplete SourceCopyCofinal.wholeComplete

theorem recover_residual_zero (depth : Nat) (index : Index depth) (target : SourceJointClockGraph.Carrier) :
    SourceCopyGraph.recover depth index (SourceCopyGraph.residual depth index target) = 0 := by
  change SourceCopyGraph.recover depth index
    (target - SourceCopyGraph.action depth index (SourceCopyGraph.recover depth index target)) = 0
  rw [map_sub, SourceCopyGraph.recover_action, sub_self]

theorem projection_residual_zero (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (steps : Nat) (target : SourceJointClockGraph.Carrier) :
    (SourceCopyCofinal.historyImages (inventoryBound runtime) index steps).starProjection
      (SourceCopyGraph.residual (inventoryBound runtime) index target) = 0 := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact Submodule.zero_mem _
  · intro value present
    rcases SourceCopyCofinal.image_in_action (inventoryBound runtime) index (inventoryBound runtime + steps) present with ⟨source, rfl⟩
    rw [sub_zero]
    exact SourceCopyCofinal.whole_orthogonal _ index target source

theorem residual_prediction_zero (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (steps : Nat) (target : SourceJointClockGraph.Carrier) :
    SourceCopyGraph.action (inventoryBound runtime) index
      (fieldRead (inventoryBound runtime + steps) (inventoryBound runtime + steps)
        (SourceRecordedEvolution.recovery runtime index steps (SourceCopyGraph.residual (inventoryBound runtime) index target))) = 0 := by
  have source := SourceCopyCofinal.actual_projection runtime index steps
    (SourceCopyGraph.residual (inventoryBound runtime) index target)
  rw [projection_residual_zero, SourceCopyCofinal.advanced_action] at source
  exact source.symm

theorem residual_stays (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (steps : Nat) (target : SourceJointClockGraph.Carrier) :
    SourceRecordedEvolution.residual runtime index steps (SourceCopyGraph.residual (inventoryBound runtime) index target) =
      SourceCopyGraph.residual (inventoryBound runtime) index target := by
  rw [SourceRecordedEvolution.residual, SourceCopyCofinal.advanced_action, residual_prediction_zero, sub_zero]

theorem residual_budget_zero (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (steps : Nat) (target : SourceJointClockGraph.Carrier) :
    remainingCost runtime index steps (SourceCopyGraph.residual (inventoryBound runtime) index target) = 0 := by
  rw [remainingCost, recover_residual_zero, zero_sub, map_neg, residual_prediction_zero, neg_zero, norm_zero,
    zero_pow (by decide : 2 ≠ 0)]

theorem residual_birth_zero (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (steps : Nat) (target : SourceJointClockGraph.Carrier) :
    SourceRecordedEvolution.birth runtime index steps (SourceCopyGraph.residual (inventoryBound runtime) index target) = 0 := by
  have budget := tail_budget runtime index steps 1 (SourceCopyGraph.residual (inventoryBound runtime) index target)
  rw [residual_budget_zero, residual_budget_zero, zero_add, Finset.sum_range_one, Nat.add_zero] at budget
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp budget)

theorem boundary_budget_pos (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (steps : Nat) : 0 < remainingCost runtime index steps SourceCompleteGraph.boundary := by
  have source := actual_error runtime index steps SourceCompleteGraph.boundary
  rw [SourceCopyCofinal.boundary_remaining, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add] at source
  rw [← source]
  exact sq_pos_of_pos (norm_pos_iff.mpr (SourceRecordedEvolution.boundary_nonzero runtime index steps))

end
end SourceCopyRecoveryBudget
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
