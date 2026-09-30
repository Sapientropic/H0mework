import H0mework.Versions.X.Fock.CopyGraph.RecoveryBudgetSource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyRecoveryBudget

open SourceGeneratedAcquisitionContinuation
open SourceCopyProgram (Index)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open Filter
open scoped Topology
noncomputable section

theorem remaining_tendsto (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (target : SourceJointClockGraph.Carrier) :
    Tendsto (fun steps => remainingCost runtime index steps target) atTop (𝓝 0) := by
  have source := (SourceCopyCofinal.cost_tendsto runtime index target).sub
    (tendsto_const_nhds (x := ‖SourceCopyGraph.residual (inventoryBound runtime) index target‖ ^ 2))
  simpa only [actual_error, add_sub_cancel_left, sub_self] using source

theorem finite_sum (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (steps : Nat) (target : SourceJointClockGraph.Carrier) :
    ∑ stage ∈ Finset.range steps, ‖SourceRecordedEvolution.birth runtime index stage target‖ ^ 2 =
      remainingCost runtime index 0 target - remainingCost runtime index steps target :=
  eq_sub_iff_add_eq.mpr ((add_comm _ _).trans (history_budget runtime index steps target))

theorem complete_budget (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (target : SourceJointClockGraph.Carrier) :
    HasSum (fun stage => ‖SourceRecordedEvolution.birth runtime index stage target‖ ^ 2)
      (remainingCost runtime index 0 target) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun stage => sq_nonneg ‖SourceRecordedEvolution.birth runtime index stage target‖) _).mpr
  have source := (tendsto_const_nhds (x := remainingCost runtime index 0 target)).sub (remaining_tendsto runtime index target)
  simpa only [finite_sum, sub_zero] using source

theorem tail_budget (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (offset steps : Nat) (target : SourceJointClockGraph.Carrier) :
    remainingCost runtime index (offset + steps) target +
      ∑ stage ∈ Finset.range steps, ‖SourceRecordedEvolution.birth runtime index (offset + stage) target‖ ^ 2 =
        remainingCost runtime index offset target := by
  have complete := history_budget runtime index (offset + steps) target
  have prior := history_budget runtime index offset target
  rw [Finset.sum_range_add] at complete
  linarith only [complete, prior]

theorem complete_tail_budget (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (offset : Nat) (target : SourceJointClockGraph.Carrier) :
    HasSum (fun stage => ‖SourceRecordedEvolution.birth runtime index (offset + stage) target‖ ^ 2)
      (remainingCost runtime index offset target) := by
  have source : HasSum (fun stage => ‖SourceRecordedEvolution.birth runtime index stage target‖ ^ 2)
      (remainingCost runtime index offset target +
        ∑ stage ∈ Finset.range offset, ‖SourceRecordedEvolution.birth runtime index stage target‖ ^ 2) := by
    rw [history_budget]
    exact complete_budget runtime index target
  have tail := (hasSum_nat_add_iff offset).mpr source
  simpa only [Nat.add_comm] using tail

end
end SourceCopyRecoveryBudget
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
