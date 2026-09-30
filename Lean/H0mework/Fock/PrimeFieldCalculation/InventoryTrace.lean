import H0mework.Fock.PrimeFieldCalculation.ContinuationSource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedConditionalInventory

open SourceGeneratedAcquisitionContinuation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem normal_cost (runtime : LivingRuntimeState process) :
    snapshotCost (normal runtime).targetRuntime.state = snapshotCost runtime.state +
      ∑ step ∈ Finset.range ((frontier runtime).stageCount + 1),
        if Nat.Prime (2 * (runtime.advance step).state + 5) then (0 : ℝ) else 1 := by
  have evolve (count : Nat) (inside : count ≤ (frontier runtime).stageCount + 1) :
      snapshotCost (runtime.advance count).state = snapshotCost runtime.state +
        ∑ step ∈ Finset.range count,
          if Nat.Prime (2 * (runtime.advance step).state + 5) then (0 : ℝ) else 1 := by
    induction count with
    | zero => simp [LivingRuntimeState.advance]
    | succ count previous =>
        have generated := ((realization runtime).operationAt ⟨count, by omega⟩).2.2.2.1
        change snapshotCost (runtime.advance (count + 1)).state =
          snapshotCost (runtime.advance count).state +
            if Nat.Prime (2 * (runtime.advance count).state + 5) then (0 : ℝ) else 1 at generated
        rw [generated, previous (by omega), Finset.sum_range_succ]
        ring
  exact evolve ((frontier runtime).stageCount + 1) le_rfl

theorem generated_next_cost (runtime : LivingRuntimeState process) :
    snapshotCost (normal runtime).targetRuntime.tick.next.state = snapshotCost runtime.state +
      ∑ step ∈ Finset.range ((frontier runtime).stageCount + 2),
        if Nat.Prime (2 * (runtime.advance step).state + 5) then (0 : ℝ) else 1 := by
  have fresh := actual_cost_step (runtime.advance ((frontier runtime).stageCount + 1)).state
  change snapshotCost (normal runtime).targetRuntime.tick.next.state =
    snapshotCost (normal runtime).targetRuntime.state +
      if Nat.Prime (2 * (runtime.advance ((frontier runtime).stageCount + 1)).state + 5) then (0 : ℝ) else 1 at fresh
  rw [fresh, normal_cost]
  conv_rhs => rw [Finset.sum_range_succ]
  ring

end
end SourceGeneratedConditionalInventory
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
