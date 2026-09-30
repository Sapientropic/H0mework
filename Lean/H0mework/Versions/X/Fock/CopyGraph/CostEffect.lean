import H0mework.Versions.X.Fock.CopyGraph.CostPrice
import H0mework.Versions.X.Fock.CopyGraph.CorrectionEffect

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalCost

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability SourceConditionalCorrection
open SourceCopyProgram (Index)
noncomputable section
universe u
variable {Observed : Type u} [MeasurableSpace Observed] [MeasurableSingletonClass Observed]

theorem strict_clock_price (depth bound : Nat) (index : Index depth) (query : Fin (bound + 1) → Observed)
    (value : Space (historyPMF bound)) (forced : clockPair bound query value ≠ 0) :
    ‖residual (historyPMF bound) query value‖ ^ 2 <
      ‖SourceConditionalGraphDecoder.residual depth bound index query (SourceConditionalGraph.copyRead depth bound index value)‖ ^ 2 := by
  rw [minimum_cost]
  exact lt_add_of_pos_right _ (div_pos
    (mul_pos (strength_pos depth bound index) (sq_pos_of_pos (norm_pos_iff.mpr forced)))
      (denominator_pos depth bound index query))

theorem zero_surplus_iff (depth bound : Nat) (index : Index depth) (query : Fin (bound + 1) → Observed)
    (value : Space (historyPMF bound)) :
    ‖SourceConditionalGraphDecoder.residual depth bound index query (SourceConditionalGraph.copyRead depth bound index value)‖ ^ 2 =
      ‖residual (historyPMF bound) query value‖ ^ 2 ↔ clockPair bound query value = 0 := by
  constructor
  · intro same
    by_contra forced
    exact (ne_of_gt (strict_clock_price depth bound index query value forced)) same
  · intro vanished
    rw [minimum_cost, vanished, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_div, add_zero]

open SourceCopyObservation (before after twoMaterial)
open SourceGeneratedJointClock
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock
local instance effectParentMeasurable : MeasurableSpace ParentCarrier := ⊤
local notation "clockValue" => taskValue (historyPMF 3) (signal 3)

theorem before_best_cost_strict :
    ‖residual (historyPMF 3) (before 3 3) clockValue‖ ^ 2 <
      ‖SourceConditionalGraphDecoder.residual 3 3 twoMaterial (before 3 3)
        (SourceConditionalGraph.copyRead 3 3 twoMaterial clockValue)‖ ^ 2 :=
  strict_clock_price _ _ _ _ _ before_pair_ne_zero

theorem before_complete_budget :
    ‖SourceConditionalGraphDecoder.residual 3 3 twoMaterial (before 3 3)
      (SourceConditionalGraph.copyRead 3 3 twoMaterial clockValue)‖ ^ 2 =
        ‖residual (historyPMF 3) (before 3 3) clockValue‖ ^ 2 +
          strength 3 3 twoMaterial * ‖clockPair 3 (before 3 3) clockValue‖ ^ 2 / denominator 3 3 twoMaterial (before 3 3) := by
  with_reducible exact minimum_cost 3 3 twoMaterial (before 3 3) clockValue

theorem after_best_cost_zero (value : Space (historyPMF 3)) :
    ‖SourceConditionalGraphDecoder.residual 3 3 twoMaterial (after 3 3 twoMaterial)
      (SourceConditionalGraph.copyRead 3 3 twoMaterial value)‖ ^ 2 = 0 := by
  rw [SourceConditionalGraphDecoder.after_minimum_zero, norm_zero, zero_pow (by decide : 2 ≠ 0)]

end
end SourceConditionalCost
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
