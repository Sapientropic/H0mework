import H0mework.Fock.CopyGraph.CostSource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalCost

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability SourceConditionalCorrection
open SourceConditionalGraphDecoder (action)
open SourceCopyProgram (Index scale)
noncomputable section
universe u
variable {Observed : Type u} [MeasurableSpace Observed]

theorem coefficient_norm_sq (depth bound : Nat) (index : Index depth) (query : Fin (bound + 1) → Observed)
    (value : Space (historyPMF bound)) :
    ‖coefficient depth bound index query value‖ ^ 2 =
      strength depth bound index ^ 2 * ‖clockPair bound query value‖ ^ 2 / denominator depth bound index query ^ 2 := by
  unfold coefficient
  rw [norm_div, norm_mul, Complex.norm_of_nonneg (strength_pos depth bound index).le,
    Complex.norm_of_nonneg (denominator_pos depth bound index query).le, div_pow, mul_pow]

variable [MeasurableSingletonClass Observed]

theorem correction_cost (depth bound : Nat) (index : Index depth) (query : Fin (bound + 1) → Observed)
    (value : Space (historyPMF bound)) :
    ‖action depth bound index query (update depth bound index query value)‖ ^ 2 =
      strength depth bound index ^ 2 * ‖clockPair bound query value‖ ^ 2 * coupling bound query /
        denominator depth bound index query := by
  unfold update
  rw [map_smul, norm_smul, mul_pow, coefficient_norm_sq, direction_energy]
  have nonzero := (denominator_pos depth bound index query).ne'
  field_simp

theorem old_conditional_cost (depth bound : Nat) (index : Index depth) (query : Fin (bound + 1) → Observed)
    (value : Space (historyPMF bound)) :
    ‖SourceConditionalGraph.copyRead depth bound index (residual (historyPMF bound) query value)‖ ^ 2 =
      ‖residual (historyPMF bound) query value‖ ^ 2 + strength depth bound index * ‖clockPair bound query value‖ ^ 2 := by
  rw [SourceConditionalGraph.residual_graph_energy, SourceConditionalGraph.residual_clock, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ bound + 1)]
  unfold strength clockPair
  ring

theorem minimum_cost (depth bound : Nat) (index : Index depth) (query : Fin (bound + 1) → Observed)
    (value : Space (historyPMF bound)) :
    ‖SourceConditionalGraphDecoder.residual depth bound index query (SourceConditionalGraph.copyRead depth bound index value)‖ ^ 2 =
      ‖residual (historyPMF bound) query value‖ ^ 2 + strength depth bound index * ‖clockPair bound query value‖ ^ 2 /
        denominator depth bound index query := by
  have generated := explicit_gain depth bound index query value
  rw [old_conditional_cost, correction_cost] at generated
  have nonzero := (denominator_pos depth bound index query).ne'
  have balance : strength depth bound index * ‖clockPair bound query value‖ ^ 2 =
      strength depth bound index * ‖clockPair bound query value‖ ^ 2 / denominator depth bound index query +
        strength depth bound index ^ 2 * ‖clockPair bound query value‖ ^ 2 * coupling bound query / denominator depth bound index query := by
    field_simp
    unfold denominator
    ring
  linarith only [generated, balance]

end
end SourceConditionalCost
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
