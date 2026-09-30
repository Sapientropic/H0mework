import H0mework.Fock.CopyGraph.ConditionalMoments
import H0mework.Fock.PrimeFieldJoint.ClockField

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalGraph

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability SourceUniformFibreVariance
open SourceGeneratedJointClock
open scoped InnerProductSpace
noncomputable section
universe u
variable {Observed : Type u} [MeasurableSpace Observed] [MeasurableSingletonClass Observed]

theorem clock_inner (bound : Nat) (value : Space (historyPMF bound)) :
    SourceClockComplex.clock (SourceHistoryWord.word bound value) =
      Real.sqrt (bound + 1 : ℝ) • ⟪taskValue (historyPMF bound) (signal bound), value⟫_ℂ := by
  rw [SourceHistoryWord.word_sum, map_sum, inner_source_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro actor _
  rw [SourceClockComplex.clock_single, SourceHistoryWord.coefficient_value,
    SourceHistoryWord.coefficient_scale, taskValue_at _ _ actor (source_positive bound actor), signal_value,
    source_weight]
  simp only [SourceClockModel.rawClock, Int.cast_add, Int.cast_natCast, Int.cast_one,
    RCLike.inner_apply, map_add, map_natCast, map_one, Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one]
  have factor : (1 / Real.sqrt (bound + 1 : ℝ) : ℝ) = Real.sqrt (bound + 1 : ℝ) * (1 / (bound + 1 : ℝ)) := by
    rw [mul_one_div, Real.sqrt_div_self']
  have castFactor := congrArg (fun scalar : ℝ => (scalar : ℂ)) factor
  simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_one] at castFactor
  rw [castFactor]
  ring

omit [MeasurableSingletonClass Observed] in
theorem residual_clock (bound : Nat) (observer : Fin (bound + 1) → Observed) (value : Space (historyPMF bound)) :
    SourceClockComplex.clock (SourceHistoryWord.word bound (residual (historyPMF bound) observer value)) =
      Real.sqrt (bound + 1 : ℝ) •
        ⟪residual (historyPMF bound) observer (taskValue (historyPMF bound) (signal bound)),
          residual (historyPMF bound) observer value⟫_ℂ := by
  rw [clock_inner]
  congr 1
  have whole := IsometricRetainedTransfer.pullback_transfer_add_residual (pullback (historyPMF bound) observer)
    (taskValue (historyPMF bound) (signal bound))
  have same := congrArg (fun test : Space (historyPMF bound) =>
    inner ℂ test (residual (historyPMF bound) observer value)) whole
  rw [inner_add_left, IsometricRetainedTransfer.residual_orthogonal, zero_add] at same
  exact same.symm

omit [MeasurableSingletonClass Observed] in
theorem residual_clock_bound (bound : Nat) (observer : Fin (bound + 1) → Observed) (value : Space (historyPMF bound)) :
    ‖SourceClockComplex.clock (SourceHistoryWord.word bound (residual (historyPMF bound) observer value))‖ ^ 2 ≤
      (bound + 1 : ℝ) * ‖residual (historyPMF bound) observer (taskValue (historyPMF bound) (signal bound))‖ ^ 2 *
        ‖residual (historyPMF bound) observer value‖ ^ 2 := by
  rw [residual_clock, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt (by positivity : (0 : ℝ) ≤ bound + 1)]
  have cauchy := norm_inner_le_norm (𝕜 := ℂ)
    (residual (historyPMF bound) observer (taskValue (historyPMF bound) (signal bound)))
    (residual (historyPMF bound) observer value)
  have squared := pow_le_pow_left₀ (norm_nonneg _) cauchy 2
  rw [mul_pow] at squared
  nlinarith only [mul_le_mul_of_nonneg_left squared (by positivity : (0 : ℝ) ≤ bound + 1)]

theorem clock_conditional (bound : Nat) (observer : Fin (bound + 1) → Observed) (atom : Observed)
    (supported : atom ∈ (observed (historyPMF bound) observer).support) :
    transfer (historyPMF bound) observer (taskValue (historyPMF bound) (signal bound)) atom =
      ∑ actor : Fin (bound + 1),
        (SourceConditionalHistory.conditional (historyPMF bound) observer atom supported actor).toReal • signal bound actor :=
  optimal_is_conditional (historyPMF bound) observer (signal bound) atom supported

end
end SourceConditionalGraph
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
