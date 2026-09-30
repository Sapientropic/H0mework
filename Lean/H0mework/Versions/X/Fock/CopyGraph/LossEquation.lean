import H0mework.Versions.X.Fock.CopyGraph.LossDirection

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGraphLoss

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability SourceOwnedObservationHistory
open SourceCopyProgram (Index)
open SourceGraphGrowth (newRead taggedRead newAction forgettingLoss)
open scoped InnerProductSpace
noncomputable section
universe u
variable {Observed : Type u} [MeasurableSpace Observed] [MeasurableSingletonClass Observed]

omit [MeasurableSingletonClass Observed] in
theorem direction_raw_orthogonal (depth : Nat) (index : Index depth) (read : Nat → Observed)
    (value : Space (observed (historyPMF (depth + 1)) (newRead depth read))) :
    inner ℂ (direction depth index read) (newAction depth index read value) = 0 :=
  inner_eq_zero_symm.mp (SourceConditionalGraphDecoder.source_orthogonal (depth + 1) (depth + 1)
    (FamilyModel.Fock.oldIndex depth index) (newRead depth read) (SourceGraphBirth.fresh depth index) value)

theorem direction_tagged_orthogonal (depth : Nat) (index : Index depth) (read : Nat → Observed)
    (value : SourceJointClockGraph.Carrier) :
    inner ℂ (direction depth index read) (SourceGraphGrowth.taggedResidual depth index read value) = 0 := by
  have original := SourceConditionalGraphDecoder.source_orthogonal (depth + 1) (depth + 1)
    (FamilyModel.Fock.oldIndex depth index) (taggedRead depth read) value (directionObserved depth index read)
  rw [direction_observed_source] at original
  exact original

theorem coefficient_pairing (depth : Nat) (index : Index depth) (read : Nat → Observed)
    (value : SourceJointClockGraph.Carrier) :
    coefficient depth index read value * ((‖direction depth index read‖ ^ 2 : ℝ) : ℂ) = inner ℂ (direction depth index read) value := by
  have generated := SourceConditionalGraphDecoder.reconstruction (depth + 1) (depth + 1)
    (FamilyModel.Fock.oldIndex depth index) (newRead depth read) value
  have pairing := congrArg (inner ℂ (direction depth index read)) generated
  rw [inner_add_right, direction_raw_orthogonal, zero_add] at pairing
  change inner ℂ (direction depth index read) (SourceGraphGrowth.newResidual depth index read value) =
    inner ℂ (direction depth index read) value at pairing
  rw [SourceGraphGrowth.forgetting_residual, inner_add_right, direction_tagged_orthogonal, zero_add,
    loss_direction, inner_smul_right, inner_self_eq_norm_sq_to_K] at pairing
  rw [Complex.ofReal_pow]
  with_unfolding_all exact pairing

theorem loss_formula (depth : Nat) (index : Index depth) (read : Nat → Observed)
    (value : SourceJointClockGraph.Carrier) :
    forgettingLoss depth index read value =
      (inner ℂ (direction depth index read) value / ((‖direction depth index read‖ ^ 2 : ℝ) : ℂ)) • direction depth index read := by
  by_cases zero : direction depth index read = 0
  · rw [loss_direction, zero, smul_zero, smul_zero]
  · have denominator : ((‖direction depth index read‖ ^ 2 : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 (norm_ne_zero_iff.mpr zero))
    rw [loss_direction, (eq_div_iff denominator).mpr (coefficient_pairing depth index read value)]

theorem loss_cost (depth : Nat) (index : Index depth) (read : Nat → Observed)
    (value : SourceJointClockGraph.Carrier) :
    ‖forgettingLoss depth index read value‖ ^ 2 = ‖inner ℂ (direction depth index read) value‖ ^ 2 / ‖direction depth index read‖ ^ 2 := by
  by_cases zero : direction depth index read = 0
  · simp only [loss_direction, zero, smul_zero, norm_zero, zero_pow (by decide : 2 ≠ 0), div_zero]
  · have normDenominator : ‖((‖direction depth index read‖ ^ 2 : ℝ) : ℂ)‖ = ‖direction depth index read‖ ^ 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    rw [loss_formula, norm_smul, norm_div, normDenominator, mul_pow, div_pow]
    field_simp [norm_ne_zero_iff.mpr zero]

theorem loss_zero_iff (depth : Nat) (index : Index depth) (read : Nat → Observed)
    (value : SourceJointClockGraph.Carrier) :
    forgettingLoss depth index read value = 0 ↔ inner ℂ (direction depth index read) value = 0 := by
  by_cases zero : direction depth index read = 0
  · simp only [loss_direction, zero, smul_zero, inner_zero_left]
  · have denominator : ((‖direction depth index read‖ ^ 2 : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 (norm_ne_zero_iff.mpr zero))
    rw [loss_formula, smul_eq_zero]
    simp only [zero, or_false, div_eq_zero_iff, denominator, or_false]

end
end SourceGraphLoss
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
