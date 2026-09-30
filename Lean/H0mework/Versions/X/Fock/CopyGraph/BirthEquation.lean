import H0mework.Versions.X.Fock.CopyGraph.BirthDirection

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGraphBirth

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability SourceOwnedObservationHistory
open SourceCopyProgram (Index)
open SourceGraphGrowth (oldRead taggedRead oldAction taggedAction birthGain)
open scoped InnerProductSpace
noncomputable section
universe u
variable {Observed : Type u} [MeasurableSpace Observed] [MeasurableSingletonClass Observed]

omit [MeasurableSingletonClass Observed] in
theorem innovation_old_orthogonal (depth : Nat) (index : Index depth) (read : Nat → Observed)
    (value : Space (observed (historyPMF depth) (oldRead depth read))) :
    inner ℂ (innovation depth index read) (oldAction depth index read value) = 0 :=
  inner_eq_zero_symm.mp (SourceConditionalGraphDecoder.source_orthogonal depth depth index (oldRead depth read) (fresh depth index) value)

theorem innovation_tagged_orthogonal (depth : Nat) (index : Index depth) (read : Nat → Observed)
    (value : SourceJointClockGraph.Carrier) :
    inner ℂ (innovation depth index read) (SourceGraphGrowth.taggedResidual depth index read value) = 0 := by
  have original := SourceConditionalGraphDecoder.source_orthogonal (depth + 1) (depth + 1)
    (FamilyModel.Fock.oldIndex depth index) (taggedRead depth read) value (innovationObserved depth index read)
  rw [innovation_observed_source] at original
  exact original

theorem coefficient_pairing (depth : Nat) (index : Index depth) (read : Nat → Observed)
    (value : SourceJointClockGraph.Carrier) :
    coefficient depth index read value * ((‖innovation depth index read‖ ^ 2 : ℝ) : ℂ) =
      inner ℂ (innovation depth index read) value := by
  have generated := SourceConditionalGraphDecoder.reconstruction depth depth index (oldRead depth read) value
  have pairing := congrArg (inner ℂ (innovation depth index read)) generated
  rw [inner_add_right, innovation_old_orthogonal, zero_add] at pairing
  change inner ℂ (innovation depth index read) (SourceGraphGrowth.oldResidual depth index read value) =
    inner ℂ (innovation depth index read) value at pairing
  rw [SourceGraphGrowth.birth_residual, inner_add_right, innovation_tagged_orthogonal, zero_add,
    birth_direction, inner_smul_right, inner_self_eq_norm_sq_to_K] at pairing
  rw [Complex.ofReal_pow]
  with_unfolding_all exact pairing

omit [MeasurableSingletonClass Observed] in
theorem denominator_ne_zero (depth : Nat) (index : Index depth) (read : Nat → Observed) :
    ((‖innovation depth index read‖ ^ 2 : ℝ) : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 (norm_ne_zero_iff.mpr (innovation_ne_zero depth index read)))

theorem coefficient_formula (depth : Nat) (index : Index depth) (read : Nat → Observed)
    (value : SourceJointClockGraph.Carrier) :
    coefficient depth index read value = inner ℂ (innovation depth index read) value / ((‖innovation depth index read‖ ^ 2 : ℝ) : ℂ) :=
  (eq_div_iff (denominator_ne_zero depth index read)).mpr (coefficient_pairing depth index read value)

theorem birth_formula (depth : Nat) (index : Index depth) (read : Nat → Observed)
    (value : SourceJointClockGraph.Carrier) :
    birthGain depth index read value =
      (inner ℂ (innovation depth index read) value / ((‖innovation depth index read‖ ^ 2 : ℝ) : ℂ)) • innovation depth index read := by
  rw [birth_direction, coefficient_formula]

theorem birth_cost (depth : Nat) (index : Index depth) (read : Nat → Observed)
    (value : SourceJointClockGraph.Carrier) :
    ‖birthGain depth index read value‖ ^ 2 = ‖inner ℂ (innovation depth index read) value‖ ^ 2 / ‖innovation depth index read‖ ^ 2 := by
  have normDenominator : ‖((‖innovation depth index read‖ ^ 2 : ℝ) : ℂ)‖ = ‖innovation depth index read‖ ^ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  rw [birth_formula, norm_smul, norm_div, normDenominator, mul_pow, div_pow]
  field_simp [norm_ne_zero_iff.mpr (innovation_ne_zero depth index read)]

theorem birth_zero_iff (depth : Nat) (index : Index depth) (read : Nat → Observed)
    (value : SourceJointClockGraph.Carrier) :
    birthGain depth index read value = 0 ↔ inner ℂ (innovation depth index read) value = 0 := by
  rw [birth_formula, smul_eq_zero]
  simp only [innovation_ne_zero depth index read, or_false, div_eq_zero_iff, denominator_ne_zero depth index read, or_false]

end
end SourceGraphBirth
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
