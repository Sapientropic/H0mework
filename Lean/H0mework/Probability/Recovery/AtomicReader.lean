import H0mework.Probability.Recovery.AtomicCotest

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedAtomicObservation

open SourceWeightedRecovery MeasureTheory
open scoped InnerProductSpace

noncomputable section

universe u

variable {A : Type u} [MeasurableSpace A] [MeasurableSingletonClass A]
variable (source : PMF A) (point : A)

private def normalizedCotest : Space source →L[ℂ] ℂ :=
  ((source point).toReal)⁻¹ • innerSL ℂ (cotest source point)

private theorem normalizedCotest_read (supported : point ∈ source.support) (value : Space source) :
    normalizedCotest source point value = evalAt source point supported value := by
  change ((source point).toReal)⁻¹ • ⟪cotest source point, value⟫_ℂ = _
  rw [cotest_pairing, smul_smul, inv_mul_cancel₀ (ne_of_gt (mass_positive source point supported)), one_smul]
  rfl

def covector : Space source := (((((source point).toReal)⁻¹ : ℝ)) : ℂ) • cotest source point

theorem covector_read (supported : point ∈ source.support) (value : Space source) :
    ⟪covector source point, value⟫_ℂ = evalAt source point supported value := by
  have scalar := inner_smul_real_left (𝕜 := ℂ) (cotest source point) value ((source point).toReal)⁻¹
  exact scalar.trans (normalizedCotest_read source point supported value)

def evalAtContinuous (supported : point ∈ source.support) : Space source →L[ℂ] ℂ where
  toLinearMap := evalAt source point supported
  cont := by
    have same : (fun value => evalAt source point supported value) = normalizedCotest source point :=
      funext fun value => (normalizedCotest_read source point supported value).symm
    change Continuous fun value : Space source => evalAt source point supported value
    rw [same]
    exact (normalizedCotest source point).continuous

theorem evalAtContinuous_toLinearMap (supported : point ∈ source.support) :
    (evalAtContinuous source point supported).toLinearMap = evalAt source point supported := rfl

theorem evalAtContinuous_norm (supported : point ∈ source.support) :
    ‖evalAtContinuous source point supported‖ = 1 / Real.sqrt (source point).toReal := by
  have same : evalAtContinuous source point supported = normalizedCotest source point := by
    ext value
    exact (normalizedCotest_read source point supported value).symm
  rw [same, normalizedCotest, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg), innerSL_apply_norm, cotest_norm]
  have positive := mass_positive source point supported
  have square := Real.sq_sqrt (le_of_lt positive)
  have sqrtNonzero := ne_of_gt (Real.sqrt_pos.mpr positive)
  field_simp
  nlinarith

end
end SourceGeneratedAtomicObservation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
