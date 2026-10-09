import H0mework.Versions.V2.Arithmetic.BurnolPhysical.QuarterMellinAdditiveEvenRechart

/-!
# Exact norm of the quarter-Mellin additive rechart

The reciprocal-square Jacobian identifies the even additive Burnol L² norm
with one half of the existing quarter-Mellin feature norm.  This file keeps
the integral bookkeeping separate from the bounded completion interfaces.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open Complex MeasureTheory Set
open scoped ENNReal InnerProductSpace

noncomputable section

/-- Squared Burnol L² norm in its integral representative form. -/
theorem burnolL2_norm_sq_eq_integral_norm_sq
    (state : BurnolL2) :
    ‖state‖ ^ 2 = ∫ x : ℝ, ‖state x‖ ^ 2 := by
  have innerIntegrable := MeasureTheory.L2.integrable_inner
    (𝕜 := ℂ) state state
  calc
    ‖state‖ ^ 2 = (inner ℂ state state).re :=
      InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) state
    _ = (∫ x : ℝ, inner ℂ (state x) (state x)).re := by
      rw [MeasureTheory.L2.inner_def]
    _ = ∫ x : ℝ, (inner ℂ (state x) (state x)).re :=
      (integral_re innerIntegrable).symm
    _ = ∫ x : ℝ, ‖state x‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards with x
      rw [inner_self_eq_norm_sq_to_K]
      norm_cast

private theorem quarterMellinL2Feature_coeFn {z : ℂ}
    (value : QuarterMellinL2Test z) :
    (quarterMellinL2Feature z value : ℝ → ℂ) =ᵐ[volume]
      positiveMellinLogQuarterTransform value.1 := by
  exact MemLp.coeFn_toLp value.2.1

private theorem quarterMellinAdditiveHalfDensity_sqNorm
    {z : ℂ} (value : QuarterMellinL2Test z) (x : ℝ) :
    ‖quarterMellinAdditiveHalfDensity value x‖ ^ 2 =
      Real.exp x *
        ‖quarterMellinAdditiveEvenRechartRaw value (Real.exp x)‖ ^ 2 := by
  have featureRead :
      positiveMellinLogQuarterTransform value.1 (-2 * x) =
        (Real.exp ((-2 * x) / 4) : ℂ) *
          positiveMellinExtension value.1 (Real.exp (-2 * x)) := by
    change (Real.exp ((-2 * x) / 4) : ℂ) *
        value.1 ⟨Real.exp (-2 * x), Real.exp_pos _⟩ =
      (Real.exp ((-2 * x) / 4) : ℂ) *
        (if positive : 0 < Real.exp (-2 * x) then
          value.1 ⟨Real.exp (-2 * x), positive⟩ else 0)
    rw [dif_pos (Real.exp_pos _)]
  simp only [quarterMellinAdditiveHalfDensity,
    burnolQuarterFeatureAdditiveRechart]
  rw [featureRead]
  simp only [
    quarterMellinAdditiveEvenRechartRaw, abs_of_pos (Real.exp_pos x),
    quarterMellinAdditivePositiveRechartRaw, smul_eq_mul]
  rw [show Real.exp x ^ (-2 : ℝ) = Real.exp (-2 * x) by
    rw [Real.rpow_def_of_pos (Real.exp_pos x), Real.log_exp]
    congr 1
    ring]
  simp only [positiveMellinExtension]
  rw [show (Real.exp x : ℂ) ^ (-(1 : ℂ)) =
      (Real.exp (-x) : ℂ) by
    simp only [Complex.cpow_neg, Complex.cpow_one]
    simpa using (Complex.exp_neg (x : ℂ)).symm]
  simp only [norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le]
  ring_nf
  have leftExp : Real.exp (x * (-1 / 2 : ℝ)) ^ 2 = Real.exp (-x) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have rightExp : Real.exp x * Real.exp (-x) ^ 2 = Real.exp (-x) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  rw [leftExp]
  conv_lhs => rw [← rightExp]
  ring

private theorem quarterMellinAdditiveHalfDensity_sqNorm_eq_feature
    {z : ℂ} (value : QuarterMellinL2Test z) (x : ℝ) :
    ‖quarterMellinAdditiveHalfDensity value x‖ ^ 2 =
      (1 / 4 : ℝ) *
        ‖positiveMellinLogQuarterTransform value.1 (-2 * x)‖ ^ 2 := by
  unfold quarterMellinAdditiveHalfDensity
    burnolQuarterFeatureAdditiveRechart
  rw [norm_mul]
  norm_num
  ring

private theorem quarterMellinAdditiveEvenRechart_integral_sqNorm_eq_two_positive
    {z : ℂ} (value : QuarterMellinL2Test z) :
    (∫ t : ℝ,
        ‖quarterMellinAdditiveEvenRechartRaw value t‖ ^ 2) =
      2 * ∫ t : ℝ in Ioi 0,
        ‖quarterMellinAdditiveEvenRechartRaw value t‖ ^ 2 := by
  let integrand : ℝ → ℝ := fun t =>
    ‖quarterMellinAdditiveEvenRechartRaw value t‖ ^ 2
  have integrandEven (t : ℝ) : integrand (-t) = integrand t := by
    simp only [integrand]
    rw [quarterMellinAdditiveEvenRechartRaw_neg]
  have integrandIntegrable : Integrable integrand := by
    exact (memLp_two_iff_integrable_sq_norm
      (quarterMellinAdditiveEvenRechartRaw_memLp value).1).mp
        (quarterMellinAdditiveEvenRechartRaw_memLp value)
  have negativeIntegral :
      (∫ t : ℝ in Iic 0, integrand t) =
        ∫ t : ℝ in Ioi 0, integrand t := by
    calc
      (∫ t : ℝ in Iic 0, integrand t) =
          ∫ t : ℝ in Iic 0, integrand (-t) := by
        apply setIntegral_congr_fun measurableSet_Iic
        intro t _
        exact (integrandEven t).symm
      _ = ∫ t : ℝ in Ioi 0, integrand t := by
        simpa only [neg_zero] using integral_comp_neg_Iic 0 integrand
  change (∫ t : ℝ, integrand t) =
    2 * ∫ t : ℝ in Ioi 0, integrand t
  calc
    (∫ t : ℝ, integrand t) =
        (∫ t : ℝ in Iic 0, integrand t) +
          ∫ t : ℝ in Ioi 0, integrand t := by
      rw [← setIntegral_univ, ← Iic_union_Ioi (a := (0 : ℝ)),
        setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi
          integrandIntegrable.integrableOn integrandIntegrable.integrableOn]
    _ = 2 * ∫ t : ℝ in Ioi 0, integrand t := by
      rw [negativeIntegral]
      ring

private theorem quarterMellinAdditive_positive_integral_sqNorm_eq_halfDensity
    {z : ℂ} (value : QuarterMellinL2Test z) :
    (∫ t : ℝ in Ioi 0,
        ‖quarterMellinAdditiveEvenRechartRaw value t‖ ^ 2) =
      ∫ x : ℝ, ‖quarterMellinAdditiveHalfDensity value x‖ ^ 2 := by
  let integrand : ℝ → ℝ := fun t =>
    ‖quarterMellinAdditiveEvenRechartRaw value t‖ ^ 2
  have change := integral_image_eq_integral_abs_deriv_smul
    (f := Real.exp) (f' := Real.exp) (g := integrand)
    (s := (Set.univ : Set ℝ)) MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    (fun _ _ _ _ equality => Real.exp_injective equality)
  change (∫ t : ℝ in Ioi 0, integrand t) = _
  calc
    (∫ t : ℝ in Ioi 0, integrand t) =
        ∫ t : ℝ in Real.exp '' (Set.univ : Set ℝ), integrand t := by
      rw [image_univ, Real.range_exp]
    _ = ∫ x : ℝ in (Set.univ : Set ℝ),
        |Real.exp x| • integrand (Real.exp x) := change
    _ = ∫ x : ℝ, ‖quarterMellinAdditiveHalfDensity value x‖ ^ 2 := by
      rw [Measure.restrict_univ]
      apply integral_congr_ae
      filter_upwards with x
      rw [abs_of_pos (Real.exp_pos x)]
      change Real.exp x *
          ‖quarterMellinAdditiveEvenRechartRaw value (Real.exp x)‖ ^ 2 = _
      exact (quarterMellinAdditiveHalfDensity_sqNorm value x).symm

private theorem quarterMellinAdditive_halfDensity_integral_sqNorm_eq_feature
    {z : ℂ} (value : QuarterMellinL2Test z) :
    (∫ x : ℝ, ‖quarterMellinAdditiveHalfDensity value x‖ ^ 2) =
      (1 / 8 : ℝ) *
        ∫ x : ℝ, ‖positiveMellinLogQuarterTransform value.1 x‖ ^ 2 := by
  let featureIntegrand : ℝ → ℝ := fun x =>
    ‖positiveMellinLogQuarterTransform value.1 x‖ ^ 2
  have scaled := Measure.integral_comp_mul_left featureIntegrand (-2)
  have scaled' :
      (∫ x : ℝ, featureIntegrand (-2 * x)) =
        (1 / 2 : ℝ) * ∫ x : ℝ, featureIntegrand x := by
    simpa [abs_of_nonneg] using scaled
  calc
    (∫ x : ℝ, ‖quarterMellinAdditiveHalfDensity value x‖ ^ 2) =
        ∫ x : ℝ, (1 / 4 : ℝ) * featureIntegrand (-2 * x) := by
      apply integral_congr_ae
      filter_upwards with x
      exact quarterMellinAdditiveHalfDensity_sqNorm_eq_feature value x
    _ = (1 / 4 : ℝ) * ∫ x : ℝ, featureIntegrand (-2 * x) := by
      rw [integral_const_mul]
    _ = (1 / 8 : ℝ) * ∫ x : ℝ, featureIntegrand x := by
      rw [scaled']
      ring

theorem quarterMellinAdditiveEvenRechart_norm
    {z : ℂ} (value : QuarterMellinL2Test z) :
    ‖quarterMellinAdditiveEvenRechart value‖ =
      (1 / 2 : ℝ) * ‖quarterMellinL2Feature z value‖ := by
  have additiveSquare :
      ‖quarterMellinAdditiveEvenRechart value‖ ^ 2 =
        (1 / 4 : ℝ) * ‖quarterMellinL2Feature z value‖ ^ 2 := by
    rw [burnolL2_norm_sq_eq_integral_norm_sq]
    have additiveRead := quarterMellinAdditiveEvenRechart_coeFn value
    have featureRead := quarterMellinL2Feature_coeFn value
    calc
      (∫ x : ℝ, ‖(quarterMellinAdditiveEvenRechart value : ℝ → ℂ) x‖ ^ 2) =
          ∫ x : ℝ, ‖quarterMellinAdditiveEvenRechartRaw value x‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards [additiveRead] with x read
        rw [read]
      _ = 2 * ∫ x : ℝ in Ioi 0,
          ‖quarterMellinAdditiveEvenRechartRaw value x‖ ^ 2 :=
        quarterMellinAdditiveEvenRechart_integral_sqNorm_eq_two_positive value
      _ = 2 * ∫ x : ℝ,
          ‖quarterMellinAdditiveHalfDensity value x‖ ^ 2 := by
        rw [quarterMellinAdditive_positive_integral_sqNorm_eq_halfDensity]
      _ = 2 * ((1 / 8 : ℝ) *
          ∫ x : ℝ,
            ‖positiveMellinLogQuarterTransform value.1 x‖ ^ 2) := by
        rw [quarterMellinAdditive_halfDensity_integral_sqNorm_eq_feature]
      _ = (1 / 4 : ℝ) *
          ∫ x : ℝ, ‖(quarterMellinL2Feature z value : ℝ → ℂ) x‖ ^ 2 := by
        rw [show (∫ x : ℝ,
            ‖positiveMellinLogQuarterTransform value.1 x‖ ^ 2) =
            ∫ x : ℝ,
              ‖(quarterMellinL2Feature z value : ℝ → ℂ) x‖ ^ 2 by
          apply integral_congr_ae
          filter_upwards [featureRead] with x read
          rw [read]]
        ring
      _ = (1 / 4 : ℝ) * ‖quarterMellinL2Feature z value‖ ^ 2 := by
        rw [← burnolL2_norm_sq_eq_integral_norm_sq]
  have additiveNonnegative := norm_nonneg
    (quarterMellinAdditiveEvenRechart value)
  have featureNonnegative := norm_nonneg (quarterMellinL2Feature z value)
  nlinarith

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
