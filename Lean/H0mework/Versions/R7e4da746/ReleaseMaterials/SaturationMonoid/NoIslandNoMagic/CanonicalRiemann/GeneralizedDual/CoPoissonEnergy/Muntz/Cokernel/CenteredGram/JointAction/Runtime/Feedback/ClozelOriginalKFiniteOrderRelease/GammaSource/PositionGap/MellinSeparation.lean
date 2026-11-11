import H0mework.Versions.R7e4da746.Arithmetic.RiemannDivision.AnalyticComplementAmbientMellinEvaluator

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley

open Complex Filter FourierTransform MeasureTheory Set BurnolPhysicalState
open scoped SchwartzMap ContDiff

open private divisionJet_value_ae_eq_gapCoefficient_on_Ioc from
  H0mework.Versions.R7e4da746.Arithmetic.RiemannDivision.AnalyticComplementAmbientMellinEvaluator

local notation "r" => burnolUnscaledCommonGapRadius
local notation "G" => locallyConstantFace r
local notation "M" => burnolAmbientCompletedMellinEvaluator

private def probe (y : ℝ) : BurnolCompletedMellinCoordinate where
  value := (3/4 : ℂ) + ((2*Real.pi*y : ℝ) : ℂ) * Complex.I
  rightHalf := by norm_num [Complex.add_re, Complex.mul_re]
  belowOne := by norm_num [Complex.add_re, Complex.mul_re]

private theorem positive_weight_integrable (d : BurnolCompletedMellinCoordinate) (v : BurnolL2) (gap : v ∈ G) :
    IntegrableOn (fun x : ℝ => (x : ℂ)^(-d.value) * v x) (Ioi 0) := by
  have rPos : 0 < r := by norm_num [burnolUnscaledCommonGapRadius]
  obtain ⟨coefficient, literal⟩ := mem_locallyConstantFace_iff_exists.mp gap
  have exponent : -1 < (-d.value).re := by simp only [Complex.neg_re]; linarith [d.belowOne]
  have power : IntegrableOn (fun x : ℝ => (x : ℂ)^(-d.value)) (Ioc 0 r) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le rPos.le).mp (intervalIntegral.intervalIntegrable_cpow' exponent)
  have head : IntegrableOn (fun x : ℝ => (x : ℂ)^(-d.value) * v x) (Ioc 0 r) := by
    apply (power.mul_const coefficient).congr
    filter_upwards [divisionJet_value_ae_eq_gapCoefficient_on_Ioc r rPos v coefficient literal] with x known
    rw [known]
  rw [← Ioc_union_Ioi_eq_Ioi rPos.le]
  exact head.union (burnolRadiusMellinWeight_integrableOn_tail r rPos d.value d.rightHalf v)

private theorem exp_integral {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : ℝ → E) : (∫ t : ℝ, Real.exp t • f (Real.exp t)) = ∫ x in Ioi (0 : ℝ), f x := by
  have changed := integral_image_eq_integral_abs_deriv_smul (s := univ) MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    (fun x _ y _ equal => Real.exp_injective equal) f
  rw [image_univ, Real.range_exp] at changed
  simpa only [Measure.restrict_univ, abs_of_pos (Real.exp_pos _)] using changed.symm

private theorem exp_integrable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (paid : IntegrableOn f (Ioi (0 : ℝ))) : Integrable (fun t => Real.exp t • f (Real.exp t)) := by
  have changed := integrableOn_image_iff_integrableOn_abs_deriv_smul (s := univ) MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    (fun x _ y _ equal => Real.exp_injective equal) (g := f)
  rw [image_univ, Real.range_exp] at changed
  simpa only [IntegrableOn, Measure.restrict_univ, abs_of_pos (Real.exp_pos _)] using changed.mp paid

private theorem ordinary_fourier_zero (f : ℝ → ℂ) (integrable : Integrable f)
    (gone : 𝓕 f = 0) : ∀ᵐ x ∂volume, f x = 0 := by
  apply ae_eq_zero_of_integral_contDiff_smul_eq_zero integrable.locallyIntegrable
  intro test smooth supported
  have cs : HasCompactSupport (Complex.ofRealCLM ∘ test) := supported.comp_left rfl
  have cd : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ test) := Complex.ofRealCLM.contDiff.comp smooth
  let φ : 𝓢(ℝ, ℂ) := cs.toSchwartzMap cd
  let χ : 𝓢(ℝ, ℂ) := 𝓕⁻ φ
  have pairing : (∫ ξ : ℝ, 𝓕 f ξ • χ ξ) = ∫ x : ℝ, f x • 𝓕 χ x := by
    simpa using! VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℝ)
      Real.continuous_fourierChar continuous_inner integrable χ.integrable
  have inverted : 𝓕 χ = φ := fourier_fourierInv_eq φ
  rw [gone, inverted] at pairing
  simp only [Pi.zero_apply, zero_smul, integral_zero] at pairing
  calc
    (∫ x : ℝ, test x • f x) = ∫ x : ℝ, φ x • f x := rfl
    _ = ∫ x : ℝ, f x • φ x := by simp only [smul_eq_mul, mul_comm]
    _ = 0 := pairing.symm

private theorem exp_cpow (t : ℝ) (z : ℂ) : ((Real.exp t : ℝ) : ℂ)^z = Complex.exp ((t:ℂ)*z) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero t)),
    ← Complex.ofReal_log (Real.exp_nonneg t), Real.log_exp]

/-- The original ambient reads on a vertical line determine the complete even position-gap field. -/
theorem actual_mellin_separates_positionGap (v : BurnolL2) (gap : v ∈ G) (even : reflectL2 v = v)
    (zero : ∀ d : BurnolCompletedMellinCoordinate, d.value.re = 3/4 → M d v = 0) : v = 0 := by
  let base (x : ℝ) := (x : ℂ)^(-(3/4 : ℂ)) * v x
  let logField (t : ℝ) := Real.exp t • base (Real.exp t)
  have source := positive_weight_integrable (probe 0) v gap
  rw [show (probe 0).value = (3/4 : ℂ) by simp [probe]] at source
  have native : Integrable logField := exp_integrable source
  have transform : 𝓕 logField = 0 := by
    funext y
    have read : 𝓕 logField y = M (probe y) v := by
      rw [Real.fourier_real_eq_integral_exp_smul,
        burnolAmbientCompletedMellinEvaluator_eq_positive_integral_of_positionGap _ v gap, ← exp_integral]
      apply integral_congr_ae
      filter_upwards [] with t
      simp only [logField, base, Complex.real_smul, smul_eq_mul, exp_cpow, probe]
      rw [← mul_assoc, mul_comm (Complex.exp (↑(-2 * Real.pi * t * y) * Complex.I)),
        mul_assoc, ← mul_assoc (Complex.exp (↑(-2 * Real.pi * t * y) * Complex.I)), ← Complex.exp_add]
      congr 3
      push_cast
      ring
    exact read.trans (zero (probe y) (by norm_num [probe, Complex.add_re, Complex.mul_re]))
  have gone := ordinary_fourier_zero logField native transform
  have logNorm : (∫ t : ℝ, ‖logField t‖) = 0 := by
    have ae : (fun t => ‖logField t‖) =ᵐ[volume] (0 : ℝ → ℝ) := by
      filter_upwards [gone] with t erased
      change ‖logField t‖ = 0
      rw [erased, norm_zero]
    rw [integral_congr_ae ae, Pi.zero_def, integral_zero]
  have paidNorm : (∫ x in Ioi (0 : ℝ), ‖base x‖) = 0 := by
    rw [← exp_integral]
    simpa only [logField, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), smul_eq_mul] using logNorm
  have normGone := (integral_eq_zero_iff_of_nonneg_ae
    (Eventually.of_forall (fun x : ℝ => norm_nonneg (base x))) (Integrable.norm source)).mp paidNorm
  have positive : ∀ᵐ x ∂volume.restrict (Ioi (0 : ℝ)), v x = 0 := by
    filter_upwards [normGone, ae_restrict_mem measurableSet_Ioi] with x value inside
    have erased : (x : ℂ)^(-(3/4 : ℂ)) * v x = 0 := norm_eq_zero.mp value
    exact (mul_eq_zero.mp erased).resolve_left (Complex.cpow_ne_zero_iff.mpr
      (Or.inl (Complex.ofReal_ne_zero.mpr (ne_of_gt inside))))
  have full := (ae_restrict_iff' measurableSet_Ioi).mp positive
  have reflected := negMeasurePreserving.quasiMeasurePreserving.ae full
  have parity := Lp.coeFn_compMeasurePreserving v negMeasurePreserving
  change (reflectL2 v : ℝ → ℂ) =ᵐ[volume] (v : ℝ → ℂ) ∘ Neg.neg at parity
  rw [even] at parity
  apply Lp.ext
  filter_upwards [full, reflected, parity, volume.ae_ne (0 : ℝ), Lp.coeFn_zero ℂ 2 volume]
    with x pos neg symmetric away zeroRead
  rw [zeroRead]
  rcases lt_or_gt_of_ne away with left | right
  · rw [symmetric]
    exact neg (neg_pos.mpr left)
  · exact pos right

end OriginalKFiniteOrderRelease.PositionGapCayley
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
