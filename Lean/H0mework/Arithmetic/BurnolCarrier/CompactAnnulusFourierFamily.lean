import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Distribution.Support
import H0mework.Arithmetic.BurnolCarrier.CompactAnnulusAdditiveFamily

/-! # Fourier gap for the compact-annulus additive co-Poisson family -/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open Complex FourierTransform MeasureTheory Set
open ClozelEndpointSourceEffect
open scoped ENNReal SchwartzMap

noncomputable section

theorem burnolCompactAdditiveSource_zero_of_four_le_abs
    (source : burnolCompactAnnulusSource) {t : ℝ} (outside : 4 ≤ |t|) :
    burnolCompactAdditiveSource source t = 0 := by
  have nonzero : t ≠ 0 := by
    intro zero
    subst t
    norm_num at outside
  rw [burnolCompactAdditiveSource, if_neg nonzero, source.2.2.1 t⁻¹]
  · simp
  · rw [abs_inv]
    have positive : 0 < |t| := abs_pos.mpr nonzero
    have inverseOrder := (inv_le_inv₀ positive (by norm_num)).mpr outside
    norm_num at inverseOrder ⊢
    exact inverseOrder

theorem burnolCompactAdditiveSource_measurable
    (source : burnolCompactAnnulusSource) :
    Measurable (burnolCompactAdditiveSource source) := by
  unfold burnolCompactAdditiveSource
  apply Measurable.ite
  · have setEq : {a : ℝ | a = 0} = ({0} : Set ℝ) := by ext a; simp
    rw [setEq]
    exact measurableSet_singleton 0
  · exact measurable_const
  · exact (Complex.measurable_ofReal.comp continuous_abs.measurable).inv.mul
      (source.1.continuous.measurable.comp measurable_inv)

private theorem burnolCompactAdditiveSource_integrable
    (source : burnolCompactAnnulusSource) :
    Integrable (burnolCompactAdditiveSource source) := by
  have onInterval : IntegrableOn (burnolCompactAdditiveSource source)
      (Icc (-4 : ℝ) 4) :=
    IntegrableOn.of_bound (by rw [Real.volume_Icc]; norm_num)
      (burnolCompactAdditiveSource_measurable source).aestronglyMeasurable.restrict
      (4 * (SchwartzMap.seminorm ℝ 0 0) source.1)
      (ae_of_all _ fun t => by
        by_cases inside : |t| ≤ (1 / 4 : ℝ)
        · rw [burnolCompactAdditiveSource_zero_of_abs_le_quarter source inside,
            norm_zero]
          positivity
        · have nonzero : t ≠ 0 := by rintro rfl; simp at inside
          have positive : 0 < |t| := abs_pos.mpr nonzero
          have quarterLe : (1 / 4 : ℝ) ≤ |t| := le_of_not_ge inside
          rw [burnolCompactAdditiveSource, if_neg nonzero, norm_mul]
          calc
            _ ≤ 4 * ‖source.1 t⁻¹‖ := by
              apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
              simp only [norm_inv, norm_real, Real.norm_eq_abs,
                abs_of_nonneg (abs_nonneg t)]
              rw [inv_eq_one_div]
              apply (div_le_iff₀ positive).mpr
              nlinarith
            _ ≤ _ := mul_le_mul_of_nonneg_left
              (SchwartzMap.norm_le_seminorm ℝ source.1 t⁻¹) (by norm_num))
  apply onInterval.integrable_of_forall_notMem_eq_zero
  intro t outside
  apply burnolCompactAdditiveSource_zero_of_four_le_abs source
  change ¬(-4 ≤ t ∧ t ≤ 4) at outside
  rcases lt_or_ge t (-4) with left | left
  · rw [abs_of_neg (by linarith)]
    linarith
  · have right : 4 < t := lt_of_not_ge fun upper => outside ⟨left, upper⟩
    rw [abs_of_nonneg (by linarith)]
    linarith

private theorem burnolCompactAdditiveReciprocalWeightedSource_integrable
    (source : burnolCompactAnnulusSource) :
    Integrable (fun t : ℝ =>
      (t : ℂ)⁻¹ * burnolCompactAdditiveSource source t) := by
  have measurable : AEStronglyMeasurable (fun t : ℝ =>
      (t : ℂ)⁻¹ * burnolCompactAdditiveSource source t) :=
    (Complex.measurable_ofReal.comp measurable_id).inv.mul
      (burnolCompactAdditiveSource_measurable source) |>.aestronglyMeasurable
  apply ((burnolCompactAdditiveSource_integrable source).norm.const_mul 4).mono'
    measurable
  filter_upwards with t
  by_cases inside : |t| ≤ (1 / 4 : ℝ)
  · rw [burnolCompactAdditiveSource_zero_of_abs_le_quarter source inside]
    simp
  · have nonzero : t ≠ 0 := by rintro rfl; simp at inside
    have positive : 0 < |t| := abs_pos.mpr nonzero
    have quarterLe : (1 / 4 : ℝ) ≤ |t| := le_of_not_ge inside
    rw [norm_mul, norm_inv, norm_real, Real.norm_eq_abs]
    calc
      |t|⁻¹ * ‖burnolCompactAdditiveSource source t‖ ≤
          4 * ‖burnolCompactAdditiveSource source t‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        rw [inv_eq_one_div]
        apply (div_le_iff₀ positive).mpr
        nlinarith
      _ = _ := rfl

def burnolCompactAdditiveFourierGapConstant
    (source : burnolCompactAnnulusSource) : ℂ :=
  -(∫ t : ℝ in Ioi 0, burnolCompactAdditiveSource source t)

def burnolCompactFourierRescaledSummand
    (source : burnolCompactAnnulusSource)
    (test : SchwartzMap ℝ ℂ) (n : ℕ) (u : ℝ) : ℂ :=
  FourierTransform.fourier test (((n + 1 : ℕ) : ℝ) * u) *
    burnolCompactAdditiveSource source u

private theorem compact_rescaledSummand_integrable
    (source : burnolCompactAnnulusSource)
    (test : SchwartzMap ℝ ℂ) (n : ℕ) :
    Integrable (burnolCompactFourierRescaledSummand source test n) := by
  have scaleNe : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have bounded :=
    (scaledSchwartzTest ((n + 1 : ℕ) : ℝ) scaleNe
      (FourierTransform.fourier test)).memLp ∞ volume
  refine ((burnolCompactAdditiveSource_integrable source).mul_of_top_left
    bounded).congr ?_
  exact ae_of_all volume fun u => by
    change burnolCompactAdditiveSource source u *
        scaledSchwartzTest ((n + 1 : ℕ) : ℝ) scaleNe
          (FourierTransform.fourier test) u = _
    rw [scaledSchwartzTest_apply]
    simpa [burnolCompactFourierRescaledSummand, add_comm] using
      (mul_comm (burnolCompactAdditiveSource source u)
        (FourierTransform.fourier test (((n + 1 : ℕ) : ℝ) * u)))

private theorem compact_fourier_scaled_norm_le
    (source : burnolCompactAnnulusSource)
    (test : SchwartzMap ℝ ℂ) (n : ℕ) {u : ℝ}
    (sourceNe : burnolCompactAdditiveSource source u ≠ 0) :
    ‖FourierTransform.fourier test (((n + 1 : ℕ) : ℝ) * u)‖ ≤
      16 * (SchwartzMap.seminorm ℝ 2 0) (FourierTransform.fourier test) /
        (((n + 1 : ℕ) : ℝ) ^ 2) := by
  have notInside : ¬|u| ≤ (1 / 4 : ℝ) := fun inside =>
    sourceNe (burnolCompactAdditiveSource_zero_of_abs_le_quarter source inside)
  have quarterLe : (1 / 4 : ℝ) ≤ |u| := le_of_not_ge notInside
  have scalePositive : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  have pointNe : ((n + 1 : ℕ) : ℝ) * u ≠ 0 := by
    apply mul_ne_zero scalePositive.ne'
    rintro rfl
    norm_num at quarterLe
  have seminormBound := SchwartzMap.norm_pow_mul_le_seminorm ℝ
    (FourierTransform.fourier test) 2 (((n + 1 : ℕ) : ℝ) * u)
  have pointNorm : (1 / 16 : ℝ) * (((n + 1 : ℕ) : ℝ) ^ 2) ≤
      ‖((n + 1 : ℕ) : ℝ) * u‖ ^ 2 := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos scalePositive]
    nlinarith [sq_nonneg (((n + 1 : ℕ) : ℝ) * (|u| - 1 / 4))]
  have denomPositive : 0 < (((n + 1 : ℕ) : ℝ) ^ 2) := sq_pos_of_pos scalePositive
  apply (le_div_iff₀ denomPositive).mpr
  calc
    ‖FourierTransform.fourier test (((n + 1 : ℕ) : ℝ) * u)‖ *
        (((n + 1 : ℕ) : ℝ) ^ 2) ≤
      16 * (‖FourierTransform.fourier test (((n + 1 : ℕ) : ℝ) * u)‖ *
        ‖((n + 1 : ℕ) : ℝ) * u‖ ^ 2) := by
          nlinarith [norm_nonneg
            (FourierTransform.fourier test (((n + 1 : ℕ) : ℝ) * u))]
    _ ≤ 16 * (SchwartzMap.seminorm ℝ 2 0)
        (FourierTransform.fourier test) := by
      nlinarith [seminormBound]
    _ = _ := by ring

private theorem compact_summable_integral_norm_rescaled
    (source : burnolCompactAnnulusSource) (test : SchwartzMap ℝ ℂ) :
    Summable (fun n : ℕ => ∫ u : ℝ,
      ‖burnolCompactFourierRescaledSummand source test n u‖) := by
  have pSeries : Summable (fun n : ℕ =>
      1 / (((n + 1 : ℕ) : ℝ) ^ 2)) := by
    have shifted := (Real.summable_one_div_nat_add_rpow 1 2).mpr (by norm_num)
    refine shifted.congr ?_
    intro n
    rw [abs_of_nonneg (by positivity), Real.rpow_two]
    norm_num
  let coefficient := 16 *
    (SchwartzMap.seminorm ℝ 2 0) (FourierTransform.fourier test) *
      ∫ u : ℝ, ‖burnolCompactAdditiveSource source u‖
  apply (pSeries.mul_left coefficient).of_nonneg_of_le
  · intro n
    exact integral_nonneg fun _ => norm_nonneg _
  · intro n
    have integrable := (compact_rescaledSummand_integrable source test n).norm
    have majorantIntegrable :=
      (burnolCompactAdditiveSource_integrable source).norm.const_mul
        (16 * (SchwartzMap.seminorm ℝ 2 0)
          (FourierTransform.fourier test) / (((n + 1 : ℕ) : ℝ) ^ 2))
    calc
      (∫ u : ℝ, ‖burnolCompactFourierRescaledSummand source test n u‖) ≤
          ∫ u : ℝ, (16 * (SchwartzMap.seminorm ℝ 2 0)
            (FourierTransform.fourier test) / (((n + 1 : ℕ) : ℝ) ^ 2)) *
              ‖burnolCompactAdditiveSource source u‖ := by
        apply integral_mono integrable majorantIntegrable
        intro u
        by_cases sourceZero : burnolCompactAdditiveSource source u = 0
        · simp [burnolCompactFourierRescaledSummand, sourceZero]
        · simp only [burnolCompactFourierRescaledSummand, norm_mul]
          change ‖FourierTransform.fourier test
              (((n + 1 : ℕ) : ℝ) * u)‖ *
              ‖burnolCompactAdditiveSource source u‖ ≤ _
          exact mul_le_mul_of_nonneg_right
            (compact_fourier_scaled_norm_le source test n sourceZero)
            (norm_nonneg _)
      _ = coefficient * (1 / (((n + 1 : ℕ) : ℝ) ^ 2)) := by
        rw [integral_const_mul]
        dsimp only [coefficient]
        ring

private theorem compact_source_mul_fourierTheta_eq
    (source : burnolCompactAnnulusSource)
    (test : SchwartzMap ℝ ℂ)
    (testSupport : tsupport test ⊆ Ioo (-(1 / 4 : ℝ)) (1 / 4 : ℝ))
    {u : ℝ} (positive : 0 < u) :
    burnolCompactAdditiveSource source u *
        coPoissonMuntzThetaNonzero (FourierTransform.fourier test) u =
      test 0 * ((u : ℂ)⁻¹ * burnolCompactAdditiveSource source u) -
        FourierTransform.fourier test 0 * burnolCompactAdditiveSource source u := by
  by_cases sourceZero : burnolCompactAdditiveSource source u = 0
  · simp [sourceZero]
  have upper : u < 4 := by
    by_contra notUpper
    exact sourceZero (burnolCompactAdditiveSource_zero_of_four_le_abs source
      (by rw [abs_of_pos positive]; exact le_of_not_gt notUpper))
  have thetaCore : coPoissonMuntzThetaNonzero test u⁻¹ = 0 := by
    unfold coPoissonMuntzThetaNonzero
    rw [show (fun n : {n : ℤ // n ≠ 0} => test (u⁻¹ * (n.1 : ℝ))) = 0 by
      funext n
      by_contra nonzero
      have inside := testSupport (subset_tsupport test nonzero)
      have invQuarter : (1 / 4 : ℝ) < u⁻¹ := by
        rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num]
        exact (inv_lt_inv₀ (by norm_num) positive).mpr upper
      have oneLe : (1 : ℝ) ≤ |(n.1 : ℝ)| := by
        rw [← Int.cast_abs]
        exact_mod_cast Int.one_le_abs n.property
      have absLower : (1 / 4 : ℝ) < |u⁻¹ * (n.1 : ℝ)| := by
        rw [abs_mul, abs_of_pos (inv_pos.mpr positive)]
        exact lt_of_lt_of_le invQuarter
          (le_mul_of_one_le_right (inv_pos.mpr positive).le oneLe)
      exact (not_lt_of_ge absLower.le) (abs_lt.mpr inside)]
    exact tsum_zero
  have poisson := coPoissonMuntzTheta_fourier_equation test positive
  unfold coPoissonMuntzTheta at poisson
  have uNe : (u : ℂ) ≠ 0 := by exact_mod_cast positive.ne'
  simp only [one_div, thetaCore, zero_add, smul_eq_mul] at poisson
  calc
    burnolCompactAdditiveSource source u *
        coPoissonMuntzThetaNonzero (FourierTransform.fourier test) u =
      burnolCompactAdditiveSource source u *
        ((u : ℂ)⁻¹ * test 0 - FourierTransform.fourier test 0) := by
        congr 1
        apply (mul_left_cancel₀ uNe)
        rw [mul_sub, ← mul_assoc, mul_inv_cancel₀ uNe, one_mul,
          eq_sub_iff_add_eq]
        simpa [mul_add] using poisson.symm
    _ = _ := by ring

def burnolCompactFourierOriginalSummand
    (source : burnolCompactAnnulusSource)
    (test : SchwartzMap ℝ ℂ) (n : ℕ) (t : ℝ) : ℂ :=
  FourierTransform.fourier test t *
    (((n + 1 : ℕ) : ℂ)⁻¹ *
      burnolCompactAdditiveSource source (t / (n + 1 : ℕ)))

private theorem compact_originalSummand_integrable
    (source : burnolCompactAnnulusSource)
    (test : SchwartzMap ℝ ℂ) (n : ℕ) :
    Integrable (burnolCompactFourierOriginalSummand source test n) := by
  have scaleNe : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have scaledSource :=
    ((burnolCompactAdditiveSource_integrable source).comp_div scaleNe).const_mul
      (((n + 1 : ℕ) : ℂ)⁻¹)
  have boundedFourier := (FourierTransform.fourier test).memLp ∞ volume
  exact (scaledSource.mul_of_top_left boundedFourier).congr
    (ae_of_all volume fun t => by
      change (((n + 1 : ℕ) : ℂ)⁻¹ *
          burnolCompactAdditiveSource source (t / (n + 1 : ℕ))) *
            FourierTransform.fourier test t = _
      simp only [burnolCompactFourierOriginalSummand]
      ring)

private theorem compact_integral_original_eq_rescaled
    (source : burnolCompactAnnulusSource)
    (test : SchwartzMap ℝ ℂ) (n : ℕ) :
    (∫ t : ℝ, burnolCompactFourierOriginalSummand source test n t) =
      ∫ u : ℝ, burnolCompactFourierRescaledSummand source test n u := by
  have scalePositive : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  let scale : ℝ := (n + 1 : ℕ)
  calc
    (∫ t : ℝ, burnolCompactFourierOriginalSummand source test n t) =
        ∫ t : ℝ, (((n + 1 : ℕ) : ℂ)⁻¹) *
          burnolCompactFourierRescaledSummand source test n
            (t / (n + 1 : ℕ)) := by
      apply integral_congr_ae
      exact ae_of_all volume fun t => by
        unfold burnolCompactFourierOriginalSummand
          burnolCompactFourierRescaledSummand
        have argumentEq : ((n + 1 : ℕ) : ℝ) *
            (t / (n + 1 : ℕ)) = t := by
          field_simp [scalePositive.ne']
        dsimp only [Function.comp_apply]
        rw [argumentEq]
        ring
    _ = (((n + 1 : ℕ) : ℂ)⁻¹) *
        ∫ t : ℝ, burnolCompactFourierRescaledSummand source test n
          (t / (n + 1 : ℕ)) := by rw [integral_const_mul]
    _ = (((n + 1 : ℕ) : ℂ)⁻¹) *
        (((n + 1 : ℕ) : ℝ) •
          ∫ u : ℝ, burnolCompactFourierRescaledSummand source test n u) := by
      rw [Measure.integral_comp_div, abs_of_pos scalePositive]
    _ = _ := by
      rw [Complex.real_smul]
      push_cast
      field_simp [scalePositive.ne']

private theorem compact_integral_norm_original_eq_rescaled
    (source : burnolCompactAnnulusSource)
    (test : SchwartzMap ℝ ℂ) (n : ℕ) :
    (∫ t : ℝ, ‖burnolCompactFourierOriginalSummand source test n t‖) =
      ∫ u : ℝ, ‖burnolCompactFourierRescaledSummand source test n u‖ := by
  have scalePositive : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  calc
    _ = ∫ t : ℝ, (((n + 1 : ℕ) : ℝ)⁻¹) *
        ‖burnolCompactFourierRescaledSummand source test n
          (t / (n + 1 : ℕ))‖ := by
      apply integral_congr_ae
      exact ae_of_all volume fun t => by
        unfold burnolCompactFourierOriginalSummand
          burnolCompactFourierRescaledSummand
        have argumentEq : ((n + 1 : ℕ) : ℝ) *
            (t / (n + 1 : ℕ)) = t := by
          field_simp [scalePositive.ne']
        dsimp only [Function.comp_apply]
        rw [argumentEq]
        simp only [norm_mul, norm_inv, norm_natCast]
        ring
    _ = (((n + 1 : ℕ) : ℝ)⁻¹) *
        ∫ t : ℝ, ‖burnolCompactFourierRescaledSummand source test n
          (t / (n + 1 : ℕ))‖ := by rw [integral_const_mul]
    _ = (((n + 1 : ℕ) : ℝ)⁻¹) * (((n + 1 : ℕ) : ℝ) *
        ∫ u : ℝ, ‖burnolCompactFourierRescaledSummand source test n u‖) := by
      have change := Measure.integral_comp_div
        (fun u : ℝ => ‖burnolCompactFourierRescaledSummand source test n u‖)
        (((n + 1 : ℕ) : ℝ))
      rw [change, abs_of_pos scalePositive]
      simp only [smul_eq_mul]
    _ = _ := by field_simp [scalePositive.ne']

private theorem compact_summable_integral_norm_original
    (source : burnolCompactAnnulusSource) (test : SchwartzMap ℝ ℂ) :
    Summable (fun n : ℕ => ∫ t : ℝ,
      ‖burnolCompactFourierOriginalSummand source test n t‖) :=
  (compact_summable_integral_norm_rescaled source test).congr fun n =>
    (compact_integral_norm_original_eq_rescaled source test n).symm

private theorem compact_tsum_original_eq
    (source : burnolCompactAnnulusSource)
    (test : SchwartzMap ℝ ℂ) (t : ℝ) :
    (∑' n : ℕ, burnolCompactFourierOriginalSummand source test n t) =
      FourierTransform.fourier test t *
        (burnolCompactAdditiveCoSum source t +
          burnolCompactAdditiveNormalization source) := by
  let additiveTerm : ℕ → ℂ := fun n =>
    ((n + 1 : ℕ) : ℂ)⁻¹ *
      burnolCompactAdditiveSource source (t / (n + 1 : ℕ))
  have scaled := (burnolCompactAdditiveCoSum_summable source t).tsum_mul_left
    (FourierTransform.fourier test t)
  calc
    _ = ∑' n : ℕ, FourierTransform.fourier test t * additiveTerm n := by
      apply tsum_congr
      intro n
      rfl
    _ = FourierTransform.fourier test t * ∑' n : ℕ, additiveTerm n := scaled
    _ = _ := by
      unfold additiveTerm burnolCompactAdditiveCoSum
      ring

def burnolCompactFourierPairedSummand
    (source : burnolCompactAnnulusSource)
    (test : SchwartzMap ℝ ℂ) (n : ℕ) (u : ℝ) : ℂ :=
  burnolCompactFourierRescaledSummand source test n u +
    burnolCompactFourierRescaledSummand source test n (-u)

private theorem compact_pairedSummand_integrable
    (source : burnolCompactAnnulusSource)
    (test : SchwartzMap ℝ ℂ) (n : ℕ) :
    Integrable (burnolCompactFourierPairedSummand source test n) := by
  have base := compact_rescaledSummand_integrable source test n
  have reflected : Integrable (fun u : ℝ =>
      burnolCompactFourierRescaledSummand source test n (-u)) := by
    convert base.comp_mul_left' (by norm_num : (-1 : ℝ) ≠ 0) using 1
    funext u
    congr 1
    ring
  exact base.add reflected

private theorem compact_integral_rescaled_eq_paired_Ioi
    (source : burnolCompactAnnulusSource)
    (test : SchwartzMap ℝ ℂ) (n : ℕ) :
    (∫ u : ℝ, burnolCompactFourierRescaledSummand source test n u) =
      ∫ u : ℝ in Ioi 0,
        burnolCompactFourierPairedSummand source test n u := by
  have base := compact_rescaledSummand_integrable source test n
  have reflected : Integrable (fun u : ℝ =>
      burnolCompactFourierRescaledSummand source test n (-u)) := by
    convert base.comp_mul_left' (by norm_num : (-1 : ℝ) ≠ 0) using 1
    funext u
    congr 1
    ring
  have negative : (∫ u : ℝ in Iic 0,
      burnolCompactFourierRescaledSummand source test n u) =
      ∫ u : ℝ in Ioi 0,
        burnolCompactFourierRescaledSummand source test n (-u) := by
    simpa only [neg_zero] using
      (integral_comp_neg_Ioi 0
        (burnolCompactFourierRescaledSummand source test n)).symm
  calc
    _ = (∫ u : ℝ in Iic 0,
          burnolCompactFourierRescaledSummand source test n u) +
        ∫ u : ℝ in Ioi 0,
          burnolCompactFourierRescaledSummand source test n u := by
      rw [← setIntegral_univ, ← Iic_union_Ioi (a := (0 : ℝ)),
        setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi
          base.integrableOn base.integrableOn]
    _ = _ := by
      rw [negative, ← integral_add reflected.integrableOn base.integrableOn]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u _
      unfold burnolCompactFourierPairedSummand
      ring

private theorem compact_summable_integral_norm_paired_Ioi
    (source : burnolCompactAnnulusSource) (test : SchwartzMap ℝ ℂ) :
    Summable (fun n : ℕ => ∫ u : ℝ in Ioi 0,
      ‖burnolCompactFourierPairedSummand source test n u‖) := by
  have majorant :=
    (compact_summable_integral_norm_rescaled source test).mul_left 2
  apply majorant.of_nonneg_of_le
  · intro n
    exact integral_nonneg fun _ => norm_nonneg _
  · intro n
    let r := burnolCompactFourierRescaledSummand source test n
    have rInt : Integrable r := compact_rescaledSummand_integrable source test n
    have rNegInt : Integrable (fun u : ℝ => r (-u)) := by
      convert rInt.comp_mul_left' (by norm_num : (-1 : ℝ) ≠ 0) using 1
      funext u
      congr 1
      ring
    calc
      (∫ u : ℝ in Ioi 0,
          ‖burnolCompactFourierPairedSummand source test n u‖) ≤
          ∫ u : ℝ, ‖burnolCompactFourierPairedSummand source test n u‖ :=
        setIntegral_le_integral
          (compact_pairedSummand_integrable source test n).norm
          (ae_of_all _ fun _ => norm_nonneg _)
      _ ≤ ∫ u : ℝ, ‖r u‖ + ‖r (-u)‖ := by
        apply integral_mono
        · exact (compact_pairedSummand_integrable source test n).norm
        · exact rInt.norm.add rNegInt.norm
        · intro u
          exact norm_add_le _ _
      _ = 2 * ∫ u : ℝ, ‖r u‖ := by
        rw [integral_add rInt.norm rNegInt.norm,
          integral_neg_eq_self (fun u : ℝ => ‖r u‖) volume]
        ring

private theorem compact_tsum_paired_eq_theta
    (source : burnolCompactAnnulusSource)
    (test : SchwartzMap ℝ ℂ) {u : ℝ} (positive : 0 < u) :
    (∑' n : ℕ, burnolCompactFourierPairedSummand source test n u) =
      burnolCompactAdditiveSource source u *
        coPoissonMuntzThetaNonzero (FourierTransform.fourier test) u := by
  rw [coPoissonMuntzThetaNonzero_eq_positive_tsum
    (FourierTransform.fourier test) positive.ne']
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  unfold burnolCompactFourierPairedSummand
    burnolCompactFourierRescaledSummand coPoissonMuntzEvenSource
  rw [burnolCompactAdditiveSource_even]
  ring_nf

private theorem compact_tsum_integral_rescaled_eq_positiveTheta
    (source : burnolCompactAnnulusSource) (test : SchwartzMap ℝ ℂ) :
    (∑' n : ℕ, ∫ u : ℝ,
      burnolCompactFourierRescaledSummand source test n u) =
      ∫ u : ℝ in Ioi 0, burnolCompactAdditiveSource source u *
        coPoissonMuntzThetaNonzero (FourierTransform.fourier test) u := by
  calc
    _ = ∑' n : ℕ, ∫ u : ℝ in Ioi 0,
        burnolCompactFourierPairedSummand source test n u := by
      apply tsum_congr
      exact compact_integral_rescaled_eq_paired_Ioi source test
    _ = ∫ u : ℝ in Ioi 0,
        ∑' n : ℕ, burnolCompactFourierPairedSummand source test n u := by
      rw [← integral_tsum_of_summable_integral_norm
        (fun n => (compact_pairedSummand_integrable source test n).integrableOn)
        (compact_summable_integral_norm_paired_Ioi source test)]
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u positive
      exact compact_tsum_paired_eq_theta source test positive

private theorem compact_tsum_original_integrable
    (source : burnolCompactAnnulusSource) (test : SchwartzMap ℝ ℂ) :
    Integrable (fun t : ℝ =>
      ∑' n : ℕ, burnolCompactFourierOriginalSummand source test n t) := by
  have productIntegrable :=
    ((FourierTransform.fourier test).memLp 2 volume).integrable_mul
      (burnolCompactAdditiveCoSum_memLp_full source)
  have correctionIntegrable :=
    ((FourierTransform.fourier test).integrable (μ := volume)).const_mul
      (burnolCompactAdditiveNormalization source)
  exact (productIntegrable.add correctionIntegrable).congr
    (ae_of_all volume fun t => by
      change FourierTransform.fourier test t *
          burnolCompactAdditiveCoSum source t +
        burnolCompactAdditiveNormalization source *
          FourierTransform.fourier test t =
        ∑' n : ℕ, burnolCompactFourierOriginalSummand source test n t
      rw [compact_tsum_original_eq]
      ring)

theorem burnolCompactAdditiveFourier_pairing_eq_gapConstant
    (source : burnolCompactAnnulusSource)
    (test : SchwartzMap ℝ ℂ)
    (testSupport : tsupport test ⊆ Ioo (-(1 / 4 : ℝ)) (1 / 4 : ℝ)) :
    (∫ t : ℝ, FourierTransform.fourier test t *
        burnolCompactAdditiveCoSum source t) =
      burnolCompactAdditiveFourierGapConstant source * ∫ t : ℝ, test t := by
  have seriesIntegral :
      (∫ t : ℝ, FourierTransform.fourier test t *
          burnolCompactAdditiveCoSum source t) =
        (∑' n : ℕ, ∫ u : ℝ,
          burnolCompactFourierRescaledSummand source test n u) -
          burnolCompactAdditiveNormalization source *
            ∫ t : ℝ, FourierTransform.fourier test t := by
    have correctionIntegrable :=
      ((FourierTransform.fourier test).integrable (μ := volume)).const_mul
        (burnolCompactAdditiveNormalization source)
    calc
      _ = ∫ t : ℝ,
          (∑' n : ℕ, burnolCompactFourierOriginalSummand source test n t) -
            burnolCompactAdditiveNormalization source *
              FourierTransform.fourier test t := by
        apply integral_congr_ae
        exact ae_of_all volume fun t => by
          change FourierTransform.fourier test t *
              burnolCompactAdditiveCoSum source t =
            (∑' n : ℕ,
              burnolCompactFourierOriginalSummand source test n t) -
              burnolCompactAdditiveNormalization source *
                FourierTransform.fourier test t
          rw [compact_tsum_original_eq]
          ring
      _ = (∫ t : ℝ,
          ∑' n : ℕ, burnolCompactFourierOriginalSummand source test n t) -
          ∫ t : ℝ, burnolCompactAdditiveNormalization source *
            FourierTransform.fourier test t := by
        rw [integral_sub (compact_tsum_original_integrable source test)
          correctionIntegrable]
      _ = _ := by
        rw [← integral_tsum_of_summable_integral_norm
          (compact_originalSummand_integrable source test)
          (compact_summable_integral_norm_original source test),
          integral_const_mul]
        congr 1
        apply tsum_congr
        exact compact_integral_original_eq_rescaled source test
  rw [seriesIntegral, compact_tsum_integral_rescaled_eq_positiveTheta]
  have reciprocalIntegrable : IntegrableOn (fun t : ℝ =>
      (t : ℂ)⁻¹ * burnolCompactAdditiveSource source t) (Ioi 0) :=
    (burnolCompactAdditiveReciprocalWeightedSource_integrable source).integrableOn
  have sourceIntegrable : IntegrableOn
      (burnolCompactAdditiveSource source) (Ioi 0) :=
    (burnolCompactAdditiveSource_integrable source).integrableOn
  rw [setIntegral_congr_fun measurableSet_Ioi
      (fun u positive => compact_source_mul_fourierTheta_eq
        source test testSupport positive),
    integral_sub (reciprocalIntegrable.const_mul (test 0))
      (sourceIntegrable.const_mul (FourierTransform.fourier test 0)),
    integral_const_mul, integral_const_mul]
  have fourierZero : FourierTransform.fourier test 0 = ∫ x : ℝ, test x := by
    rw [SchwartzMap.fourier_coe, Real.fourier_real_eq]
    simp
  have integralFourier :
      (∫ x : ℝ, FourierTransform.fourier test x) = test 0 := by
    have twiceFourierZero :
        FourierTransform.fourier (FourierTransform.fourier test) 0 =
          ∫ x : ℝ, FourierTransform.fourier test x := by
      rw [SchwartzMap.fourier_coe, Real.fourier_real_eq]
      simp
    rw [← twiceFourierZero]
    simpa using sonine_fourier_fourier_apply test 0
  rw [fourierZero, integralFourier]
  unfold burnolCompactAdditiveFourierGapConstant
    burnolCompactAdditiveNormalization
  have positiveIntegral :
      (∫ t : ℝ in Ioi 0, source.1 t) =
        (1 / 2 : ℂ) * ∫ t : ℝ, source.1 t := by
    have negative : (∫ t : ℝ in Iic 0, source.1 t) =
        ∫ t : ℝ in Ioi 0, source.1 t := by
      calc
        _ = ∫ t : ℝ in Iic 0, source.1 (-t) := by
          apply setIntegral_congr_fun measurableSet_Iic
          intro t _
          exact (source.2.1 t).symm
        _ = _ := by simpa only [neg_zero] using integral_comp_neg_Iic 0 source.1
    have full : (∫ t : ℝ, source.1 t) =
        2 * ∫ t : ℝ in Ioi 0, source.1 t := by
      calc
        _ = (∫ t : ℝ in Iic 0, source.1 t) +
            ∫ t : ℝ in Ioi 0, source.1 t := by
          rw [← setIntegral_univ, ← Iic_union_Ioi (a := (0 : ℝ)),
            setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi
              source.1.integrable.integrableOn source.1.integrable.integrableOn]
        _ = _ := by rw [negative]; ring
    rw [full]
    ring
  have reciprocalMoment :
      (∫ t : ℝ in Ioi 0,
        (t : ℂ)⁻¹ * burnolCompactAdditiveSource source t) =
        burnolCompactAdditiveNormalization source := by
    have change := MeasureTheory.integral_comp_rpow_Ioi
      (fun y : ℝ => source.1 y) (p := (-1 : ℝ)) (by norm_num)
    calc
      _ = ∫ t : ℝ in Ioi 0,
          (|-1| * t ^ ((-1 : ℝ) - 1)) • source.1 (t ^ (-1 : ℝ)) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        have tNe : t ≠ 0 := ht.ne'
        dsimp only
        rw [burnolCompactAdditiveSource, if_neg tNe]
        rw [abs_of_pos ht, Real.rpow_neg_one]
        simp only [abs_neg, abs_one, one_mul, Complex.real_smul]
        rw [show ((-1 : ℝ) - 1) = -2 by norm_num,
          Real.rpow_neg ht.le, Real.rpow_two]
        push_cast
        field_simp [tNe]
      _ = ∫ y : ℝ in Ioi 0, source.1 y := change
      _ = _ := positiveIntegral.trans (by rfl)
  rw [reciprocalMoment]
  simp only [burnolCompactAdditiveNormalization]
  ring


end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
