import Mathlib.MeasureTheory.Integral.DominatedConvergence
import H0mework.Arithmetic.BurnolCarrier.AdditiveSourceIntegral
/-! # Source-side Fourier pairing for the Burnol additive co-sum -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex FourierTransform MeasureTheory Set
open ClozelEndpointSourceEffect
open scoped ENNReal SchwartzMap
noncomputable section
def burnolAdditiveFourierRescaledSummand
    (test : SchwartzMap ℝ ℂ) (n : ℕ) (u : ℝ) : ℂ :=
  FourierTransform.fourier test (((n + 1 : ℕ) : ℝ) * u) *
    burnolAdditiveAnnulusSource u
def burnolAdditiveFourierOriginalSummand
    (test : SchwartzMap ℝ ℂ) (n : ℕ) (t : ℝ) : ℂ :=
  FourierTransform.fourier test t *
    (((n + 1 : ℕ) : ℂ)⁻¹ *
      burnolAdditiveAnnulusSource (t / (n + 1 : ℕ)))
theorem burnolAdditiveFourierRescaledSummand_integrable
    (test : SchwartzMap ℝ ℂ) (n : ℕ) :
    Integrable (burnolAdditiveFourierRescaledSummand test n) := by
  have scaleNe : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have bounded :=
    (scaledSchwartzTest ((n + 1 : ℕ) : ℝ) scaleNe
      (FourierTransform.fourier test)).memLp ∞ volume
  have product := burnolAdditiveAnnulusSource_integrable.mul_of_top_left bounded
  refine product.congr ?_
  exact ae_of_all (volume : Measure ℝ) fun u => by
    change burnolAdditiveAnnulusSource u *
        scaledSchwartzTest ((n + 1 : ℕ) : ℝ) scaleNe
          (FourierTransform.fourier test) u = _
    rw [scaledSchwartzTest_apply, mul_comm]
    rfl
private theorem fourier_scaled_norm_le
    (test : SchwartzMap ℝ ℂ) (n : ℕ) {u : ℝ}
    (sourceNe : burnolAdditiveAnnulusSource u ≠ 0) :
    ‖FourierTransform.fourier test (((n + 1 : ℕ) : ℝ) * u)‖ ≤
      (SchwartzMap.seminorm ℝ 2 0) (FourierTransform.fourier test) /
        (((n + 1 : ℕ) : ℝ) ^ 2) := by
  have notInside : ¬|u| ≤ 1 := by
    intro inside
    exact sourceNe (burnolAdditiveAnnulusSource_zero_of_abs_le_one inside)
  have oneLe : (1 : ℝ) ≤ |u| := le_of_not_ge notInside
  have scalePositive : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  have pointNe : ((n + 1 : ℕ) : ℝ) * u ≠ 0 := by
    apply mul_ne_zero scalePositive.ne'
    intro zero
    subst u
    norm_num at oneLe
  have scaleSqPositive : (0 : ℝ) < (((n + 1 : ℕ) : ℝ) ^ 2) :=
    sq_pos_of_pos scalePositive
  have normPoint :
      ‖((n + 1 : ℕ) : ℝ) * u‖ = ((n + 1 : ℕ) : ℝ) * |u| := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos scalePositive]
  have denominatorOrder : (((n + 1 : ℕ) : ℝ) ^ 2) ≤
      ‖((n + 1 : ℕ) : ℝ) * u‖ ^ 2 := by
    rw [normPoint]
    have scaleLe : ((n + 1 : ℕ) : ℝ) ≤
        ((n + 1 : ℕ) : ℝ) * |u| :=
      (le_mul_iff_one_le_right scalePositive).mpr oneLe
    exact (sq_le_sq₀ scalePositive.le
      (mul_nonneg scalePositive.le (abs_nonneg u))).mpr scaleLe
  have seminormBound := SchwartzMap.norm_pow_mul_le_seminorm ℝ
    (FourierTransform.fourier test) 2 (((n + 1 : ℕ) : ℝ) * u)
  apply (le_div_iff₀ scaleSqPositive).mpr
  calc
    ‖FourierTransform.fourier test (((n + 1 : ℕ) : ℝ) * u)‖ *
        (((n + 1 : ℕ) : ℝ) ^ 2) ≤
      ‖FourierTransform.fourier test (((n + 1 : ℕ) : ℝ) * u)‖ *
        ‖((n + 1 : ℕ) : ℝ) * u‖ ^ 2 :=
      mul_le_mul_of_nonneg_left denominatorOrder (norm_nonneg _)
    _ = ‖((n + 1 : ℕ) : ℝ) * u‖ ^ 2 *
        ‖FourierTransform.fourier test (((n + 1 : ℕ) : ℝ) * u)‖ := by ring
    _ ≤ _ := seminormBound
private theorem rescaledSummand_norm_le
    (test : SchwartzMap ℝ ℂ) (n : ℕ) (u : ℝ) :
    ‖burnolAdditiveFourierRescaledSummand test n u‖ ≤
      ((SchwartzMap.seminorm ℝ 2 0) (FourierTransform.fourier test) /
        (((n + 1 : ℕ) : ℝ) ^ 2)) *
          ‖burnolAdditiveAnnulusSource u‖ := by
  by_cases sourceZero : burnolAdditiveAnnulusSource u = 0
  · simp [burnolAdditiveFourierRescaledSummand, sourceZero]
  · rw [burnolAdditiveFourierRescaledSummand, norm_mul]
    exact mul_le_mul_of_nonneg_right
      (fourier_scaled_norm_le test n sourceZero) (norm_nonneg _)
theorem integral_norm_rescaledSummand_le
    (test : SchwartzMap ℝ ℂ) (n : ℕ) :
    (∫ u : ℝ, ‖burnolAdditiveFourierRescaledSummand test n u‖) ≤
      ((SchwartzMap.seminorm ℝ 2 0) (FourierTransform.fourier test) /
        (((n + 1 : ℕ) : ℝ) ^ 2)) *
          ∫ u : ℝ, ‖burnolAdditiveAnnulusSource u‖ := by
  have coefficientNonnegative : 0 ≤
      (SchwartzMap.seminorm ℝ 2 0) (FourierTransform.fourier test) /
        (((n + 1 : ℕ) : ℝ) ^ 2) := div_nonneg (apply_nonneg _ _) (sq_nonneg _)
  calc
    (∫ u : ℝ, ‖burnolAdditiveFourierRescaledSummand test n u‖) ≤
        ∫ u : ℝ,
          ((SchwartzMap.seminorm ℝ 2 0) (FourierTransform.fourier test) /
            (((n + 1 : ℕ) : ℝ) ^ 2)) *
              ‖burnolAdditiveAnnulusSource u‖ := by
      apply integral_mono
      · exact (burnolAdditiveFourierRescaledSummand_integrable test n).norm
      · exact burnolAdditiveAnnulusSource_integrable.norm.const_mul _
      · exact rescaledSummand_norm_le test n
    _ = _ := by rw [integral_const_mul]
theorem summable_integral_norm_rescaledSummand
    (test : SchwartzMap ℝ ℂ) :
    Summable (fun n : ℕ =>
      ∫ u : ℝ, ‖burnolAdditiveFourierRescaledSummand test n u‖) := by
  let mass : ℝ := ∫ u : ℝ, ‖burnolAdditiveAnnulusSource u‖
  let seminorm : ℝ :=
    (SchwartzMap.seminorm ℝ 2 0) (FourierTransform.fourier test)
  have pSeries : Summable (fun n : ℕ =>
      1 / (((n + 1 : ℕ) : ℝ) ^ 2)) := by
    have shifted :=
      (Real.summable_one_div_nat_add_rpow 1 2).mpr (by norm_num)
    refine shifted.congr ?_
    intro n
    rw [abs_of_nonneg (by positivity), Real.rpow_two]
    norm_num
  have majorant : Summable (fun n : ℕ =>
      seminorm * mass * (1 / (((n + 1 : ℕ) : ℝ) ^ 2))) :=
    pSeries.mul_left (seminorm * mass)
  apply majorant.of_nonneg_of_le
  · intro n
    exact integral_nonneg fun _ => norm_nonneg _
  · intro n
    have bound := integral_norm_rescaledSummand_le test n
    change _ ≤ seminorm * mass * (1 / (((n + 1 : ℕ) : ℝ) ^ 2))
    change _ ≤ (seminorm / (((n + 1 : ℕ) : ℝ) ^ 2)) * mass at bound
    calc
      _ ≤ _ := bound
      _ = _ := by ring
private theorem originalSummand_eq_rescaled_div
    (test : SchwartzMap ℝ ℂ) (n : ℕ) (t : ℝ) :
    burnolAdditiveFourierOriginalSummand test n t =
      (((n + 1 : ℕ) : ℂ)⁻¹) *
        burnolAdditiveFourierRescaledSummand test n
          (t / (n + 1 : ℕ)) := by
  have scaleNe : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  unfold burnolAdditiveFourierOriginalSummand
    burnolAdditiveFourierRescaledSummand
  have argumentEq : ((n + 1 : ℕ) : ℝ) *
      (t / (n + 1 : ℕ)) = t := by
    field_simp [scaleNe]
  rw [argumentEq]
  ring
theorem burnolAdditiveFourierOriginalSummand_integrable
    (test : SchwartzMap ℝ ℂ) (n : ℕ) :
    Integrable (burnolAdditiveFourierOriginalSummand test n) := by
  have scaleNe : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have scaledSource :=
    (burnolAdditiveAnnulusSource_integrable.comp_div scaleNe).const_mul
      (((n + 1 : ℕ) : ℂ)⁻¹)
  have boundedFourier := (FourierTransform.fourier test).memLp ∞ volume
  have product := scaledSource.mul_of_top_left boundedFourier
  refine product.congr ?_
  exact ae_of_all (volume : Measure ℝ) fun t => by
    change (((n + 1 : ℕ) : ℂ)⁻¹ *
        burnolAdditiveAnnulusSource (t / (n + 1 : ℕ))) *
          FourierTransform.fourier test t =
      FourierTransform.fourier test t *
        (((n + 1 : ℕ) : ℂ)⁻¹ *
          burnolAdditiveAnnulusSource (t / (n + 1 : ℕ)))
    ring

theorem integral_originalSummand_eq_rescaledSummand
    (test : SchwartzMap ℝ ℂ) (n : ℕ) :
    (∫ t : ℝ, burnolAdditiveFourierOriginalSummand test n t) =
      ∫ u : ℝ, burnolAdditiveFourierRescaledSummand test n u := by
  have scalePositive : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  calc
    (∫ t : ℝ, burnolAdditiveFourierOriginalSummand test n t) =
        ∫ t : ℝ, (((n + 1 : ℕ) : ℂ)⁻¹) *
          burnolAdditiveFourierRescaledSummand test n
            (t / (n + 1 : ℕ)) := by
      apply integral_congr_ae
      exact ae_of_all (volume : Measure ℝ) fun t =>
        originalSummand_eq_rescaled_div test n t
    _ = (((n + 1 : ℕ) : ℂ)⁻¹) *
        ∫ t : ℝ, burnolAdditiveFourierRescaledSummand test n
          (t / (n + 1 : ℕ)) := by rw [integral_const_mul]
    _ = (((n + 1 : ℕ) : ℂ)⁻¹) *
        (((n + 1 : ℕ) : ℝ) •
          ∫ u : ℝ, burnolAdditiveFourierRescaledSummand test n u) := by
      rw [Measure.integral_comp_div]
      rw [abs_of_pos scalePositive]
    _ = ∫ u : ℝ, burnolAdditiveFourierRescaledSummand test n u := by
      rw [Complex.real_smul]
      push_cast
      field_simp [scalePositive.ne']

private theorem integral_norm_originalSummand_eq_rescaledSummand
    (test : SchwartzMap ℝ ℂ) (n : ℕ) :
    (∫ t : ℝ, ‖burnolAdditiveFourierOriginalSummand test n t‖) =
      ∫ u : ℝ, ‖burnolAdditiveFourierRescaledSummand test n u‖ := by
  have scalePositive : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  calc
    (∫ t : ℝ, ‖burnolAdditiveFourierOriginalSummand test n t‖) =
        ∫ t : ℝ, (((n + 1 : ℕ) : ℝ)⁻¹) *
          ‖burnolAdditiveFourierRescaledSummand test n
            (t / (n + 1 : ℕ))‖ := by
      apply integral_congr_ae
      exact ae_of_all (volume : Measure ℝ) fun t => by
        dsimp only
        rw [originalSummand_eq_rescaled_div, norm_mul, norm_inv]
        rw [norm_natCast]
    _ = (((n + 1 : ℕ) : ℝ)⁻¹) *
        ∫ t : ℝ, ‖burnolAdditiveFourierRescaledSummand test n
          (t / (n + 1 : ℕ))‖ := by rw [integral_const_mul]
    _ = (((n + 1 : ℕ) : ℝ)⁻¹) *
        (((n + 1 : ℕ) : ℝ) *
          ∫ u : ℝ, ‖burnolAdditiveFourierRescaledSummand test n u‖) := by
      have change := Measure.integral_comp_div
        (fun u : ℝ => ‖burnolAdditiveFourierRescaledSummand test n u‖)
        (((n + 1 : ℕ) : ℝ))
      rw [change, abs_of_pos scalePositive]
      rfl
    _ = ∫ u : ℝ, ‖burnolAdditiveFourierRescaledSummand test n u‖ := by
      field_simp [scalePositive.ne']

theorem summable_integral_norm_originalSummand
    (test : SchwartzMap ℝ ℂ) :
    Summable (fun n : ℕ =>
      ∫ t : ℝ, ‖burnolAdditiveFourierOriginalSummand test n t‖) :=
  (summable_integral_norm_rescaledSummand test).congr fun n =>
    (integral_norm_originalSummand_eq_rescaledSummand test n).symm

theorem tsum_originalSummand_eq
    (test : SchwartzMap ℝ ℂ) (t : ℝ) :
    (∑' n : ℕ, burnolAdditiveFourierOriginalSummand test n t) =
      FourierTransform.fourier test t *
        (burnolAdditiveCoSum t + burnolAdditiveNormalization) := by
  let additiveTerm : ℕ → ℂ := fun n =>
    ((n + 1 : ℕ) : ℂ)⁻¹ *
      burnolAdditiveAnnulusSource (t / (n + 1 : ℕ))
  have scaled := (burnolAdditiveCoSum_summable t).tsum_mul_left
    (FourierTransform.fourier test t)
  calc
    (∑' n : ℕ, burnolAdditiveFourierOriginalSummand test n t) =
        ∑' n : ℕ, FourierTransform.fourier test t * additiveTerm n := by
      apply tsum_congr
      intro n
      rfl
    _ = FourierTransform.fourier test t * ∑' n : ℕ, additiveTerm n :=
      scaled
    _ = FourierTransform.fourier test t *
        (burnolAdditiveCoSum t + burnolAdditiveNormalization) := by
      unfold additiveTerm burnolAdditiveCoSum
      ring

private theorem tsum_originalSummand_integrable
    (test : SchwartzMap ℝ ℂ) :
    Integrable (fun t : ℝ =>
      ∑' n : ℕ, burnolAdditiveFourierOriginalSummand test n t) := by
  have productIntegrable :=
    ((FourierTransform.fourier test).memLp 2 volume).integrable_mul
      burnolAdditiveCoSum_memLp_full
  have correctionIntegrable :=
    ((FourierTransform.fourier test).integrable
      (μ := (volume : Measure ℝ))).const_mul
      burnolAdditiveNormalization
  have sumIntegrable := productIntegrable.add correctionIntegrable
  refine sumIntegrable.congr ?_
  exact ae_of_all (volume : Measure ℝ) fun t => by
    dsimp only [Pi.add_apply, Pi.mul_apply]
    rw [tsum_originalSummand_eq]
    ring

/-- First source-side Fourier readback: pairing the additive co-sum with a
Schwartz Fourier transform is the absolutely justified sum of rescaled
source pairings, minus the normalization mode. -/
theorem integral_fourier_mul_additiveCoSum_eq
    (test : SchwartzMap ℝ ℂ) :
    (∫ t : ℝ, FourierTransform.fourier test t *
        burnolAdditiveCoSum t) =
      (∑' n : ℕ, ∫ u : ℝ,
        burnolAdditiveFourierRescaledSummand test n u) -
        burnolAdditiveNormalization *
          ∫ t : ℝ, FourierTransform.fourier test t := by
  have correctionIntegrable :=
    ((FourierTransform.fourier test).integrable
      (μ := (volume : Measure ℝ))).const_mul
      burnolAdditiveNormalization
  calc
    (∫ t : ℝ, FourierTransform.fourier test t *
        burnolAdditiveCoSum t) =
      ∫ t : ℝ,
        (∑' n : ℕ, burnolAdditiveFourierOriginalSummand test n t) -
          burnolAdditiveNormalization *
            FourierTransform.fourier test t := by
      apply integral_congr_ae
      exact ae_of_all (volume : Measure ℝ) fun t => by
        dsimp only
        rw [tsum_originalSummand_eq]
        ring
    _ = (∫ t : ℝ,
          ∑' n : ℕ, burnolAdditiveFourierOriginalSummand test n t) -
        ∫ t : ℝ, burnolAdditiveNormalization *
          FourierTransform.fourier test t := by
      rw [integral_sub (tsum_originalSummand_integrable test)
        correctionIntegrable]
    _ = (∑' n : ℕ, ∫ t : ℝ,
          burnolAdditiveFourierOriginalSummand test n t) -
        burnolAdditiveNormalization *
          ∫ t : ℝ, FourierTransform.fourier test t := by
      rw [← integral_tsum_of_summable_integral_norm
        (burnolAdditiveFourierOriginalSummand_integrable test)
        (summable_integral_norm_originalSummand test),
        integral_const_mul]
    _ = _ := by
      congr 1
      apply tsum_congr
      exact integral_originalSummand_eq_rescaledSummand test

def burnolAdditiveFourierPairedSummand
    (test : SchwartzMap ℝ ℂ) (n : ℕ) (u : ℝ) : ℂ :=
  burnolAdditiveFourierRescaledSummand test n u +
    burnolAdditiveFourierRescaledSummand test n (-u)

private theorem pairedSummand_integrable
    (test : SchwartzMap ℝ ℂ) (n : ℕ) :
    Integrable (burnolAdditiveFourierPairedSummand test n) := by
  have base := burnolAdditiveFourierRescaledSummand_integrable test n
  have reflected := base.comp_mul_left' (by norm_num : (-1 : ℝ) ≠ 0)
  have reflected' : Integrable (fun u : ℝ =>
      burnolAdditiveFourierRescaledSummand test n (-u)) := by
    convert reflected using 1
    funext u
    congr 2
    ring
  exact base.add reflected'

private theorem integral_rescaled_eq_paired_Ioi
    (test : SchwartzMap ℝ ℂ) (n : ℕ) :
    (∫ u : ℝ, burnolAdditiveFourierRescaledSummand test n u) =
      ∫ u : ℝ in Ioi 0, burnolAdditiveFourierPairedSummand test n u := by
  have base := burnolAdditiveFourierRescaledSummand_integrable test n
  have reflected : Integrable (fun u : ℝ =>
      burnolAdditiveFourierRescaledSummand test n (-u)) := by
    have source := base.comp_mul_left' (by norm_num : (-1 : ℝ) ≠ 0)
    convert source using 1
    funext u
    congr 2
    ring
  have negative : (∫ u : ℝ in Iic 0,
      burnolAdditiveFourierRescaledSummand test n u) =
      ∫ u : ℝ in Ioi 0,
        burnolAdditiveFourierRescaledSummand test n (-u) := by
    simpa only [neg_zero] using
      (integral_comp_neg_Ioi 0
        (burnolAdditiveFourierRescaledSummand test n)).symm
  calc
    (∫ u : ℝ, burnolAdditiveFourierRescaledSummand test n u) =
        (∫ u : ℝ in Iic 0,
          burnolAdditiveFourierRescaledSummand test n u) +
        ∫ u : ℝ in Ioi 0,
          burnolAdditiveFourierRescaledSummand test n u := by
      rw [← setIntegral_univ, ← Iic_union_Ioi (a := (0 : ℝ)),
        setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi
          base.integrableOn base.integrableOn]
    _ = _ := by
      rw [negative, ← integral_add reflected.integrableOn base.integrableOn]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u _
      unfold burnolAdditiveFourierPairedSummand
      ring

private theorem summable_integral_norm_paired_Ioi
    (test : SchwartzMap ℝ ℂ) :
    Summable (fun n : ℕ => ∫ u : ℝ in Ioi 0,
      ‖burnolAdditiveFourierPairedSummand test n u‖) := by
  have majorant :=
    (summable_integral_norm_rescaledSummand test).mul_left 2
  apply majorant.of_nonneg_of_le
  · intro n
    exact integral_nonneg fun _ => norm_nonneg _
  · intro n
    let r := burnolAdditiveFourierRescaledSummand test n
    have rInt : Integrable r :=
      burnolAdditiveFourierRescaledSummand_integrable test n
    have rNegInt : Integrable (fun u : ℝ => r (-u)) := by
      have reflected := rInt.comp_mul_left' (by norm_num : (-1 : ℝ) ≠ 0)
      convert reflected using 1
      funext u
      congr 1
      ring
    calc
      (∫ u : ℝ in Ioi 0,
          ‖burnolAdditiveFourierPairedSummand test n u‖) ≤
          ∫ u : ℝ, ‖burnolAdditiveFourierPairedSummand test n u‖ :=
        setIntegral_le_integral (pairedSummand_integrable test n).norm
          (ae_of_all _ fun _ => norm_nonneg _)
      _ ≤ ∫ u : ℝ, ‖r u‖ + ‖r (-u)‖ := by
        apply integral_mono
        · exact (pairedSummand_integrable test n).norm
        · exact rInt.norm.add rNegInt.norm
        · intro u
          exact norm_add_le _ _
      _ = 2 * ∫ u : ℝ, ‖r u‖ := by
        rw [integral_add rInt.norm rNegInt.norm,
          integral_neg_eq_self (fun u : ℝ => ‖r u‖) volume]
        ring

private theorem tsum_paired_eq_theta
    (test : SchwartzMap ℝ ℂ) {u : ℝ} (positive : 0 < u) :
    (∑' n : ℕ, burnolAdditiveFourierPairedSummand test n u) =
      burnolAdditiveAnnulusSource u *
        coPoissonMuntzThetaNonzero (FourierTransform.fourier test) u := by
  rw [coPoissonMuntzThetaNonzero_eq_positive_tsum
    (FourierTransform.fourier test) positive.ne']
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  unfold burnolAdditiveFourierPairedSummand
    burnolAdditiveFourierRescaledSummand coPoissonMuntzEvenSource
  rw [burnolAdditiveAnnulusSource_even]
  ring_nf

/-- The rescaled pairing series is the positive-source integral against the
full nonzero Fourier theta kernel. -/
theorem tsum_integral_rescaled_eq_positiveTheta
    (test : SchwartzMap ℝ ℂ) :
    (∑' n : ℕ, ∫ u : ℝ,
      burnolAdditiveFourierRescaledSummand test n u) =
      ∫ u : ℝ in Ioi 0, burnolAdditiveAnnulusSource u *
        coPoissonMuntzThetaNonzero (FourierTransform.fourier test) u := by
  calc
    _ = ∑' n : ℕ, ∫ u : ℝ in Ioi 0,
        burnolAdditiveFourierPairedSummand test n u := by
      apply tsum_congr
      exact integral_rescaled_eq_paired_Ioi test
    _ = ∫ u : ℝ in Ioi 0,
        ∑' n : ℕ, burnolAdditiveFourierPairedSummand test n u := by
      rw [← integral_tsum_of_summable_integral_norm
        (fun n => (pairedSummand_integrable test n).integrableOn)
        (summable_integral_norm_paired_Ioi test)]
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u positive
      dsimp only
      rw [tsum_paired_eq_theta test positive]

end

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
