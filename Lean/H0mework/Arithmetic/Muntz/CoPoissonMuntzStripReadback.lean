import H0mework.Arithmetic.Muntz.CoPoissonMuntzWeakFEPair

/-!
# Critical-strip readback of the arbitrary-Schwartz Müntz pair

On the open strip, the actual scale remainder differs from the modified theta
kernel by the two canonical pole corrections on complementary half-lines.
Their Mellin values identify the actual remainder transform with the same
weak-FE `Λ`, modulo only the null singleton at scale one.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace ClozelGeneralizedDual

open Complex FourierTransform MeasureTheory Set Filter Asymptotics
open ClozelEndpointSourceEffect
open scoped SchwartzMap RealInnerProductSpace Topology

noncomputable section

private theorem hasMellin_cpow_neg_one_Ioi_one
    {s : ℂ} (belowOne : s.re < 1) :
    HasMellin
      (Set.indicator (Ioi (1 : ℝ))
        (fun t : ℝ => (t : ℂ) ^ (-(1 : ℂ))))
      s (1 / (1 - s)) := by
  let highPower : ℝ → ℂ := fun t => (t : ℂ) ^ (s - 2)
  have exponentBound : (s - 2).re < -1 := by
    norm_num [Complex.sub_re]
    linarith
  have highIntegrable : IntegrableOn highPower (Ioi (1 : ℝ)) := by
    exact integrableOn_Ioi_cpow_of_lt exponentBound one_pos
  have integrandEq : EqOn
      (fun t : ℝ => (t : ℂ) ^ (s - 1) *
        Set.indicator (Ioi (1 : ℝ))
          (fun u : ℝ => (u : ℂ) ^ (-(1 : ℂ))) t)
      (Set.indicator (Ioi (1 : ℝ)) highPower) (Ioi 0) := by
    intro t positive
    change (t : ℂ) ^ (s - 1) *
        Set.indicator (Ioi (1 : ℝ))
          (fun u : ℝ => (u : ℂ) ^ (-(1 : ℂ))) t =
      Set.indicator (Ioi (1 : ℝ)) highPower t
    by_cases high : 1 < t
    · simp only [Set.indicator_apply, mem_Ioi, if_pos high]
      dsimp only [highPower]
      rw [← Complex.cpow_add _ _ (ofReal_ne_zero.mpr positive.ne')]
      congr 2
      ring
    · simp only [Set.indicator_apply, mem_Ioi, if_neg high, mul_zero]
  have highIndicatorIntegrable : Integrable
      (Set.indicator (Ioi (1 : ℝ)) highPower) :=
    highIntegrable.integrable_indicator measurableSet_Ioi
  constructor
  · unfold MellinConvergent
    simp only [smul_eq_mul]
    exact (highIndicatorIntegrable.integrableOn).congr_fun integrandEq.symm
      measurableSet_Ioi
  · unfold mellin
    simp only [smul_eq_mul]
    rw [setIntegral_congr_fun measurableSet_Ioi integrandEq]
    rw [integral_indicator measurableSet_Ioi]
    rw [Measure.restrict_restrict_of_subset
      (Ioi_subset_Ioi (show (0 : ℝ) ≤ 1 by norm_num))]
    change (∫ t : ℝ in Ioi (1 : ℝ), (t : ℂ) ^ (s - 2)) = _
    rw [integral_Ioi_cpow_of_lt exponentBound one_pos]
    norm_num
    rw [show s - 2 + 1 = -(1 - s) by ring]
    simp only [neg_div, one_div]
    rw [show 1 - s = -(s - 1) by ring, inv_neg]
    simp

private theorem coPoissonMuntz_fourier_zero
    (test : SchwartzMap ℝ ℂ) :
    FourierTransform.fourier test 0 = ∫ x : ℝ, test x := by
  rw [SchwartzMap.fourier_coe, Real.fourier_real_eq]
  simp

def coPoissonMuntzLowCorrection
    (test : SchwartzMap ℝ ℂ) : ℝ → ℂ :=
  Set.indicator (Ioc (0 : ℝ) 1) (fun _ => test 0)

def coPoissonMuntzHighCorrection
    (test : SchwartzMap ℝ ℂ) : ℝ → ℂ :=
  Set.indicator (Ioi (1 : ℝ)) (fun t =>
    (t : ℂ) ^ (-(1 : ℂ)) * FourierTransform.fourier test 0)

private theorem coPoissonMuntzLowCorrection_hasMellin
    (test : SchwartzMap ℝ ℂ) {s : ℂ} (positive : 0 < s.re) :
    HasMellin (coPoissonMuntzLowCorrection test) s
      ((1 / s) * test 0) := by
  have base := hasMellin_one_Ioc positive
  have scaled := hasMellin_const_smul (R := ℂ) base.1 (test 0)
  rw [base.2] at scaled
  have functionEq : coPoissonMuntzLowCorrection test =
      fun t => test 0 * Set.indicator (Ioc (0 : ℝ) 1)
        (fun _ => (1 : ℂ)) t := by
    funext t
    by_cases ht : t ∈ Ioc (0 : ℝ) 1 <;>
      simp [coPoissonMuntzLowCorrection, ht]
  rw [functionEq]
  have scaled' : HasMellin
      (fun t => test 0 * Set.indicator (Ioc (0 : ℝ) 1)
        (fun _ => (1 : ℂ)) t) s (test 0 * (1 / s)) := by
    simpa only [smul_eq_mul] using scaled
  exact ⟨scaled'.1, scaled'.2.trans (by ring)⟩

private theorem coPoissonMuntzHighCorrection_hasMellin
    (test : SchwartzMap ℝ ℂ) {s : ℂ} (belowOne : s.re < 1) :
    HasMellin (coPoissonMuntzHighCorrection test) s
      ((1 / (1 - s)) * FourierTransform.fourier test 0) := by
  have base := hasMellin_cpow_neg_one_Ioi_one belowOne
  have scaled := hasMellin_const_smul (R := ℂ) base.1
    (FourierTransform.fourier test 0)
  rw [base.2] at scaled
  have functionEq : coPoissonMuntzHighCorrection test =
      fun t => FourierTransform.fourier test 0 *
        Set.indicator (Ioi (1 : ℝ))
          (fun u : ℝ => (u : ℂ) ^ (-(1 : ℂ))) t := by
    funext t
    by_cases ht : t ∈ Ioi (1 : ℝ) <;>
      simp [coPoissonMuntzHighCorrection,
        ht, mul_comm]
  rw [functionEq]
  have scaled' : HasMellin
      (fun t => FourierTransform.fourier test 0 *
        Set.indicator (Ioi (1 : ℝ))
          (fun u : ℝ => (u : ℂ) ^ (-(1 : ℂ))) t)
      s (FourierTransform.fourier test 0 * (1 / (1 - s))) := by
    simpa only [smul_eq_mul] using scaled
  exact ⟨scaled'.1, scaled'.2.trans (by ring)⟩

theorem coPoissonMuntzScaleRemainder_mellin_eq_weakFEPair
    (test : SchwartzMap ℝ ℂ) (s : ℂ)
    (positive : 0 < s.re) (belowOne : s.re < 1) :
    mellin (coPoissonMuntzScaleRemainder test) s =
      (coPoissonMuntzWeakFEPair test).Λ s := by
  let P := coPoissonMuntzWeakFEPair test
  have modified : HasMellin P.f_modif s (P.Λ₀ s) := by
    have source := P.isStrongFEPair_toStrongFEPair.hasMellin s
    have valueEq : P.toStrongFEPair.Λ s = P.Λ₀ s := by
      rw [P.isStrongFEPair_toStrongFEPair.Λ_eq]
      rfl
    change HasMellin P.f_modif s (P.toStrongFEPair.Λ s) at source
    rwa [valueEq] at source
  have low := coPoissonMuntzLowCorrection_hasMellin test positive
  have high := coPoissonMuntzHighCorrection_hasMellin test belowOne
  have relationEq (scale : ℝ) (scalePositive : 0 < scale)
      (scale_ne_one : scale ≠ 1) :
      coPoissonMuntzScaleRemainder test scale =
        (P.f_modif scale - coPoissonMuntzLowCorrection test scale) -
          coPoissonMuntzHighCorrection test scale := by
    have fourierZero := coPoissonMuntz_fourier_zero test
    rw [coPoissonMuntzScaleRemainder_eq test scalePositive]
    rcases lt_or_gt_of_ne scale_ne_one with lower | upper
    · have inIoo : scale ∈ Ioo (0 : ℝ) 1 := ⟨scalePositive, lower⟩
      have inIoc : scale ∈ Ioc (0 : ℝ) 1 := ⟨scalePositive, lower.le⟩
      have notIoi : scale ∉ Ioi (1 : ℝ) := not_lt_of_ge lower.le
      simp [P, WeakFEPair.f_modif, coPoissonMuntzWeakFEPair,
        coPoissonMuntzTheta, coPoissonMuntzLowCorrection,
        coPoissonMuntzHighCorrection,
        inIoo, inIoc, notIoi, Real.rpow_neg_one, fourierZero]
      ring
    · have inIoi : scale ∈ Ioi (1 : ℝ) := upper
      have notIoo : scale ∉ Ioo (0 : ℝ) 1 := fun member =>
        (lt_asymm upper member.2)
      have notIoc : scale ∉ Ioc (0 : ℝ) 1 := fun member =>
        (not_le_of_gt upper member.2)
      simp [P, WeakFEPair.f_modif, coPoissonMuntzWeakFEPair,
        coPoissonMuntzTheta, coPoissonMuntzLowCorrection,
        coPoissonMuntzHighCorrection,
        inIoi, notIoo, notIoc, Real.rpow_neg_one, fourierZero]
      left
      rw [Complex.cpow_neg, Complex.cpow_one]
  have firstDifference := hasMellin_sub modified.1 low.1
  rw [modified.2, low.2] at firstDifference
  have secondDifference := hasMellin_sub firstDifference.1 high.1
  rw [firstDifference.2, high.2] at secondDifference
  have combined : HasMellin
      (fun scale =>
        (P.f_modif scale - coPoissonMuntzLowCorrection test scale) -
          coPoissonMuntzHighCorrection test scale)
      s (((P.Λ₀ s - (1 / s) * test 0) -
        (1 / (1 - s)) * FourierTransform.fourier test 0)) := by
    exact secondDifference
  have almostEverywhereNeOne : ∀ᵐ scale : ℝ ∂volume, scale ≠ 1 := by
    exact compl_mem_ae_iff.mpr
      (Subsingleton.measure_zero (s := ({1} : Set ℝ)) (by simp) volume)
  have relationAE : coPoissonMuntzScaleRemainder test =ᵐ[
      volume.restrict (Ioi 0)]
      fun scale =>
        (P.f_modif scale - coPoissonMuntzLowCorrection test scale) -
          coPoissonMuntzHighCorrection test scale := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi,
      ae_restrict_of_ae almostEverywhereNeOne] with scale scalePositive scale_ne_one
    exact relationEq scale scalePositive scale_ne_one
  have mellinEq : mellin (coPoissonMuntzScaleRemainder test) s =
      mellin (fun scale =>
        (P.f_modif scale - coPoissonMuntzLowCorrection test scale) -
          coPoissonMuntzHighCorrection test scale) s := by
    unfold mellin
    apply integral_congr_ae
    filter_upwards [relationAE] with scale equality
    rw [equality]
  rw [mellinEq, combined.2]
  change ((P.Λ₀ s - (1 / s) * test 0) -
      (1 / (1 - s)) * FourierTransform.fourier test 0) = P.Λ s
  simp only [WeakFEPair.Λ, P, coPoissonMuntzWeakFEPair,
    one_div, smul_eq_mul]
  norm_num

end

end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
