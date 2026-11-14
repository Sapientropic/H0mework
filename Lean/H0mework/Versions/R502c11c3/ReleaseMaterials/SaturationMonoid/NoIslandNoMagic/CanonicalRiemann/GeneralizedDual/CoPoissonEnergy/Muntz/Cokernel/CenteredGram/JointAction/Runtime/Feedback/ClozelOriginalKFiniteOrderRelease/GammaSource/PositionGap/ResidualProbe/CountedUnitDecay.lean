import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.DirichletRate
import H0mework.Versions.R7e4da746.Arithmetic.RiemannUnitFourier.Realization
import H0mework.Versions.R7e4da746.Arithmetic.BurnolMellin.FourierSiblingComplementZero

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.CountedUnitDecay

open Complex MeasureTheory Set
open OriginalRieszFinitePairing.CoPoisson.Ward

def tailConstant (c : BurnolCompletedMellinCoordinate) : ℝ :=
  (DirichletRate.constant (1 - c.value) + 1) * (4 : ℝ) ^ (1 - c.value.re)

theorem tailConstant_nonneg (c : BurnolCompletedMellinCoordinate) : 0 ≤ tailConstant c := by
  have positive : 0 < (1 - c.value).re := by
    simp only [sub_re, one_re]
    linarith [c.belowOne]
  unfold tailConstant DirichletRate.constant
  positivity

/-- The complementary zero removes the slow tail of the original radius-four Dirichlet response. -/
theorem tail_bound (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0)
    (x : ℝ) (outside : 4 ≤ |x|) :
    ‖burnolUnitTailDirichletRaw c.value 4 x‖ ≤ tailConstant c * |x|⁻¹ := by
  let y := |x| / 4
  let N := ⌈y⌉₊
  let s := 1 - c.value
  have absPos : 0 < |x| := lt_of_lt_of_le (by norm_num) outside
  have ypos : 0 < y := div_pos absPos (by norm_num)
  have before : y ≤ (N : ℝ) := Nat.le_ceil y
  have width : (N : ℝ) - y ≤ 1 := by
    have next := Nat.ceil_lt_add_one ypos.le
    change (⌈y⌉₊ : ℝ) - y ≤ 1
    linarith
  have Npos : 0 < N := by exact_mod_cast ypos.trans_le before
  have spos : 0 < s.re := by simp only [s, sub_re, one_re]; linarith [c.belowOne]
  have sbound : s.re < 1 := by simp only [s, sub_re, one_re]; linarith [c.rightHalf]
  have reverse : riemannZeta s = 0 := riemannZeta_one_sub_eq_zero_of_rightHalfZero c zero
  have expRe : -s.re = c.value.re - 1 := by simp only [s, sub_re, one_re]; ring
  have count := DirichletRate.coefficient_rate s spos sbound N Npos
  rw [reverse, sub_zero, expRe] at count
  have nonpositive : c.value.re - 1 ≤ 0 := by linarith [c.belowOne]
  have Cnonneg : 0 ≤ DirichletRate.constant s := by unfold DirichletRate.constant; positivity
  have countBound : ‖FiniteForcing.coefficient s N‖ ≤
      DirichletRate.constant s * y ^ (c.value.re - 1) :=
    count.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos ypos before nonpositive) Cnonneg)
  let endpoint := ∫ t : ℝ in y..(N : ℝ), (t : ℂ) ^ (c.value - 1)
  have endpointBound : ‖endpoint‖ ≤ y ^ (c.value.re - 1) := by
    have bound := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := y) (b := (N : ℝ)) (C := y ^ (c.value.re - 1))
      (f := fun t => (t : ℂ) ^ (c.value - 1)) (fun t mem => by
        rw [uIoc_of_le before] at mem
        rw [Complex.norm_cpow_eq_rpow_re_of_pos (ypos.trans mem.1), sub_re, one_re]
        exact Real.rpow_le_rpow_of_nonpos ypos mem.1.le nonpositive)
    rw [abs_of_nonneg (sub_nonneg.mpr before)] at bound
    exact bound.trans (by simpa only [mul_one] using
      mul_le_mul_of_nonneg_left width (Real.rpow_nonneg ypos.le (c.value.re - 1)))
  have endpointRead : endpoint = ((N : ℂ) ^ c.value - (y : ℂ) ^ c.value) / c.value := by
    have localExp : -1 < (c.value - 1).re := by
      simp only [sub_re, one_re]
      linarith [c.rightHalf]
    dsimp only [endpoint]
    rw [integral_cpow (Or.inl localExp), sub_add_cancel,
      Complex.ofReal_natCast]
  have countRead : (∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (c.value - 1)) =
      FiniteForcing.coefficient s N + (N : ℂ) ^ c.value / c.value := by
    unfold FiniteForcing.coefficient s
    rw [show -(1-c.value) = c.value-1 by ring, sub_sub_cancel]
    ring
  have absComplex : (↑|x| : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr absPos.ne'
  have scale : (4 : ℂ) ^ (-c.value) = (↑|x| : ℂ) ^ (-c.value) * (y : ℂ) ^ c.value := by
    have ratio : (y : ℂ) ^ c.value = (↑|x| : ℂ) ^ c.value / (4 : ℂ) ^ c.value := by
      unfold y
      rw [Complex.ofReal_div, Complex.div_cpow_ofReal_nonneg (abs_nonneg x) (by norm_num)]
      norm_num
    have nonzero : (↑|x| : ℂ) ^ c.value ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl absComplex)
    symm
    rw [ratio, Complex.cpow_neg, Complex.cpow_neg, div_eq_mul_inv, ← mul_assoc,
      inv_mul_cancel₀ nonzero, one_mul]
  have actual : burnolUnitTailDirichletRaw c.value 4 x =
      -((↑|x| : ℂ) ^ (-c.value) * (FiniteForcing.coefficient s N + endpoint)) := by
    change (4 : ℂ) ^ (-c.value) / c.value -
      (↑|x| : ℂ) ^ (-c.value) * (∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (c.value - 1)) = _
    rw [endpointRead, countRead, scale]
    ring
  have decay : |x| ^ (-c.value.re) * y ^ (c.value.re - 1) =
      (4 : ℝ) ^ (1 - c.value.re) * |x|⁻¹ := by
    unfold y
    rw [Real.div_rpow absPos.le (by norm_num), div_eq_mul_inv, ← mul_assoc,
      ← Real.rpow_add absPos, show -c.value.re + (c.value.re - 1) = -1 by ring,
      Real.rpow_neg_one, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4),
      show -(c.value.re - 1) = 1 - c.value.re by ring, mul_comm]
  rw [actual, norm_neg, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos absPos, neg_re]
  calc
    _ ≤ |x| ^ (-c.value.re) * (DirichletRate.constant s * y ^ (c.value.re - 1) +
        y ^ (c.value.re - 1)) :=
      mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add countBound endpointBound))
        (Real.rpow_nonneg absPos.le _)
    _ = _ := by
      unfold tailConstant
      change _ = (DirichletRate.constant s + 1) * (4 : ℝ) ^ (1 - c.value.re) * |x|⁻¹
      rw [show |x| ^ (-c.value.re) *
          (DirichletRate.constant s * y ^ (c.value.re - 1) + y ^ (c.value.re - 1)) =
          (DirichletRate.constant s + 1) * (|x| ^ (-c.value.re) * y ^ (c.value.re - 1)) by ring,
        decay, mul_assoc]

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.CountedUnitDecay
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
