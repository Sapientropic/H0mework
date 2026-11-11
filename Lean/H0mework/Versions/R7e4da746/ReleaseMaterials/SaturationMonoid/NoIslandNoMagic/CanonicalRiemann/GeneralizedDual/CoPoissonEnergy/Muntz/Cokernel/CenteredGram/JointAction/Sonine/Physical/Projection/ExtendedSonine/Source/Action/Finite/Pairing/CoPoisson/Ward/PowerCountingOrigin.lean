import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.RefinedRate
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.SmoothCountingOrigin

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.PowerCountingOrigin

open Complex Filter MeasureTheory Set
open scoped Topology
noncomputable section
attribute [local instance 1100] NormedSpace.complexToReal
local notation "q" => (1 / 4 : ℝ)

def nextEnd (x : ℝ) : ℝ := ((⌊q / x⌋₊ + 1 : ℕ) : ℝ) * x

theorem nextEnd_bounds (x : ℝ) (positive : 0 < x) : q < nextEnd x ∧ nextEnd x - q ≤ x := by
  have old := SmoothCountingOrigin.gridEnd_bounds x positive
  have next := (div_lt_iff₀ positive).mp (Nat.lt_floor_add_one (q / x))
  simp only [nextEnd, Nat.cast_add, Nat.cast_one]
  constructor
  · exact next
  · have upper : (⌊q / x⌋₊ : ℝ) * x ≤ q := old.2.1
    nlinarith [upper]

def error (s : ℂ) (x : ℝ) : ℂ :=
  (∑ n ∈ Finset.Icc 1 ⌊q / x⌋₊, (((n : ℝ) * x : ℝ) : ℂ) ^ (-s)) -
    (x : ℂ)⁻¹ * (q : ℂ) ^ (1 - s) / (1 - s) -
      (q : ℂ) ^ (-s) * ((1 / 2 : ℂ) - ((Int.fract (q / x) : ℝ) : ℂ))

private theorem slope_bound (s : ℂ) (positiveS : 0 < s.re) (x y : ℝ) (lower : q ≤ x) (ordered : x ≤ y) :
    ‖(y : ℂ) ^ (-s) - (x : ℂ) ^ (-s)‖ ≤ ‖s‖ * q ^ (-s.re - 1) * (y - x) := by
  have derivative (t : ℝ) (inside : t ∈ Icc x y) :
      HasDerivAt (fun t : ℝ => (t : ℂ) ^ (-s)) (-s * (t : ℂ) ^ (-s - 1)) t :=
    (Complex.hasStrictDerivAt_cpow_const (c := -s)
      (Complex.ofReal_mem_slitPlane.mpr ((by norm_num : (0 : ℝ) < q).trans_le (lower.trans inside.1)))).hasDerivAt.comp_ofReal
  have bound (t : ℝ) (inside : t ∈ Icc x y) : ‖-s * (t : ℂ) ^ (-s - 1)‖ ≤ ‖s‖ * q ^ (-s.re - 1) := by
    rw [norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos
      ((by norm_num : (0 : ℝ) < q).trans_le (lower.trans inside.1))]
    simp only [sub_re, neg_re, one_re]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (by norm_num)
      (lower.trans inside.1) (by linarith)) (norm_nonneg _)
  have actual := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t inside => (derivative t inside).hasDerivWithinAt) bound (convex_Icc x y)
    (show x ∈ Icc x y from ⟨le_rfl, ordered⟩) (show y ∈ Icc x y from ⟨ordered, le_rfl⟩)
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ordered)] using actual

private theorem error_decomposition (s : ℂ) (below : s.re < 1) (x : ℝ) (positive : 0 < x) :
    error s x = (x : ℂ) ^ (-s) * RefinedRate.adjusted s (⌊q / x⌋₊ + 1) +
      ((q : ℂ) ^ (-s) - (nextEnd x : ℂ) ^ (-s)) / 2 +
      (x : ℂ)⁻¹ * ∫ t : ℝ in q..(nextEnd x), (t : ℂ) ^ (-s) - (q : ℂ) ^ (-s) := by
  let M := ⌊q / x⌋₊
  let N := M + 1
  have basePositive : (0 : ℝ) < N := by exact_mod_cast Nat.succ_pos M
  have counted : (∑ n ∈ Finset.Icc 1 M, (((n : ℝ) * x : ℝ) : ℂ) ^ (-s)) =
      (x : ℂ) ^ (-s) * (∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-s)) := by
    rw [Finset.mul_sum, show Finset.Icc 1 M = Finset.Ico 1 N by simp only [N, Finset.Ico_add_one_right_eq_Icc]]
    apply Finset.sum_congr rfl
    intro n _
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg n) positive.le,
      Complex.ofReal_natCast, mul_comm]
  have continuousTerm : (x : ℂ) ^ (-s) * (N : ℂ) ^ (1 - s) / (1 - s) =
      (x : ℂ)⁻¹ * (nextEnd x : ℂ) ^ (1 - s) / (1 - s) := by
    rw [show -s = (1 - s) - 1 by ring, Complex.cpow_sub _ _ (Complex.ofReal_ne_zero.mpr positive.ne'), cpow_one]
    change _ = (x : ℂ)⁻¹ * (((N : ℝ) * x : ℝ) : ℂ) ^ (1 - s) / (1 - s)
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg basePositive.le positive.le, Complex.ofReal_natCast]
    ring
  have powerProduct : (x : ℂ) ^ (-s) * (N : ℂ) ^ (-s) = (nextEnd x : ℂ) ^ (-s) := by
    change _ = (((N : ℝ) * x : ℝ) : ℂ) ^ (-s)
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg basePositive.le positive.le, Complex.ofReal_natCast]
    ring
  have powerIntegral : (∫ t : ℝ in q..(nextEnd x), (t : ℂ) ^ (-s)) =
      ((nextEnd x : ℂ) ^ (1 - s) - (q : ℂ) ^ (1 - s)) / (1 - s) := by
    rw [integral_cpow (Or.inl (by simp only [neg_re]; linarith)), show -s + 1 = 1 - s by ring]
  have regular : IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ (-s)) volume q (nextEnd x) :=
    intervalIntegral.intervalIntegrable_cpow' (by simp only [neg_re]; linarith)
  have tail : (∫ t : ℝ in q..(nextEnd x), (t : ℂ) ^ (-s) - (q : ℂ) ^ (-s)) =
      ((nextEnd x : ℂ) ^ (1 - s) - (q : ℂ) ^ (1 - s)) / (1 - s) -
        (nextEnd x - q) • (q : ℂ) ^ (-s) := by
    rw [intervalIntegral.integral_sub regular intervalIntegrable_const, powerIntegral, intervalIntegral.integral_const]
  have width : nextEnd x - q = x * (1 - Int.fract (q / x)) := by
    have old := SmoothCountingOrigin.gridEnd_fract x positive
    unfold nextEnd SmoothCountingOrigin.gridEnd at *
    push_cast
    linarith
  change (∑ n ∈ Finset.Icc 1 M, (((n : ℝ) * x : ℝ) : ℂ) ^ (-s)) - _ - _ =
    (x : ℂ) ^ (-s) * RefinedRate.adjusted s N + _ + _
  rw [counted, tail, width, RefinedRate.adjusted, FiniteForcing.coefficient]
  simp only [mul_add, mul_sub, mul_div_assoc]
  simp only [mul_div_assoc] at continuousTerm
  rw [continuousTerm]
  have half : (x : ℂ) ^ (-s) * ((1 / 2 : ℂ) * (N : ℂ) ^ (-s)) =
      (1 / 2 : ℂ) * (nextEnd x : ℂ) ^ (-s) := by rw [← mul_assoc, mul_comm _ (1 / 2 : ℂ), mul_assoc, powerProduct]
  rw [half]
  simp only [Complex.real_smul, ofReal_mul, ofReal_sub, ofReal_one]
  field_simp [Complex.ofReal_ne_zero.mpr positive.ne']
  ring

def bound (s : ℂ) : ℝ := (RefinedRate.constant s + 2 * ‖s‖) * q ^ (-s.re - 1)

theorem error_bound (s : ℂ) (positiveS : 0 < s.re) (below : s.re < 1) (zero : riemannZeta s = 0)
    (x : ℝ) (positive : 0 < x) : ‖error s x‖ ≤ bound s * x := by
  let N := ⌊q / x⌋₊ + 1
  have indexPositive : 0 < N := Nat.succ_pos _
  have basePositive : (0 : ℝ) < N := by exact_mod_cast indexPositive
  have next := nextEnd_bounds x positive
  have notOne : s ≠ 1 := by intro equality; simp [equality] at below
  have constantNonnegative : 0 ≤ RefinedRate.constant s := by unfold RefinedRate.constant; positivity
  have rate := RefinedRate.coefficient_error_bound s positiveS notOne N indexPositive
  rw [zero, sub_zero] at rate
  have arithmetic : ‖(x : ℂ) ^ (-s) * RefinedRate.adjusted s N‖ ≤
      RefinedRate.constant s * q ^ (-s.re - 1) * x := by
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos positive, neg_re]
    have powers : x ^ (-s.re) * (N : ℝ) ^ (-s.re - 1) = (nextEnd x) ^ (-s.re - 1) * x := by
      have powerX : x ^ (-s.re) = x ^ (-s.re - 1) * x := by
        simpa only [sub_add_cancel, Real.rpow_one] using Real.rpow_add positive (-s.re - 1) 1
      change _ = ((N : ℝ) * x) ^ (-s.re - 1) * x
      rw [powerX, Real.mul_rpow basePositive.le positive.le]
      ring
    calc
      _ ≤ x ^ (-s.re) * (RefinedRate.constant s * (N : ℝ) ^ (-s.re - 1)) :=
        mul_le_mul_of_nonneg_left rate (Real.rpow_nonneg positive.le _)
      _ = RefinedRate.constant s * (nextEnd x) ^ (-s.re - 1) * x := by rw [← mul_assoc, mul_comm _ (RefinedRate.constant s), mul_assoc, powers]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (z := -s.re - 1)
          (by norm_num) next.1.le (by linarith)) constantNonnegative) positive.le
  have boundary := slope_bound s positiveS q (nextEnd x) le_rfl next.1.le
  rw [norm_sub_rev] at boundary
  have boundaryBound : ‖((q : ℂ) ^ (-s) - (nextEnd x : ℂ) ^ (-s)) / 2‖ ≤
      (‖s‖ * q ^ (-s.re - 1) * x) / 2 := by
    rw [norm_div, Complex.norm_ofNat]
    exact div_le_div_of_nonneg_right (boundary.trans
      (mul_le_mul_of_nonneg_left next.2 (by positivity))) (by norm_num)
  have integralBound : ‖(x : ℂ)⁻¹ * ∫ t : ℝ in q..(nextEnd x), (t : ℂ) ^ (-s) - (q : ℂ) ^ (-s)‖ ≤
      ‖s‖ * q ^ (-s.re - 1) * x := by
    have actual := intervalIntegral.norm_integral_le_of_norm_le_const (a := q) (b := nextEnd x)
      (C := ‖s‖ * q ^ (-s.re - 1) * x) (f := fun t => (t : ℂ) ^ (-s) - (q : ℂ) ^ (-s))
      (fun t located => by
        have inside : t ∈ Ioc q (nextEnd x) := by simpa only [uIoc_of_le next.1.le] using located
        exact (slope_bound s positiveS q t le_rfl inside.1.le).trans
          (mul_le_mul_of_nonneg_left (by linarith [inside.2, next.2]) (by positivity)))
    rw [abs_of_nonneg (sub_nonneg.mpr next.1.le)] at actual
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos positive]
    calc
      _ ≤ x⁻¹ * (‖s‖ * q ^ (-s.re - 1) * x * (nextEnd x - q)) := mul_le_mul_of_nonneg_left actual (inv_nonneg.mpr positive.le)
      _ = ‖s‖ * q ^ (-s.re - 1) * (nextEnd x - q) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left next.2 (by positivity)
  rw [error_decomposition s below x positive]
  have remainder : 0 ≤ (‖s‖ * q ^ (-s.re - 1) * x) / 2 := by positivity
  exact ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)).trans
    ((add_le_add (add_le_add arithmetic boundaryBound) integralBound).trans (by unfold bound; nlinarith [remainder]))

theorem error_tendsto (s : ℂ) (positive : 0 < s.re) (below : s.re < 1) (zero : riemannZeta s = 0) :
    Tendsto (error s) (𝓝[>] 0) (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have identity : Tendsto (fun x : ℝ => x) (𝓝[>] (0 : ℝ)) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have upper := identity.const_mul (bound s)
  simp only [mul_zero] at upper
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ upper
  filter_upwards [self_mem_nhdsWithin] with x positiveX
  exact error_bound s positive below zero x positiveX

end
end OriginalRieszFinitePairing.CoPoisson.Ward.PowerCountingOrigin
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
