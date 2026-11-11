import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.TrapezoidSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.DirichletRate
import Mathlib.Analysis.SumIntegralComparisons

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.RefinedRate

open Complex Filter MeasureTheory Set
open scoped Topology
noncomputable section
attribute [local instance 1100] NormedSpace.complexToReal

def adjusted (s : ℂ) (N : ℕ) : ℂ := FiniteForcing.coefficient s N + (1 / 2 : ℂ) * (N : ℂ) ^ (-s)

theorem increment (s : ℂ) (notOne : s ≠ 1) (N : ℕ) (positive : 0 < N) :
    adjusted s (N + 1) - adjusted s N = TrapezoidSource.cell (fun t : ℝ => (t : ℂ) ^ (-s)) N 1 := by
  have intervalNonzero : (0 : ℝ) ∉ uIcc (N : ℝ) ((N : ℝ) + 1) := by
    rw [uIcc_of_le (by linarith)]
    simp only [mem_Icc, not_and]
    intro impossible
    have : (0 : ℝ) < N := by exact_mod_cast positive
    linarith
  have integral : (∫ t : ℝ in (N : ℝ)..((N : ℝ) + 1), (t : ℂ) ^ (-s)) =
      (((N + 1 : ℕ) : ℂ) ^ (1 - s) - (N : ℂ) ^ (1 - s)) / (1 - s) := by
    rw [integral_cpow (Or.inr ⟨by simpa using notOne, intervalNonzero⟩), show -s + 1 = 1 - s by ring]
    push_cast
    rfl
  rw [adjusted, adjusted, FiniteForcing.coefficient, FiniteForcing.coefficient,
    Finset.sum_Ico_succ_top (by omega), TrapezoidSource.cell, integral]
  simp only [Complex.real_smul, ofReal_div, ofReal_one, ofReal_ofNat, ofReal_add, ofReal_natCast, Nat.cast_add, Nat.cast_one]
  ring

theorem adjusted_tendsto (s : ℂ) (positive : 0 < s.re) (notOne : s ≠ 1) :
    Tendsto (adjusted s) atTop (𝓝 (riemannZeta s)) := by
  have vanishes : Tendsto (fun N : ℕ => (N : ℂ) ^ (-s)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have actual := (tendsto_rpow_neg_atTop positive).comp (tendsto_natCast_atTop_atTop (R := ℝ))
    apply actual.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N after
    rw [Complex.norm_natCast_cpow_of_pos (by omega : 0 < N), neg_re]
    rfl
  have actual := (DirichletCoefficient.coefficient_tendsto_riemannZeta s positive notOne).add
    (vanishes.const_mul (1 / 2 : ℂ))
  unfold adjusted
  simpa only [mul_zero, add_zero] using actual

private theorem power_derivative (s : ℂ) (x : ℝ) (positive : 0 < x) :
    HasDerivAt (fun t : ℝ => (t : ℂ) ^ (-s)) (-s * (x : ℂ) ^ (-s - 1)) x :=
  (Complex.hasStrictDerivAt_cpow_const (c := -s) (Complex.ofReal_mem_slitPlane.mpr positive)).hasDerivAt.comp_ofReal

private theorem slope_derivative (s : ℂ) (x : ℝ) (positive : 0 < x) :
    HasDerivAt (fun t : ℝ => -s * (t : ℂ) ^ (-s - 1))
      (s * (s + 1) * (x : ℂ) ^ (-s - 2)) x := by
  have original := ((Complex.hasStrictDerivAt_cpow_const (c := -s - 1)
    (Complex.ofReal_mem_slitPlane.mpr positive)).hasDerivAt.comp_ofReal).const_mul (-s)
  convert! original using 1
  rw [show -s - 1 - 1 = -s - 2 by ring]
  ring

theorem increment_bound (s : ℂ) (realPositive : 0 < s.re) (notOne : s ≠ 1)
    (N : ℕ) (positive : 0 < N) :
    ‖adjusted s (N + 1) - adjusted s N‖ ≤
      2 * ‖s * (s + 1)‖ * (N : ℝ) ^ (-s.re - 2) := by
  have basePositive : (0 : ℝ) < N := by exact_mod_cast positive
  let L : ℝ := ‖s * (s + 1)‖ * (N : ℝ) ^ (-s.re - 2)
  have bound (t : ℝ) (inside : t ∈ Icc (N : ℝ) ((N : ℝ) + 1)) :
      ‖s * (s + 1) * (t : ℂ) ^ (-s - 2)‖ ≤ L := by
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (basePositive.trans_le inside.1)]
    change ‖s * (s + 1)‖ * t ^ (-s.re - 2) ≤ L
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos basePositive inside.1 (by linarith)) (norm_nonneg _)
  have oscillation (t : ℝ) (inside : t ∈ Icc (N : ℝ) ((N : ℝ) + 1)) :
      ‖(-s * (t : ℂ) ^ (-s - 1)) - (-s * (N : ℂ) ^ (-s - 1))‖ ≤ L := by
    have actual := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun y hy => (slope_derivative s y (basePositive.trans_le hy.1)).hasDerivWithinAt)
      bound (convex_Icc (N : ℝ) ((N : ℝ) + 1)) (show (N : ℝ) ∈ Icc (N : ℝ) ((N : ℝ) + 1) by simp) inside
    simp only [Complex.ofReal_natCast] at actual
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr inside.1)] at actual
    exact actual.trans ((mul_le_mul_of_nonneg_left (by linarith [inside.2] : t - N ≤ 1) (by positivity : 0 ≤ L)).trans_eq (mul_one _))
  rw [increment s notOne N positive]
  have actual := TrapezoidSource.cell_bound (fun t : ℝ => (t : ℂ) ^ (-s))
    (fun t : ℝ => -s * (t : ℂ) ^ (-s - 1)) N 1 L (by norm_num) (by positivity)
    (fun t inside => power_derivative s t (basePositive.trans_le inside.1))
    (by simpa only [Complex.ofReal_natCast] using oscillation)
  simpa only [one_pow, mul_one, L, mul_assoc] using actual

def constant (s : ℂ) : ℝ := 2 * ‖s * (s + 1)‖ * (1 + 1 / (s.re + 1))

set_option maxHeartbeats 600000 in
theorem coefficient_error_bound (s : ℂ) (positive : 0 < s.re) (notOne : s ≠ 1)
    (N : ℕ) (indexPositive : 0 < N) :
    ‖FiniteForcing.coefficient s N - riemannZeta s + (1 / 2 : ℂ) * (N : ℂ) ^ (-s)‖ ≤
      constant s * (N : ℝ) ^ (-s.re - 1) := by
  let f := fun t : ℝ => t ^ (-s.re - 2)
  have basePositive : (0 : ℝ) < N := by exact_mod_cast indexPositive
  have anti : AntitoneOn f (Ici (N : ℝ)) := fun x hx y _ ordered =>
    Real.rpow_le_rpow_of_nonpos (basePositive.trans_le hx) ordered (by linarith)
  have integrable : IntegrableOn f (Ioi (N : ℝ)) :=
    (integrableOn_Ioi_rpow_iff basePositive).mpr (by linarith)
  have nonnegative : ∀ t ∈ Ioi (N : ℝ), 0 ≤ f t := fun t ht => Real.rpow_nonneg (basePositive.trans ht).le _
  have summable := anti.summable_of_integrableOn_Ioi integrable nonnegative
  have shifted : Summable (fun n : ℕ => f ((n + N : ℕ) : ℝ)) :=
    summable.comp_injective (add_left_injective N)
  have tail := anti.tsum_comp_add_le_integral N integrable nonnegative
  have sumBound : (∑' n : ℕ, f ((n + N : ℕ) : ℝ)) ≤
      (1 + 1 / (s.re + 1)) * (N : ℝ) ^ (-s.re - 1) := by
    rw [shifted.tsum_eq_zero_add]
    have normalized : (∑' n : ℕ, f ((n + 1 + N : ℕ) : ℝ)) = ∑' n : ℕ, f ((n + N + 1 : ℕ) : ℝ) := by
      congr 1
      funext n
      congr 2
      omega
    rw [normalized]
    simp only [zero_add]
    have integralRead : (∫ t : ℝ in Ioi (N : ℝ), f t) = (N : ℝ) ^ (-s.re - 1) / (s.re + 1) := by
      rw [integral_Ioi_rpow_of_lt (by linarith : -s.re - 2 < -1) basePositive,
        show -s.re - 2 + 1 = -(s.re + 1) by ring, neg_div_neg_eq]
      congr 1
      congr 1
      ring
    have head : f N ≤ (N : ℝ) ^ (-s.re - 1) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast indexPositive) (by linarith)
    calc
      _ ≤ (N : ℝ) ^ (-s.re - 1) + ∫ t : ℝ in Ioi (N : ℝ), f t := add_le_add head tail
      _ = _ := by rw [integralRead]; ring
  have limit := (adjusted_tendsto s positive notOne).comp
    (tendsto_add_atTop_nat N)
  have distance := dist_le_tsum_of_dist_le_of_tendsto₀
    (fun n : ℕ => 2 * ‖s * (s + 1)‖ * f ((n + N : ℕ) : ℝ))
    (f := fun n : ℕ => adjusted s (n + N)) (fun n => by
      rw [dist_comm, dist_eq_norm]
      simpa only [Nat.succ_eq_add_one, Nat.add_right_comm, f] using
        increment_bound s positive notOne (n + N) (by omega))
    (shifted.mul_left _) limit
  simp only [zero_add, dist_eq_norm, tsum_mul_left] at distance
  have final := distance.trans (mul_le_mul_of_nonneg_left sumBound (by positivity))
  convert! final using 1
  · congr 1
    unfold adjusted
    ring
  · unfold constant
    ring

end
end OriginalRieszFinitePairing.CoPoisson.Ward.RefinedRate
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
