import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.RegularQuadrature

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.TrapezoidSource

open Complex Filter MeasureTheory Set
open scoped Topology
noncomputable section
attribute [local instance 1100] NormedSpace.complexToReal
local notation "q" => (1 / 4 : ℝ)

def cell (f : ℝ → ℂ) (a h : ℝ) : ℂ :=
  (h / 2 : ℝ) • (f a + f (a + h)) - ∫ t : ℝ in a..(a + h), f t

/-- The first derivative's actual oscillation controls the complete trapezoid, including both endpoints. -/
theorem cell_bound (f f' : ℝ → ℂ) (a h epsilon : ℝ) (positive : 0 < h) (nonnegative : 0 ≤ epsilon)
    (derivative : ∀ t ∈ Icc a (a + h), HasDerivAt f (f' t) t)
    (oscillation : ∀ t ∈ Icc a (a + h), ‖f' t - f' a‖ ≤ epsilon) :
    ‖cell f a h‖ ≤ 2 * epsilon * h ^ 2 := by
  let remainder := fun t : ℝ => f t - f a - (t - a) • f' a
  have derivativeR (t : ℝ) (inside : t ∈ Icc a (a + h)) :
      HasDerivAt remainder (f' t - f' a) t := by
    have linear := ((hasDerivAt_id t).sub_const a).smul_const (f' a)
    convert! ((derivative t inside).sub_const (f a)).sub linear using 1
    simp only [one_smul]
  have regular : ContinuousOn f (Icc a (a + h)) := fun t inside => (derivative t inside).continuousAt.continuousWithinAt
  have zero : remainder a = 0 := by simp [remainder]
  have bounded (t : ℝ) (inside : t ∈ Icc a (a + h)) : ‖remainder t‖ ≤ epsilon * h := by
    have estimate := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun y hy => (derivativeR y hy).hasDerivWithinAt) oscillation (convex_Icc a (a + h))
      (show a ∈ Icc a (a + h) from ⟨le_rfl, by linarith⟩) inside
    rw [zero, sub_zero, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr inside.1)] at estimate
    exact estimate.trans (mul_le_mul_of_nonneg_left (by linarith [inside.2]) nonnegative)
  have integralLinear : (∫ t : ℝ in a..(a + h), (t - a) • f' a) = (h ^ 2 / 2 : ℝ) • f' a := by
    rw [intervalIntegral.integral_smul_const, intervalIntegral.integral_sub (f := fun t : ℝ => t) (g := fun _ => a)
      (continuous_id.intervalIntegrable _ _) intervalIntegrable_const,
      integral_id, intervalIntegral.integral_const]
    congr 1
    simp only [smul_eq_mul]
    ring
  have integralR : (∫ t : ℝ in a..(a + h), remainder t) =
      (∫ t : ℝ in a..(a + h), f t) - h • f a - (h ^ 2 / 2 : ℝ) • f' a := by
    have first : IntervalIntegrable (fun t : ℝ => f t - f a) volume a (a + h) :=
      (regular.intervalIntegrable_of_Icc (by linarith)).sub intervalIntegrable_const
    have linear : IntervalIntegrable (fun t : ℝ => (t - a) • f' a) volume a (a + h) := by
      apply Continuous.intervalIntegrable
      fun_prop
    unfold remainder
    rw [intervalIntegral.integral_sub first linear,
      intervalIntegral.integral_sub (regular.intervalIntegrable_of_Icc (by linarith)) intervalIntegrable_const,
      intervalIntegral.integral_const, add_sub_cancel_left, integralLinear]
  have identity : cell f a h = (h / 2 : ℝ) • remainder (a + h) - ∫ t : ℝ in a..(a + h), remainder t := by
    rw [integralR]
    simp only [cell, remainder, add_sub_cancel_left, Complex.real_smul, ofReal_div, ofReal_ofNat, ofReal_pow]
    ring
  have integralBound : ‖∫ t : ℝ in a..(a + h), remainder t‖ ≤ epsilon * h ^ 2 := by
    have actual := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := a + h)
      (fun t inside => bounded t (Ioc_subset_Icc_self
        (by simpa only [uIoc_of_le (by linarith : a ≤ a + h)] using inside)))
    simpa only [add_sub_cancel_left, abs_of_pos positive, pow_two, mul_assoc] using actual
  rw [identity]
  have endpoint := bounded (a + h) ⟨by linarith, le_rfl⟩
  have scalar : ‖h / 2‖ = h / 2 := Real.norm_of_nonneg (by positivity)
  calc
    _ ≤ ‖(h / 2 : ℝ) • remainder (a + h)‖ + ‖∫ t : ℝ in a..(a + h), remainder t‖ := norm_sub_le _ _
    _ ≤ (h / 2) * (epsilon * h) + epsilon * h ^ 2 := by
      rw [norm_smul, scalar]
      exact add_le_add (mul_le_mul_of_nonneg_left endpoint (by positivity)) integralBound
    _ ≤ _ := by nlinarith [mul_nonneg nonnegative (sq_nonneg h)]

def grid (f : ℝ → ℂ) (h : ℝ) (M : ℕ) : ℂ :=
  (∑ n ∈ Finset.Icc 1 M, f ((n : ℝ) * h)) -
    (h : ℂ)⁻¹ * (∫ t : ℝ in (0 : ℝ)..((M : ℝ) * h), f t) -
      (f ((M : ℝ) * h) - f 0) / 2

private theorem cell_sum (f : ℝ → ℂ) (regular : ContinuousOn f (Icc 0 q))
    (h : ℝ) (positive : 0 < h) (M : ℕ) (inside : (M : ℝ) * h ≤ q) :
    (∑ n ∈ Finset.range M, cell f ((n : ℝ) * h) h) =
      (h : ℂ) * (∑ n ∈ Finset.Icc 1 M, f ((n : ℝ) * h)) -
        (h : ℂ) / 2 * (f ((M : ℝ) * h) - f 0) -
          ∫ t : ℝ in (0 : ℝ)..((M : ℝ) * h), f t := by
  induction M with
  | zero => simp
  | succ M previous =>
    have before : (M : ℝ) * h ≤ q := by
      have : (M : ℝ) ≤ M + 1 := by linarith
      exact (mul_le_mul_of_nonneg_right this positive.le).trans (by simpa only [Nat.cast_add, Nat.cast_one] using inside)
    have first : IntervalIntegrable f volume 0 ((M : ℝ) * h) :=
      (regular.mono (Icc_subset_Icc le_rfl before)).intervalIntegrable_of_Icc (by positivity)
    have second : IntervalIntegrable f volume ((M : ℝ) * h) ((M : ℝ) * h + h) :=
      (regular.mono (Icc_subset_Icc (by positivity) (by simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul] using inside))).intervalIntegrable_of_Icc (by linarith)
    have split := intervalIntegral.integral_add_adjacent_intervals first second
    rw [Finset.sum_range_succ, previous before, cell, Finset.sum_Icc_succ_top (by omega)]
    simp only [Nat.cast_add, Nat.cast_one, add_mul, one_mul, Complex.real_smul, ofReal_div, ofReal_ofNat]
    rw [← split]
    ring

theorem grid_bound (f f' : ℝ → ℂ) (regular : ContinuousOn f (Icc 0 q))
    (derivative : ∀ t ∈ Icc 0 q, HasDerivAt f (f' t) t)
    (h epsilon : ℝ) (positive : 0 < h) (nonnegative : 0 ≤ epsilon) (M : ℕ)
    (inside : (M : ℝ) * h ≤ q)
    (oscillation : ∀ x ∈ Icc 0 q, ∀ y ∈ Icc 0 q, ‖y - x‖ ≤ h → ‖f' y - f' x‖ ≤ epsilon) :
    ‖grid f h M‖ ≤ 2 * epsilon * q := by
  have scaled : grid f h M = (h : ℂ)⁻¹ * (∑ n ∈ Finset.range M, cell f ((n : ℝ) * h) h) := by
    rw [cell_sum f regular h positive M inside]
    unfold grid
    field_simp [Complex.ofReal_ne_zero.mpr positive.ne']
    simp only [mul_comm h]
    ring
  have cellBound (n : ℕ) (member : n ∈ Finset.range M) :
      ‖cell f ((n : ℝ) * h) h‖ ≤ 2 * epsilon * h ^ 2 := by
    have upper : (n : ℝ) * h + h ≤ q := by
      have index : (n : ℝ) + 1 ≤ M := by exact_mod_cast Finset.mem_range.mp member
      exact (show (n : ℝ) * h + h ≤ (M : ℝ) * h by nlinarith).trans inside
    have start : (n : ℝ) * h ∈ Icc 0 q := ⟨by positivity, by linarith⟩
    have subset : Icc ((n : ℝ) * h) ((n : ℝ) * h + h) ⊆ Icc 0 q :=
      Icc_subset_Icc start.1 upper
    apply cell_bound f f' ((n : ℝ) * h) h epsilon positive nonnegative
      (fun t located => derivative t (subset located))
    intro t located
    apply oscillation _ start t (subset located)
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr located.1)]
    linarith [located.2]
  rw [scaled, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos positive]
  calc
    _ ≤ h⁻¹ * (∑ n ∈ Finset.range M, ‖cell f ((n : ℝ) * h) h‖) :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr positive.le)
    _ ≤ h⁻¹ * (∑ _n ∈ Finset.range M, 2 * epsilon * h ^ 2) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum cellBound) (inv_nonneg.mpr positive.le)
    _ = 2 * epsilon * ((M : ℝ) * h) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left inside (by positivity)

end
end OriginalRieszFinitePairing.CoPoisson.Ward.TrapezoidSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
