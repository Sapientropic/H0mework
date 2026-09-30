import Mathlib.MeasureTheory.Integral.IntervalIntegral.TrapezoidalRule

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement

open Set
open scoped Interval

noncomputable section

private theorem withinSecondJet_bound {f : ℝ → ℝ} {a b bound : ℝ}
    (ordered : a < b) (nonnegative : 0 ≤ bound) (regular : ContDiff ℝ 2 f)
    (sourceJet : ∀ x ∈ Icc a b, |iteratedDeriv 2 f x| ≤ bound) :
    ∀ x, |iteratedDerivWithin 2 f [[a, b]] x| ≤ bound := by
  intro x
  by_cases inside : x ∈ [[a, b]]
  · rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc ordered.ne) regular.contDiffAt inside]
    exact sourceJet x (by simpa only [uIcc_of_le ordered.le] using inside)
  · rw [show (2 : Nat) = 1 + 1 from rfl, iteratedDerivWithin_succ,
      derivWithin_zero_of_notMem_closure (by simpa only [uIcc_of_le ordered.le, closure_Icc] using inside),
      abs_zero]
    exact nonnegative

/-- A real bisection uses the same two endpoints and generates one midpoint evaluation. -/
theorem actualBisection_readout (f : ℝ → ℝ) (a b : ℝ) :
    trapezoidal_integral f 2 a b =
      trapezoidal_integral f 1 a ((a + b) / 2) +
        trapezoidal_integral f 1 ((a + b) / 2) b := by
  simp only [trapezoidal_integral_one]
  norm_num [trapezoidal_integral]
  have middle : a + (b - a) / 2 = (a + b) / 2 := by ring
  rw [middle]
  ring

/-- Subordinate consumer: the supplied data bound the actual second derivative, not the error.
The two actual quadratures and their strictly shrinking error budgets are derived. -/
theorem secondJet_generates_bisectedQuadrature (f : ℝ → ℝ) (a b bound : ℝ)
    (ordered : a < b) (positive : 0 < bound) (regular : ContDiff ℝ 2 f)
    (sourceJet : ∀ x ∈ Icc a b, |iteratedDeriv 2 f x| ≤ bound) :
    |trapezoidal_error f 1 a b| ≤ (b - a) ^ 3 * bound / 12 ∧
    |trapezoidal_error f 2 a b| ≤ (b - a) ^ 3 * bound / 48 ∧
    (b - a) ^ 3 * bound / 48 < (b - a) ^ 3 * bound / 12 ∧
    trapezoidal_integral f 2 a b =
      trapezoidal_integral f 1 a ((a + b) / 2) +
        trapezoidal_integral f 1 ((a + b) / 2) b := by
  have jet := withinSecondJet_bound ordered positive.le regular sourceJet
  have coarse := trapezoidal_error_le_of_c2 regular.contDiffOn jet (N := 1) (by decide)
  have fine := trapezoidal_error_le_of_c2 regular.contDiffOn jet (N := 2) (by decide)
  norm_num only [Nat.cast_one, Nat.cast_ofNat, one_pow, mul_one, abs_of_pos (sub_pos.mpr ordered)] at coarse fine
  refine ⟨coarse, ?_, ?_, actualBisection_readout f a b⟩
  · exact fine
  · have mass : 0 < (b - a) ^ 3 * bound := mul_pos (pow_pos (sub_pos.mpr ordered) 3) positive
    linarith

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement
