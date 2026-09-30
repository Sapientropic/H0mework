import Mathlib.Tactic

/-! Algebraic elimination for the original temporal gauge energy.
Here r = v·v, q = v·S v, d = v·d, and a = v·a_vec.
The source consumer supplies these contractions from the same native Hodge
kernel and its four temporal derivatives. No operator square root is used. -/
set_option autoImplicit false

namespace SourceTemporalStationarity

/-- Unlike the usual quadratic formula, this branch does not divide by B,
which vanishes at the actual source. -/
theorem regular_quadratic_root (B C D : ℝ)
    (discriminant : 0 ≤ C ^ 2 + B * D)
    (source_chart : C + Real.sqrt (C ^ 2 + B * D) ≠ 0) :
    B * (D / (C + Real.sqrt (C ^ 2 + B * D))) ^ 2 +
      2 * C * (D / (C + Real.sqrt (C ^ 2 + B * D))) - D = 0 := by
  have square := Real.sq_sqrt discriminant
  field_simp
  linear_combination -D * square

theorem trace_equation_iff (r q d a h ell t : ℝ)
    (shift : q - ell * r = h * a - d) :
    ell * (1 - r) = t - q - 2 * d ↔ ell = t - h * a - d := by
  constructor <;> intro hypothesis <;> nlinarith

theorem lapse_equation_iff (n r h a₀ a ell : ℝ)
    (chart : 1 - r ≠ 0) (radial : h = n ^ 2 * (1 - r)) :
    ell * (1 - r) = 2 * h * (a₀ + a) ↔ ell = 2 * n ^ 2 * (a₀ + a) := by
  rw [radial]
  constructor
  · intro hypothesis
    apply mul_right_cancel₀ chart
    calc
      ell * (1 - r) = 2 * (n ^ 2 * (1 - r)) * (a₀ + a) := hypothesis
      _ = (2 * n ^ 2 * (a₀ + a)) * (1 - r) := by ring
  · intro hypothesis
    rw [hypothesis]
    ring

theorem reduced_energy (n r h a₀ a ell : ℝ) (nonzero : n ≠ 0)
    (chart : 1 - r ≠ 0) (radial : h = n ^ 2 * (1 - r))
    (lapse : ell * (1 - r) = 2 * h * (a₀ + a)) :
    n * (a₀ + a) + ell / (2 * n) = ell / n := by
  have equation := (lapse_equation_iff n r h a₀ a ell chart radial).mp lapse
  rw [equation]
  field_simp [nonzero]
  ring

theorem reduced_energy_square (n r h a₀ a ell : ℝ) (nonzero : n ≠ 0)
    (chart : 1 - r ≠ 0) (radial : h = n ^ 2 * (1 - r))
    (lapse : ell * (1 - r) = 2 * h * (a₀ + a)) :
    (n * (a₀ + a) + ell / (2 * n)) ^ 2 = 2 * ell * (a₀ + a) := by
  rw [reduced_energy n r h a₀ a ell nonzero chart radial lapse]
  have equation := (lapse_equation_iff n r h a₀ a ell chart radial).mp lapse
  rw [equation]
  field_simp [nonzero]

#print axioms trace_equation_iff
#print axioms regular_quadratic_root
#print axioms lapse_equation_iff
#print axioms reduced_energy
#print axioms reduced_energy_square

end SourceTemporalStationarity
