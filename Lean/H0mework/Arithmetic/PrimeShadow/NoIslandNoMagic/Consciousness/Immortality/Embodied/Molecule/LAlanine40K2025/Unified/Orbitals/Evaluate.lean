import H0mework.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Moments

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals
open BasinRefinement GaussianPrimitive GlobalSource MeasureTheory Polynomial
open scoped BigOperators
noncomputable section

def momentValue (alpha : ℝ) : ℕ → ℝ
  | 0 => Real.sqrt (Real.pi/alpha)
  | 1 => 0
  | n+2 => (n+1 : ℝ)/(2*alpha) * momentValue alpha n

theorem moment_evaluated (alpha : ℝ) (positive : 0 < alpha) (n : ℕ) :
    moment alpha n = momentValue alpha n := by
  induction n using Nat.twoStepInduction with
  | zero => exact moment_zero alpha
  | one => exact moment_one alpha positive
  | more n hn _ => rw [moment_step alpha positive n,hn]; rfl

def polynomialMoment (alpha : ℝ) (p : Polynomial ℝ) : ℝ :=
  ∑ n ∈ Finset.range (p.natDegree+1), p.coeff n * momentValue alpha n

/-- The actual polynomial Gaussian integral is evaluated by a finite coefficient/moment program. -/
theorem gaussian_integral_evaluated (alpha : ℝ) (positive : 0 < alpha) (p : Polynomial ℝ) :
    (∫ x : ℝ, GaussianPrimitive.gaussian alpha p x) = polynomialMoment alpha p := by
  have each (n : ℕ) : Integrable (fun x : ℝ => p.coeff n * (x^n * Real.exp (-alpha*x^2))) :=
    (moment_integrable alpha positive n).const_mul _
  have values : GaussianPrimitive.gaussian alpha p =
      fun x : ℝ => ∑ n ∈ Finset.range (p.natDegree+1), p.coeff n * (x^n * Real.exp (-alpha*x^2)) := by
    funext x
    rw [GaussianPrimitive.gaussian,Polynomial.eval_eq_sum_range,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro n _
    ring
  rw [values,integral_finsetSum _ (fun n _ => each n)]
  simp_rw [integral_const_mul]
  change (∑ n ∈ Finset.range (p.natDegree+1), p.coeff n * moment alpha n) = _
  simp_rw [moment_evaluated alpha positive]
  rfl

end
end LAlanine40K2025.UnifiedOrbitals
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
