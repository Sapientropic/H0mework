import H0mework.Chemistry.LAlanineBandGlobalSource.Primitive
import H0mework.Chemistry.LAlanineRefinementDensity.GaussianModel

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.GlobalSource

open SourceGaussianModel
open scoped NNReal
noncomputable section

def factorBound (alpha : ℚ) (power order : ℕ) : ℝ≥0 :=
  ⟨gaussianBound (alpha : ℝ) ((jetPoly alpha power order).map (algebraMap ℚ ℝ)),
    gaussianBound_nonnegative _ _⟩

theorem factor_uniform_bound (alpha : ℚ) (positive : 0 < alpha) (power order : ℕ) (x : ℝ) :
    |factor alpha power order x| ≤ (factorBound alpha power order : ℝ) :=
  gaussian_uniform_bound (by exact_mod_cast positive) _ x

def termBound (term : Term) (d : MultiIndex) : ℝ≥0 :=
  ‖(term.weight : ℝ)‖₊ *
    factorBound term.exponent (term.powers 0) (d 0) *
    factorBound term.exponent (term.powers 1) (d 1) *
    factorBound term.exponent (term.powers 2) (d 2)

theorem term_uniform_bound (term : Term) (positive : 0 < term.exponent) (d : MultiIndex) (x : Point) :
    |value term d x| ≤ (termBound term d : ℝ) := by
  simp only [value, termBound, NNReal.coe_mul, coe_nnnorm, Real.norm_eq_abs, abs_mul]
  exact mul_le_mul
    (mul_le_mul
      (mul_le_mul_of_nonneg_left (factor_uniform_bound _ positive _ _ _) (abs_nonneg _))
      (factor_uniform_bound _ positive _ _ _) (abs_nonneg _) (by positivity))
    (factor_uniform_bound _ positive _ _ _) (abs_nonneg _) (by positivity)

def orbitalBound (terms : List Term) (d : MultiIndex) : ℝ≥0 :=
  (terms.map (fun term => termBound term d)).sum

theorem orbital_uniform_bound (terms : List Term)
    (positive : ∀ term ∈ terms, 0 < term.exponent) (d : MultiIndex) (x : Point) :
    |orbital terms d x| ≤ (orbitalBound terms d : ℝ) := by
  induction terms with
  | nil => simp [orbital, orbitalBound]
  | cons term rest ih =>
    simp only [orbital, orbitalBound, List.map_cons, List.sum_cons, NNReal.coe_add]
    exact (abs_add_le _ _).trans (add_le_add
      (term_uniform_bound term (positive term (by simp)) d x)
      (ih (fun other member => positive other (by simp [member]))))

end
end LAlanine40K2025.BasinRefinement.GlobalSource
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
