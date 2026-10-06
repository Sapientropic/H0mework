import H0mework.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Rational
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Overlap

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals
open BasinRefinement SourceGaussianModel
open scoped BigOperators

def pairExponent (first second : Term) : ℚ := first.exponent+second.exponent
def pairPenalty (first second : Term) : ℚ :=
  ∑ a : Fin 3, first.exponent*second.exponent / pairExponent first second *
    (first.centre a-second.centre a)^2
noncomputable def pairCoefficient (first second : Term) : ℚ :=
  first.weight * second.weight * ∏ a : Fin 3,
    rationalPolynomialMoment (pairExponent first second)
      (rationalProductPolynomial first.exponent second.exponent (first.centre a) (second.centre a)
        (first.powers a) (second.powers a))

noncomputable def radialKernel (gamma penalty : ℚ) : ℝ :=
  Real.exp (-(penalty : ℝ)) * Real.sqrt (Real.pi/gamma)^3

theorem axis_radial_factor (first second : Term) (a : Fin 3) :
    axisOverlap first second a =
      Real.exp (-productPenalty first.exponent second.exponent (first.centre a) (second.centre a)) *
      (rationalPolynomialMoment (pairExponent first second)
        (rationalProductPolynomial first.exponent second.exponent (first.centre a) (second.centre a)
          (first.powers a) (second.powers a)) : ℝ) *
      Real.sqrt (Real.pi/(pairExponent first second : ℚ)) := by
  unfold axisOverlap
  rw [product_polynomial_rational]
  have gamma : (first.exponent : ℝ)+second.exponent = (pairExponent first second : ℚ) := by
    simp [pairExponent]
  rw [gamma,polynomial_radial_factor]
  ring

/-- One radial material is shared exactly; powers and weights remain in the original rational coefficient. -/
theorem term_radial_factor (first second : Term) :
    termOverlap first second = (pairCoefficient first second : ℝ) *
      radialKernel (pairExponent first second) (pairPenalty first second) := by
  have penalty : (pairPenalty first second : ℝ) =
      ∑ a : Fin 3, productPenalty first.exponent second.exponent (first.centre a) (second.centre a) := by
    simp [pairPenalty,productPenalty,pairExponent]
  simp only [termOverlap,axis_radial_factor,pairCoefficient,radialKernel,Rat.cast_mul,Rat.cast_prod]
  rw [penalty]
  simp only [Fin.prod_univ_three,Fin.sum_univ_three]
  rw [neg_add,neg_add,Real.exp_add,Real.exp_add]
  ring

end LAlanine40K2025.UnifiedOrbitals
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
