import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Radial

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals
open BasinRefinement SourceGaussianModel Polynomial
open scoped BigOperators

def productCoefficient (left right : ℚ) (p q n : ℕ) : ℚ :=
  ∑ i ∈ Finset.range (n+1),
    (left^(p-i) * (p.choose i : ℚ)) * (right^(q-(n-i)) * (q.choose (n-i) : ℚ))

theorem rational_product_coeff (alpha beta a b : ℚ) (p q n : ℕ) :
    (rationalProductPolynomial alpha beta a b p q).coeff n =
      productCoefficient (rationalProductCentre alpha beta a b-a)
        (rationalProductCentre alpha beta a b-b) p q n := by
  simp only [rationalProductPolynomial,Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,Polynomial.coeff_X_add_C_pow,
    productCoefficient]

theorem rational_product_degree (alpha beta a b : ℚ) (p q : ℕ) :
    (rationalProductPolynomial alpha beta a b p q).natDegree = p+q := by
  unfold rationalProductPolynomial
  rw [Polynomial.natDegree_mul
    (pow_ne_zero _ (Polynomial.monic_X_add_C _).ne_zero)
    (pow_ne_zero _ (Polynomial.monic_X_add_C _).ne_zero),
    Polynomial.natDegree_pow_X_add_C,Polynomial.natDegree_pow_X_add_C]

def axisCoefficient (alpha beta a b : ℚ) (p q : ℕ) : ℚ :=
  ∑ n ∈ Finset.range (p+q+1),
    productCoefficient (rationalProductCentre alpha beta a b-a)
      (rationalProductCentre alpha beta a b-b) p q n * rationalMoment (alpha+beta) n

theorem axis_coefficient_evaluated (alpha beta a b : ℚ) (p q : ℕ) :
    rationalPolynomialMoment (alpha+beta) (rationalProductPolynomial alpha beta a b p q) =
      axisCoefficient alpha beta a b p q := by
  simp only [rationalPolynomialMoment,rational_product_degree,rational_product_coeff,axisCoefficient]

def primitiveCoefficient (first second : Term) : ℚ :=
  first.weight * second.weight * ∏ a : Fin 3,
    axisCoefficient first.exponent second.exponent (first.centre a) (second.centre a)
      (first.powers a) (second.powers a)

theorem primitive_coefficient_evaluated (first second : Term) :
    pairCoefficient first second = primitiveCoefficient first second := by
  simp only [pairCoefficient,pairExponent,axis_coefficient_evaluated,primitiveCoefficient]

theorem term_computed_radial (first second : Term) :
    termOverlap first second = (primitiveCoefficient first second : ℝ) *
      radialKernel (pairExponent first second) (pairPenalty first second) := by
  rw [term_radial_factor,primitive_coefficient_evaluated]

end LAlanine40K2025.UnifiedOrbitals
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
