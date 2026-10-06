import H0mework.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Product
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Integrals

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals
open BasinRefinement GaussianPrimitive SourceGaussianModel SourceFiniteData ContinuousGradient GlobalSource
open MeasureTheory Polynomial
open scoped BigOperators
noncomputable section

theorem factor_zero (alpha : ℚ) (power : ℕ) (x : ℝ) :
    factor alpha power 0 x = x^power * Real.exp (-(alpha : ℝ)*x^2) := by
  simp [SourceGaussianModel.factor,SourceGaussianModel.jetPoly,GaussianPrimitive.gaussian]

def axisOverlap (first second : Term) (a : Fin 3) : ℝ :=
  Real.exp (-productPenalty first.exponent second.exponent (first.centre a) (second.centre a)) *
    polynomialMoment (first.exponent+second.exponent)
      (productPolynomial first.exponent second.exponent (first.centre a) (second.centre a)
        (first.powers a) (second.powers a))

def termOverlap (first second : Term) : ℝ :=
  (first.weight : ℝ) * second.weight * ∏ a : Fin 3, axisOverlap first second a

theorem term_product_form (first second : Term) (x : Point) :
    value first zeroJet x * value second zeroJet x =
      (first.weight : ℝ) * second.weight * ∏ a : Fin 3,
        shiftedGaussian first.exponent (first.centre a) (first.powers a) (x a) *
          shiftedGaussian second.exponent (second.centre a) (second.powers a) (x a) := by
  simp only [value,zeroJet,factor_zero,Fin.prod_univ_three,shiftedGaussian]
  ring

theorem term_overlap_evaluated (first second : Term)
    (positive : 0 < first.exponent+second.exponent) :
    (∫ x : Point, value first zeroJet x * value second zeroJet x) = termOverlap first second := by
  have realPositive : (0 : ℝ) < (first.exponent : ℝ)+second.exponent := by exact_mod_cast positive
  simp_rw [term_product_form]
  rw [integral_const_mul]
  have split : (∫ x : Point, ∏ a : Fin 3,
      shiftedGaussian first.exponent (first.centre a) (first.powers a) (x a) *
        shiftedGaussian second.exponent (second.centre a) (second.powers a) (x a)) =
      ∏ a : Fin 3, ∫ x : ℝ, shiftedGaussian first.exponent (first.centre a) (first.powers a) x *
        shiftedGaussian second.exponent (second.centre a) (second.powers a) x := by
    simpa only using! integral_fin_nat_prod_volume_eq_prod (fun a : Fin 3 => fun x : ℝ =>
      shiftedGaussian first.exponent (first.centre a) (first.powers a) x *
        shiftedGaussian second.exponent (second.centre a) (second.powers a) x)
  rw [split]
  unfold termOverlap
  congr 1
  apply Finset.prod_congr rfl
  intro a _
  exact product_integral_evaluated first.exponent second.exponent (first.centre a) (second.centre a)
    realPositive (first.powers a) (second.powers a)

end
end LAlanine40K2025.UnifiedOrbitals
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
