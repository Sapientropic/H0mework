import H0mework.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Evaluate
import Mathlib.MeasureTheory.Group.Integral

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals
open BasinRefinement GaussianPrimitive GlobalSource MeasureTheory Polynomial
noncomputable section

def productCentre (alpha beta a b : ℝ) : ℝ := (alpha*a+beta*b)/(alpha+beta)
def productPenalty (alpha beta a b : ℝ) : ℝ := alpha*beta/(alpha+beta)*(a-b)^2

theorem completed_square (alpha beta a b x : ℝ) (positive : 0 < alpha+beta) :
    alpha*(x-a)^2 + beta*(x-b)^2 =
      (alpha+beta)*(x-productCentre alpha beta a b)^2 + productPenalty alpha beta a b := by
  unfold productCentre productPenalty
  field_simp
  ring

def productPolynomial (alpha beta a b : ℝ) (p q : ℕ) : Polynomial ℝ :=
  (X+C (productCentre alpha beta a b-a))^p * (X+C (productCentre alpha beta a b-b))^q

def shiftedGaussian (alpha a : ℝ) (p : ℕ) (x : ℝ) : ℝ :=
  (x-a)^p * Real.exp (-alpha*(x-a)^2)

/-- The original two-centre product has one exact Gaussian centre and a finite polynomial. -/
theorem product_gaussian (alpha beta a b : ℝ) (positive : 0 < alpha+beta) (p q : ℕ) (x : ℝ) :
    shiftedGaussian alpha a p x * shiftedGaussian beta b q x =
      Real.exp (-productPenalty alpha beta a b) *
        GaussianPrimitive.gaussian (alpha+beta) (productPolynomial alpha beta a b p q)
          (x-productCentre alpha beta a b) := by
  have exponent : -alpha*(x-a)^2 + -beta*(x-b)^2 =
      -productPenalty alpha beta a b + -(alpha+beta)*(x-productCentre alpha beta a b)^2 := by
    linarith [completed_square alpha beta a b x positive]
  unfold shiftedGaussian GaussianPrimitive.gaussian productPolynomial
  simp only [eval_mul,eval_pow,eval_add,eval_X,eval_C]
  have left : x-productCentre alpha beta a b+(productCentre alpha beta a b-a) = x-a := by ring
  have right : x-productCentre alpha beta a b+(productCentre alpha beta a b-b) = x-b := by ring
  rw [left,right]
  rw [show (x-a)^p*Real.exp (-alpha*(x-a)^2)*((x-b)^q*Real.exp (-beta*(x-b)^2)) =
      ((x-a)^p*(x-b)^q)*(Real.exp (-alpha*(x-a)^2)*Real.exp (-beta*(x-b)^2)) by ring,
    ← Real.exp_add,exponent,Real.exp_add]
  ring

theorem product_integral_evaluated (alpha beta a b : ℝ) (positive : 0 < alpha+beta) (p q : ℕ) :
    (∫ x : ℝ, shiftedGaussian alpha a p x * shiftedGaussian beta b q x) =
      Real.exp (-productPenalty alpha beta a b) *
        polynomialMoment (alpha+beta) (productPolynomial alpha beta a b p q) := by
  simp_rw [product_gaussian alpha beta a b positive p q]
  rw [integral_const_mul,integral_sub_right_eq_self,gaussian_integral_evaluated _ positive]

end
end LAlanine40K2025.UnifiedOrbitals
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
