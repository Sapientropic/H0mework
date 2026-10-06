import H0mework.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Product

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals
open Polynomial
open scoped BigOperators

def rationalMoment (gamma : ℚ) : ℕ → ℚ
  | 0 => 1
  | 1 => 0
  | n+2 => (n+1 : ℚ)/(2*gamma) * rationalMoment gamma n

theorem moment_radial_factor (gamma : ℚ) (n : ℕ) :
    momentValue gamma n = (rationalMoment gamma n : ℝ) * Real.sqrt (Real.pi/gamma) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [momentValue,rationalMoment]
  | one => simp [momentValue,rationalMoment]
  | more n hn _ =>
      simp only [momentValue,rationalMoment,hn,Rat.cast_mul,Rat.cast_div,Rat.cast_add,
        Rat.cast_natCast,Rat.cast_one,Rat.cast_ofNat]
      ring

def rationalPolynomialMoment (gamma : ℚ) (p : Polynomial ℚ) : ℚ :=
  ∑ n ∈ Finset.range (p.natDegree+1), p.coeff n * rationalMoment gamma n

theorem polynomial_radial_factor (gamma : ℚ) (p : Polynomial ℚ) :
    polynomialMoment gamma (p.map (Rat.castHom ℝ)) =
      (rationalPolynomialMoment gamma p : ℝ) * Real.sqrt (Real.pi/gamma) := by
  unfold polynomialMoment rationalPolynomialMoment
  rw [Polynomial.natDegree_map]
  simp only [Polynomial.coeff_map,Rat.coe_castHom,moment_radial_factor,
    Rat.cast_sum,Rat.cast_mul,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n _
  ring

def rationalProductCentre (alpha beta a b : ℚ) : ℚ := (alpha*a+beta*b)/(alpha+beta)

noncomputable def rationalProductPolynomial (alpha beta a b : ℚ) (p q : ℕ) : Polynomial ℚ :=
  (X+C (rationalProductCentre alpha beta a b-a))^p *
    (X+C (rationalProductCentre alpha beta a b-b))^q

theorem product_polynomial_rational (alpha beta a b : ℚ) (p q : ℕ) :
    productPolynomial alpha beta a b p q =
      (rationalProductPolynomial alpha beta a b p q).map (Rat.castHom ℝ) := by
  simp [productPolynomial,rationalProductPolynomial,productCentre,rationalProductCentre]

end LAlanine40K2025.UnifiedOrbitals
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
