import H0mework.Chemistry.LAlanineRefinementDensity.GaussianBounds

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.GaussianCoefficients

open Polynomial Finset GaussianPrimitive SourceGaussianModel

def jetCoeff (alpha : ℚ) (power : ℕ) : ℕ → ℕ → ℚ
  | 0, k => if k = power then 1 else 0
  | order + 1, k => jetCoeff alpha power order (k+1) * (k+1) -
      2 * alpha * (if k = 0 then 0 else jetCoeff alpha power order (k-1))

theorem jetPoly_coeff (alpha : ℚ) (power order k : ℕ) :
    (jetPoly alpha power order).coeff k = jetCoeff alpha power order k := by
  induction order generalizing k with
  | zero => simp [jetPoly, jetCoeff, Polynomial.coeff_X_pow]
  | succ order ih =>
    simp only [jetPoly] at ih
    simp only [jetPoly, Function.iterate_succ_apply', jetPolynomial, Polynomial.coeff_sub,
      Polynomial.coeff_derivative, mul_assoc, Polynomial.coeff_C_mul]
    cases k with
    | zero => simpa [jetCoeff] using ih 1
    | succ k => simp [jetCoeff, ih, Polynomial.coeff_X_mul, mul_assoc]

theorem jetCoeff_above (alpha : ℚ) (power order k : ℕ) (above : power + order < k) :
    jetCoeff alpha power order k = 0 := by
  induction order generalizing k with
  | zero => simp [jetCoeff, show k ≠ power by omega]
  | succ order ih =>
    have next : power + order < k + 1 := by omega
    have previous : power + order < k - 1 := by omega
    simp [jetCoeff, ih (k+1) next, ih (k-1) previous]

theorem jetPoly_degree (alpha : ℚ) (power order : ℕ) :
    (jetPoly alpha power order).natDegree ≤ power + order := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k above
  rw [jetPoly_coeff]
  exact jetCoeff_above alpha power order k above

def jetEnvelope (alpha radius : ℚ) (power order : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (power + order + 1), |jetCoeff alpha power order k| * radius ^ k

theorem jetEnvelope_eq (alpha radius : ℚ) (power order : ℕ) :
    coefficientEnvelope (jetPoly alpha power order) radius = jetEnvelope alpha radius power order := by
  unfold coefficientEnvelope jetEnvelope
  simp_rw [jetPoly_coeff]
  apply Finset.sum_subset
  · exact Finset.range_mono (Nat.add_le_add_right (jetPoly_degree alpha power order) 1)
  · intro k _ absent
    have above : (jetPoly alpha power order).natDegree < k := by
      simpa only [Finset.mem_range, not_lt, Nat.add_one_le_iff] using absent
    have zero := Polynomial.coeff_eq_zero_of_natDegree_lt above
    rw [jetPoly_coeff] at zero
    simp [zero]

def factorBound (term : Term) (d : MultiIndex) (centre : RationalPoint) (radius : ℚ)
    (axis : Fin 3) : ℚ :=
  jetEnvelope term.exponent (relativeUpper term centre radius axis) (term.powers axis) (d axis) /
    (2 : ℚ) ^ decayLevel term centre radius axis

def termBound (term : Term) (d : MultiIndex) (centre : RationalPoint) (radius : ℚ) : ℚ :=
  |term.weight| * factorBound term d centre radius 0 * factorBound term d centre radius 1 *
    factorBound term d centre radius 2

def orbitalBound (terms : List Term) (d : MultiIndex) (centre : RationalPoint) (radius : ℚ) : ℚ :=
  (terms.map fun term => termBound term d centre radius).sum

theorem factorEnvelope_eq_bound (term : Term) (d : MultiIndex) (centre : RationalPoint) (radius : ℚ)
    (axis : Fin 3) : factorEnvelope term d centre radius axis = factorBound term d centre radius axis := by
  simp only [factorEnvelope, factorBound, jetEnvelope_eq]

theorem orbitalEnvelope_eq_bound (terms : List Term) (d : MultiIndex) (centre : RationalPoint) (radius : ℚ) :
    orbitalEnvelope terms d centre radius = orbitalBound terms d centre radius := by
  simp only [orbitalEnvelope, orbitalBound, termEnvelope, termBound, factorEnvelope_eq_bound]

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.GaussianCoefficients
