import H0mework.Arithmetic.Goldbach.EffectiveDisposition
import H0mework.Foundation.Finite.EffectiveCoefficient

/-!
# Source-generated effective additive coefficient

The exact prime indices of one canonical even-target occurrence generate a
`Nat`-valued prime polynomial.  Squaring that polynomial produces the exact
ordered prime-pair polynomial.  Its target coefficient is positive exactly
when the already authoritative effective additive fibre is inhabited, and is
zero exactly when that fibre is empty.

All coefficients live in `Nat`: there is no signed cancellation, arbitrary
linear combination, or caller-supplied positivity premise.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticEffectiveAdditiveCoefficientProducer

open ArithmeticGeneration
open CanonicalUnitArithmeticEffectiveAdditiveProducer
open SourceGeneratedEffectiveFibreDisposition
open SourceGeneratedFiniteEffectiveCoefficient

noncomputable section

/-- Cardinal coordinate of one actual factorization-generated prime
restriction. -/
def generatedPrimeCoordinate (index : Nat)
    (primeIndex : GeneratedPrimeIndexAt index) : Nat :=
  (generatedPrimeHistory primeIndex).cardinalShadow

/-- One monomial per actual generated prime index. -/
noncomputable def generatedPrimePolynomial (index : Nat) :
    Polynomial Nat :=
  countingPolynomial (generatedPrimeCoordinate index)

/-- Cardinal evaluation of an actual generated prime pair. -/
def additiveCoordinateEvaluation (index : Nat)
    (candidate : GeneratedPrimePairCandidateAt index) : Nat :=
  (additiveEvaluation index candidate).cardinalShadow

theorem additiveCoordinateEvaluation_eq_pairSum
    (index : Nat) (candidate : GeneratedPrimePairCandidateAt index) :
    additiveCoordinateEvaluation index candidate =
      generatedPrimeCoordinate index candidate.1 +
        generatedPrimeCoordinate index candidate.2 := by
  simp [additiveCoordinateEvaluation, additiveEvaluation,
    generatedPrimeCoordinate]

/-- Exact ordered-pair representation polynomial. -/
noncomputable def generatedAdditivePolynomial (index : Nat) :
    Polynomial Nat :=
  countingPolynomial (additiveCoordinateEvaluation index)

theorem generatedAdditivePolynomial_eq_primePolynomial_square
    (index : Nat) :
    generatedAdditivePolynomial index =
      generatedPrimePolynomial index * generatedPrimePolynomial index := by
  rw [generatedAdditivePolynomial, generatedPrimePolynomial]
  have evaluation_eq : additiveCoordinateEvaluation index =
      fun pair : GeneratedPrimeIndexAt index ×
          GeneratedPrimeIndexAt index ↦
        generatedPrimeCoordinate index pair.1 +
          generatedPrimeCoordinate index pair.2 := by
    funext candidate
    exact additiveCoordinateEvaluation_eq_pairSum index candidate
  rw [evaluation_eq]
  exact pairCountingPolynomial_eq_square (generatedPrimeCoordinate index)

def generatedTargetCoordinate (index : Nat) : Nat :=
  (evenTargetHistory index).cardinalShadow

/-- The exact nonnegative Goldbach representation coefficient at this
occurrence. -/
noncomputable def generatedAdditiveCoefficient (index : Nat) : Nat :=
  effectiveCoefficient (additiveCoordinateEvaluation index)
    (generatedTargetCoordinate index)

theorem generatedAdditiveCoefficient_eq_card_filter (index : Nat) :
    generatedAdditiveCoefficient index =
      (Finset.univ.filter fun candidate :
          GeneratedPrimePairCandidateAt index ↦
        additiveCoordinateEvaluation index candidate =
          generatedTargetCoordinate index).card :=
  effectiveCoefficient_eq_card_filter
    (additiveCoordinateEvaluation index) (generatedTargetCoordinate index)

abbrev CoordinateAdditiveFibreAt (index : Nat) : Type :=
  Fibre (additiveCoordinateEvaluation index)
    (generatedTargetCoordinate index)

def coordinateFibreOfEffective {index : Nat}
    (fibre : EffectiveAdditiveFibreAt index) :
    CoordinateAdditiveFibreAt index := by
  refine ⟨fibre.1, ?_⟩
  have landing := congrArg UnitHistory.cardinalShadow fibre.2
  exact landing

def effectiveFibreOfCoordinate {index : Nat}
    (fibre : CoordinateAdditiveFibreAt index) :
    EffectiveAdditiveFibreAt index := by
  refine ⟨fibre.1, ?_⟩
  apply UnitHistory.eq_of_cardinalShadow_eq
  exact fibre.2

def coordinateEffectiveFibreEquiv (index : Nat) :
    CoordinateAdditiveFibreAt index ≃ EffectiveAdditiveFibreAt index where
  toFun := effectiveFibreOfCoordinate
  invFun := coordinateFibreOfEffective
  left_inv fibre := by
    apply Subtype.ext
    rfl
  right_inv fibre := by
    apply Subtype.ext
    rfl

theorem generatedAdditiveCoefficient_eq_card_effectiveFibre
    (index : Nat) :
    generatedAdditiveCoefficient index =
      Fintype.card (EffectiveAdditiveFibreAt index) := by
  rw [generatedAdditiveCoefficient]
  calc
    effectiveCoefficient (additiveCoordinateEvaluation index)
          (generatedTargetCoordinate index) =
        Fintype.card (CoordinateAdditiveFibreAt index) :=
      effectiveCoefficient_eq_card_fibre _ _
    _ = Fintype.card (EffectiveAdditiveFibreAt index) :=
      Fintype.card_congr (coordinateEffectiveFibreEquiv index)

theorem generatedAdditiveCoefficient_pos_iff_effectiveFibre
    (index : Nat) :
    0 < generatedAdditiveCoefficient index ↔
      Nonempty (EffectiveAdditiveFibreAt index) := by
  constructor
  · intro coefficientPositive
    obtain ⟨coordinateFibre⟩ :=
      (effectiveCoefficient_pos_iff_fibre
        (additiveCoordinateEvaluation index)
        (generatedTargetCoordinate index)).1 coefficientPositive
    exact ⟨effectiveFibreOfCoordinate coordinateFibre⟩
  · rintro ⟨fibre⟩
    apply (effectiveCoefficient_pos_iff_fibre
      (additiveCoordinateEvaluation index)
      (generatedTargetCoordinate index)).2
    exact ⟨coordinateFibreOfEffective fibre⟩

theorem generatedAdditiveCoefficient_eq_zero_iff_effectiveFibre_empty
    (index : Nat) :
    generatedAdditiveCoefficient index = 0 ↔
      ¬ Nonempty (EffectiveAdditiveFibreAt index) := by
  constructor
  · intro coefficientZero fibre
    have coefficientPositive :=
      (generatedAdditiveCoefficient_pos_iff_effectiveFibre index).2 fibre
    omega
  · intro fibreEmpty
    by_contra coefficientNonzero
    have coefficientPositive : 0 < generatedAdditiveCoefficient index := by
      omega
    exact fibreEmpty
      ((generatedAdditiveCoefficient_pos_iff_effectiveFibre index).1
        coefficientPositive)

/-- Source-owned coefficient face.  Its occurrence, factorization, prime
polynomial, convolution square, and target coefficient are all generated;
the caller supplies no branch or coefficient law. -/
structure RootGeneratedAdditiveCoefficientAt (index : Nat) : Type where
  private mk ::
  occurrence : RootedAccountedUnfolding AdditiveCalculationPoint
  occurrence_eq : occurrence = evenTargetOccurrence index
  factorization : RootGeneratedEvenTargetFactorizationAt index
  factorization_eq : factorization = generatedEvenTargetFactorization index
  primePolynomial : Polynomial Nat
  primePolynomial_eq : primePolynomial = generatedPrimePolynomial index
  additivePolynomial : Polynomial Nat
  additivePolynomial_eq :
    additivePolynomial = generatedAdditivePolynomial index
  convolutionSquare :
    additivePolynomial = primePolynomial * primePolynomial
  target : Nat
  target_eq : target = generatedTargetCoordinate index
  coefficient : Nat
  coefficient_eq : coefficient = generatedAdditiveCoefficient index
  coefficientReadout : coefficient = additivePolynomial.coeff target
  positiveIffFibre :
    0 < coefficient ↔ Nonempty (EffectiveAdditiveFibreAt index)
  zeroIffFibreEmpty :
    coefficient = 0 ↔ ¬ Nonempty (EffectiveAdditiveFibreAt index)

noncomputable def generatedAdditiveCoefficientFace (index : Nat) :
    RootGeneratedAdditiveCoefficientAt index :=
  ⟨evenTargetOccurrence index, rfl,
    generatedEvenTargetFactorization index, rfl,
    generatedPrimePolynomial index, rfl,
    generatedAdditivePolynomial index, rfl,
    generatedAdditivePolynomial_eq_primePolynomial_square index,
    generatedTargetCoordinate index, rfl,
    generatedAdditiveCoefficient index, rfl, rfl,
    generatedAdditiveCoefficient_pos_iff_effectiveFibre index,
    generatedAdditiveCoefficient_eq_zero_iff_effectiveFibre_empty index⟩

end
end CanonicalUnitArithmeticEffectiveAdditiveCoefficientProducer
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
