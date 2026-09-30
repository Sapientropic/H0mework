import H0mework.Versions.Y.Arithmetic.PrimeShadow.LivingLawCanonicalUnitArithmeticFactorizationInverseFibre
import H0mework.Versions.X.Arithmetic.EulerGlobal.WholeHistory

/-!
# The existing whole-history equation consumes the factor inverse fibre

At the same actual stage, the old scalar relation identifies two prime-power
keys, while the existing whole-history solution map, evaluated at the
anti-invariant test base, has different quotient coordinates for those keys.
Thus the scalar projection cannot recover the factor-sensitive solution.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticFactorizationInverseFibreConsumer

open CanonicalUnitArithmeticFactorizationOccurrence
open CanonicalUnitArithmeticFactorizationInverseFibre
open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationWholeHistorySolutionCarrier

noncomputable section

def antiBase : DualBase := fun dualIndex => if dualIndex = 0 then 1 else 0

def rowOfKey
    (key : FactorKeyAt (factorizationOccurrence 1).root) :
    FactorRow seedOccurrence.root 1 := by
  exact key

def antiBaseSolution : Carrier seedOccurrence.root 1 :=
  solutionOfBase seedOccurrence.root 1 antiBase

theorem antiBaseSolution_quotient (key : FactorKeyAt (factorizationOccurrence 1).root) :
    quotientCoordinate (rowOfKey key) antiBaseSolution =
      quotientCoefficient (rowOfKey key) := by
  change (quotientCoefficient (rowOfKey key) : ℤ) *
      (antiBase 0 - antiBase 1) = _
  norm_num [antiBase]

theorem stageOne_wholeCoefficient :
    wholeCoefficient seedOccurrence.root 1 = 6 := by
  unfold wholeCoefficient
  rw [factorialHistory_cardinalShadow]
  have shadow : (StageHistory seedOccurrence.root 1).cardinalShadow = 3 := by
    rfl
  rw [shadow]
  norm_num

theorem keyTwo_quotientCoefficient :
    quotientCoefficient (rowOfKey keyTwo) = 3 := by
  have landing := wholeCoefficient_eq_primePower_mul_quotientCoefficient
    seedOccurrence.root 1 (rowOfKey keyTwo)
  rw [stageOne_wholeCoefficient] at landing
  have primeValue : (rowPrime (rowOfKey keyTwo) : Nat) = 2 := by rfl
  have exponentValue : rowExponent (rowOfKey keyTwo) = 1 := by rfl
  rw [primeValue, exponentValue] at landing
  omega

theorem keyThree_quotientCoefficient :
    quotientCoefficient (rowOfKey keyThree) = 2 := by
  have landing := wholeCoefficient_eq_primePower_mul_quotientCoefficient
    seedOccurrence.root 1 (rowOfKey keyThree)
  rw [stageOne_wholeCoefficient] at landing
  have primeValue : (rowPrime (rowOfKey keyThree) : Nat) = 3 := by rfl
  have exponentValue : rowExponent (rowOfKey keyThree) = 1 := by rfl
  rw [primeValue, exponentValue] at landing
  omega

theorem antiBaseSolution_distinguishes_collapsed_keys :
    oldRelationProjectionAt (factorizationOccurrence 1).root keyTwo =
        oldRelationProjectionAt (factorizationOccurrence 1).root keyThree ∧
      quotientCoordinate (rowOfKey keyTwo) antiBaseSolution = 3 ∧
      quotientCoordinate (rowOfKey keyThree) antiBaseSolution = 2 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [oldRelationProjectionAt_eq_whole,
      oldRelationProjectionAt_eq_whole]
  · rw [antiBaseSolution_quotient, keyTwo_quotientCoefficient]
    norm_num
  · rw [antiBaseSolution_quotient, keyThree_quotientCoefficient]
    norm_num

/-- No decoder of the scalar relation can recover both factor-sensitive
quotient coordinates of this source-derived test solution. -/
theorem no_scalar_decoder_for_antiBaseSolution :
    ¬ ∃ decode : CanonicalUnitArithmeticFactorizationEulerUnitNormalizedFiniteEnvelope.Lattice → ℤ,
      ∀ key : FactorKeyAt (factorizationOccurrence 1).root,
        decode (oldRelationProjectionAt (factorizationOccurrence 1).root key) =
          quotientCoordinate (rowOfKey key) antiBaseSolution := by
  rintro ⟨decode, recovers⟩
  have two := recovers keyTwo
  have three := recovers keyThree
  have collapsed := antiBaseSolution_distinguishes_collapsed_keys.1
  rw [collapsed] at two
  rw [antiBaseSolution_distinguishes_collapsed_keys.2.1] at two
  rw [antiBaseSolution_distinguishes_collapsed_keys.2.2] at three
  omega

end
end CanonicalUnitArithmeticFactorizationInverseFibreConsumer
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
