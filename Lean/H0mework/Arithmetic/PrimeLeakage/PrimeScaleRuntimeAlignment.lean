import H0mework.Arithmetic.PrimeLeakage.BlockIntegralRawEffect
import H0mework.Arithmetic.RiemannGraph.IntegralGraphCharacterReadback
import H0mework.Arithmetic.RiemannRuntime.PairedOmegaJointRelationOccurrence

/-!
# Prime-scale alignment with the installed joint runtime

Every actual factor row supplies a rational prime `p`.  The q-rich runtime
stage `p² - 3` has successor scale `p²`, hence its source action uses the
same positive scale unit `p` as the integral block read.  The raw block
endpoint effect therefore becomes the literal integral face of the existing
runtime `.sourceBoundary` row.

The two character measurements of that one integral event recover the
selected and reversal finite Euler differences.  No quotient survival,
vanishing, pole identification, fixedness, or RH premise enters.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace AllPlace
namespace ActionCofiber
namespace RawEffect
namespace PrimeScaleRuntime

open CanonicalUnitArithmeticCoordinateProjectionObstruction
open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationWholeHistorySolutionCarrier
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockDeterminantSection
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockWholeRelationDeterminant
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockAnalyticEndpointBoundaryEigenAction
open Character
open Character.GlobalCoPoissonCurrent
open Character.IntegralCharacterGroupRing
open ClozelGeneralizedDual.CenteredGram
open ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
open ClozelGeneralizedDual.ThetaJRoleRepresentation
open SourceGeneratedIntegralCharacterGroupRing
open SourceGeneratedIntegralCoherentJointAction
open SourceGeneratedPositiveRealCharacter

noncomputable section

/-- Runtime stage whose actual square-root scale is the prime itself. -/
def primeRuntimeStage (prime : Nat.Primes) : Nat :=
  (prime : Nat) ^ 2 - 3

theorem primeRuntimeStage_add_three (prime : Nat.Primes) :
    primeRuntimeStage prime + 3 = (prime : Nat) ^ 2 := by
  unfold primeRuntimeStage
  have three_le : 3 ≤ (prime : Nat) ^ 2 := by
    nlinarith [prime.property.two_le]
  exact Nat.sub_add_cancel three_le

theorem primeRuntimeStage_qRichScale (prime : Nat.Primes) :
    QRich.blockQRichSuccessorScale (primeRuntimeStage prime) =
      (prime : Nat) ^ 2 := by
  rw [QRich.blockQRichSuccessorScale_eq_stage_add_three,
    primeRuntimeStage_add_three]

theorem primeRuntimeStage_scaleUnit (prime : Nat.Primes) :
    stageSqrtScaleUnit (primeRuntimeStage prime) =
      blockPrimeScaleUnit prime := by
  apply Units.ext
  apply NNReal.eq
  rw [stageSqrtScaleUnit, blockPrimeScaleUnit,
    positiveRealUnit_val, positiveRealUnit_val]
  rw [primeRuntimeStage_qRichScale]
  push_cast
  rw [Real.sqrt_sq_eq_abs]
  exact abs_of_pos (by exact_mod_cast prime.property.pos)

/-- The complete raw block endpoint update is the integral face of the
already installed runtime source-boundary role at the prime scale. -/
theorem blockEndpointRawEffect_runtimeSourceBoundary_integral
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) (row : FactorRow seedOccurrence.root stage) :
    blockRelationIntegralCoordinate stage row
        (blockWholeRelationEulerOperator seedOccurrence.root stage
          (localBlockEndpointBoundaryRelation stage)) =
      runtimeJointIntegralFace
        (runtimeJointRelationGeneratorValue observation nontrivial
          (primeRuntimeStage (rowPrime row), .sourceBoundary)) := by
  rw [blockRelationIntegralCoordinate_operator_endpoint]
  change delta (1 : Units NNReal) -
      delta (blockPrimeScaleUnit (rowPrime row)) =
    (runtimeJointInputAt observation nontrivial
      (primeRuntimeStage (rowPrime row))).integralFace
      ((runtimeJointInputAt observation nontrivial
        (primeRuntimeStage (rowPrime row))).sourceBoundary
        (delta (1 : Units NNReal)))
  rw [Input.sourceBoundary_integralFace]
  change delta (1 : Units NNReal) -
      delta (blockPrimeScaleUnit (rowPrime row)) =
    delta (1 : Units NNReal) -
      leftTranslation (stageSqrtScaleUnit
        (primeRuntimeStage (rowPrime row))) (delta (1 : Units NNReal))
  rw [primeRuntimeStage_scaleUnit, leftTranslation_delta, mul_one]

theorem blockEndpointRawEffect_selected_character
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) (row : FactorRow seedOccurrence.root stage) :
    selectedGraphCharacterEvaluation observation nontrivial
        (blockRelationIntegralCoordinate stage row
          (blockWholeRelationEulerOperator seedOccurrence.root stage
            (localBlockEndpointBoundaryRelation stage))) =
      1 - installedPrimeEigenvalue (rowPrime row)
        observation.coordinate := by
  rw [blockRelationIntegralCoordinate_operator_endpoint,
    map_sub, selectedGraphCharacterEvaluation_eq_integralOccurrence]
  unfold blockPrimeScaleUnit
  rw [selected_prime_basis_readback]
  simp [zeroOwnedIntegralCharacterOccurrence_root_selected,
    characterEvaluation_delta,
    zeroOwnedMultiplicativeCharacterOccurrence_root_selected]

theorem blockEndpointRawEffect_reversal_character
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) (row : FactorRow seedOccurrence.root stage) :
    reversalGraphCharacterEvaluation observation nontrivial
        (blockRelationIntegralCoordinate stage row
          (blockWholeRelationEulerOperator seedOccurrence.root stage
            (localBlockEndpointBoundaryRelation stage))) =
      1 - installedPrimeEigenvalue (rowPrime row)
        (coordinateReversal observation.coordinate) := by
  rw [blockRelationIntegralCoordinate_operator_endpoint,
    map_sub, reversalGraphCharacterEvaluation_eq_integralOccurrence]
  unfold blockPrimeScaleUnit
  rw [reversal_prime_basis_readback]
  simp [zeroOwnedIntegralCharacterOccurrence_root_reversal,
    characterEvaluation_delta,
    zeroOwnedMultiplicativeCharacterOccurrence_root_reversal]

end
end PrimeScaleRuntime
end RawEffect
end ActionCofiber
end AllPlace
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
