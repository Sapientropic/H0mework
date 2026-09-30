import H0mework.Versions.Y.Arithmetic.PrimeLeakage.PrimeScaleCofinalClosedEffect
import H0mework.Versions.Y.Arithmetic.EulerGlobal.HistoryCofinalRigidity

/-!
# Source-generated prime raw effect

Every rational prime generates its own actual exponent-one factor row; the
caller supplies neither a finite stage nor a row.  Its pre-quotient endpoint
update is the closed cofinal source-boundary event and its selected/reversal
characters are the two installed finite Euler differences.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace AllPlace
namespace ActionCofiber
namespace RawEffect
namespace AllPrimeCofinal

open CanonicalUnitArithmeticFactorizationOccurrence
open CanonicalUnitArithmeticCoordinateProjectionObstruction
open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationWholeHistorySolutionCarrier
open CanonicalUnitArithmeticFactorizationWholeHistorySolutionCofinalRigidity
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockWholeRelationDeterminant
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockDeterminantSection
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockAnalyticEndpointBoundaryEigenAction
open Character
open Character.GlobalCoPoissonCurrent
open ClozelGeneralizedDual.CenteredGram
open ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
open ClozelGeneralizedDual.ThetaJRoleRepresentation
open PrimeScaleRuntime
open PrimeScaleCofinal
open SourceGeneratedIntegralCharacterGroupRing
open SourceGeneratedPositiveRealCharacter

noncomputable section

def generatedPrimeFactor (prime : Nat.Primes) :
    RuntimePrimePowerFactorAt prime 1 :=
  RuntimePrimePowerFactorAt.generate prime 1 Nat.zero_lt_one

def generatedPrimeFactorRow (prime : Nat.Primes) :
    FactorRow seedOccurrence.root (generatedPrimeFactor prime).stage :=
  stageFactorRow (generatedPrimeFactor prime)

@[simp] theorem generatedPrimeFactorRow_prime (prime : Nat.Primes) :
    rowPrime (generatedPrimeFactorRow prime) = prime :=
  stageFactorRow_prime (generatedPrimeFactor prime)

def generatedPrimeRawEffect (prime : Nat.Primes) : IntegralScaleCarrier :=
  blockRelationIntegralCoordinate (generatedPrimeFactor prime).stage
    (generatedPrimeFactorRow prime)
      (blockWholeRelationEulerOperator seedOccurrence.root
        (generatedPrimeFactor prime).stage
        (localBlockEndpointBoundaryRelation
          (generatedPrimeFactor prime).stage))

theorem generatedPrimeRawEffect_runtime
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (prime : Nat.Primes) :
    generatedPrimeRawEffect prime =
      runtimeJointIntegralFace
        (runtimeJointRelationGeneratorValue observation nontrivial
          (primeRuntimeStage prime, .sourceBoundary)) := by
  unfold generatedPrimeRawEffect
  rw [blockEndpointRawEffect_runtimeSourceBoundary_integral]
  rw [generatedPrimeFactorRow_prime]

theorem generatedPrimeRawEffect_closed_in_initialCofinalHistory
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (prime : Nat.Primes) :
    generatedPrimeRawEffect prime =
        runtimeJointIntegralFace
          (runtimeJointRelationGeneratorValue observation nontrivial
            (primeRuntimeStage prime, .sourceBoundary)) ∧
      runtimeJointSourceBoundaryPresentedEvent (primeRuntimeStage prime) ∈
        ((runtimeJointFaithfulStepAt observation nontrivial 0).history.observation
          (primeRuntimeStage prime)).trace ∧
      runtimeJointSourceBoundaryPresentedEvent (primeRuntimeStage prime) ∉
        ((runtimeJointFaithfulStepAt observation nontrivial 0).history.observation
          (primeRuntimeStage prime)).frontier ∧
      (runtimeJointFaithfulStepAt observation nontrivial 0).faithful.freeEvaluation
          (runtimeJointSourceBoundaryStageRelation
            (primeRuntimeStage prime)) = 0 ∧
      (type_of% (runtimeJointFaithfulStep_factorizes observation nontrivial 0)) := by
  simpa only [generatedPrimeRawEffect, generatedPrimeFactorRow_prime] using
    blockPrimeRawEffect_closed_in_initialCofinalHistory
      observation nontrivial (generatedPrimeFactor prime).stage
        (generatedPrimeFactorRow prime)

theorem generatedPrimeRawEffect_selected_character
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (prime : Nat.Primes) :
    selectedGraphCharacterEvaluation observation nontrivial
        (generatedPrimeRawEffect prime) =
      1 - installedPrimeEigenvalue prime observation.coordinate := by
  unfold generatedPrimeRawEffect
  rw [blockEndpointRawEffect_selected_character,
    generatedPrimeFactorRow_prime]

theorem generatedPrimeRawEffect_reversal_character
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (prime : Nat.Primes) :
    reversalGraphCharacterEvaluation observation nontrivial
        (generatedPrimeRawEffect prime) =
      1 - installedPrimeEigenvalue prime
        (coordinateReversal observation.coordinate) := by
  unfold generatedPrimeRawEffect
  rw [blockEndpointRawEffect_reversal_character,
    generatedPrimeFactorRow_prime]

theorem blockPrimeScaleUnit_injective :
    Function.Injective blockPrimeScaleUnit := by
  intro left right equality
  apply Subtype.ext
  have value_eq := congrArg
    (fun scale : Units NNReal => (((scale : NNReal) : ℝ))) equality
  simpa [blockPrimeScaleUnit, positiveRealUnit_val] using value_eq

theorem blockPrimeScaleUnit_ne_one (prime : Nat.Primes) :
    blockPrimeScaleUnit prime ≠ 1 := by
  intro equality
  have value_eq := congrArg
    (fun scale : Units NNReal => (((scale : NNReal) : ℝ))) equality
  have prime_eq_one : (prime : Nat) = 1 := by
    exact_mod_cast (show (prime : ℝ) = 1 by
      simpa [blockPrimeScaleUnit, positiveRealUnit_val] using value_eq)
  exact prime.property.ne_one prime_eq_one

theorem generatedPrimeRawEffect_eq_delta_sub (prime : Nat.Primes) :
    generatedPrimeRawEffect prime =
      delta (1 : Units NNReal) - delta (blockPrimeScaleUnit prime) := by
  unfold generatedPrimeRawEffect
  rw [blockRelationIntegralCoordinate_operator_endpoint,
    generatedPrimeFactorRow_prime]

end
end AllPrimeCofinal
end RawEffect
end ActionCofiber
end AllPlace
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
