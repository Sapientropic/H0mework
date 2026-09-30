import H0mework.Versions.Y.Arithmetic.PrimeLeakage.ZeroOwnedAllPrimeWeilQuadraticOccurrence
import H0mework.Versions.Y.Arithmetic.PrimeLeakage.PrimePowerRuntimeAlignment

/-!
# Source reads of one actual prime-power boundary

One arithmetic `(p,k>0)` receipt selects the existing paired-runtime
`.sourceBoundary` at scale `p^k`.  Its integral current, two character reads,
Euler-log weight, and positive quadratic coordinate are all read before any
residual or vanishing classification.
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
namespace WeilQuadratic
namespace PrimePower
namespace Source

open ActionCofiber.RawEffect.AllPrimeLeakage
open CanonicalUnitArithmeticCoordinateProjectionObstruction
open Character
open Character.GlobalCoPoissonCurrent
open Character.IntegralCharacterGroupRing
open ClozelGeneralizedDual
open ClozelGeneralizedDual.CenteredGram
open ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
open ClozelGeneralizedDual.ThetaJRoleRepresentation
open NoIslandNoMagic.CanonicalArithmeticState.AllPlaceEulerLog
open Occurrence
open RootGeneratedCanonicalUnitArithmeticPrimePowerCofinalClosure
open EulerDiagonal
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.AllPlace.WeilQuadratic.PrimePower.Runtime
open SourceGeneratedIntegralCharacterGroupRing
open SourceGeneratedPositiveRealCharacter
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.AllPlace.WeilQuadratic.Source

noncomputable section

def primePowerBoundaryState
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (prime : Nat.Primes) (exponent : Nat) :
    PairedOmegaJointRelationCarrier :=
  runtimeJointRelationGeneratorValue observation nontrivial
    (primePowerRuntimeStage prime exponent, .sourceBoundary)

def primePowerBoundaryIntegralRead
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (prime : Nat.Primes) (exponent : Nat) : IntegralScaleCarrier :=
  runtimeJointIntegralFace
    (primePowerBoundaryState observation nontrivial prime exponent)

def primePowerBoundaryCoherentRead
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (prime : Nat.Primes) (exponent : Nat) :
    JointGraphTarget × JointGraphTarget :=
  runtimeJointCoherentFace
    (primePowerBoundaryState observation nontrivial prime exponent)

def primePowerBoundaryStateFromSource
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    (source : ZeroOwnedAllPrimeWeilQuadraticPayload observation nontrivial)
    (prime : Nat.Primes) (exponent : Nat) :
    PairedOmegaJointRelationCarrier :=
  let input := pairedJointInputFromSource source.1
    (stageSqrtScaleUnit (primePowerRuntimeStage prime exponent))
  runtimeJointStateInclusion ((input.sourceBoundary (delta 1)).1)

def primePowerBoundaryIntegralReadFromSource
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    (source : ZeroOwnedAllPrimeWeilQuadraticPayload observation nontrivial)
    (prime : Nat.Primes) (exponent : Nat) : IntegralScaleCarrier :=
  runtimeJointIntegralFace
    (primePowerBoundaryStateFromSource source prime exponent)

def primePowerBoundaryCoherentReadFromSource
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    (source : ZeroOwnedAllPrimeWeilQuadraticPayload observation nontrivial)
    (prime : Nat.Primes) (exponent : Nat) :
    JointGraphTarget × JointGraphTarget :=
  runtimeJointCoherentFace
    (primePowerBoundaryStateFromSource source prime exponent)

theorem primePowerBoundaryStateFromSource_root_eq
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (prime : Nat.Primes) (exponent : Nat) :
    primePowerBoundaryStateFromSource
        (zeroOwnedAllPrimeWeilQuadraticOccurrence
          observation nontrivial).root prime exponent =
      primePowerBoundaryState observation nontrivial prime exponent := by
  rfl

theorem primePowerBoundaryIntegralReadFromSource_root_eq
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (prime : Nat.Primes) (exponent : Nat) :
    primePowerBoundaryIntegralReadFromSource
        (zeroOwnedAllPrimeWeilQuadraticOccurrence
          observation nontrivial).root prime exponent =
      primePowerBoundaryIntegralRead
        observation nontrivial prime exponent := by
  unfold primePowerBoundaryIntegralReadFromSource
    primePowerBoundaryIntegralRead
  rw [primePowerBoundaryStateFromSource_root_eq]

theorem primePowerBoundaryIntegralRead_eq
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (prime : Nat.Primes) (exponent : Nat) (positive : 0 < exponent) :
    primePowerBoundaryIntegralRead observation nontrivial prime exponent =
      delta 1 - delta (primePowerUnit prime exponent) := by
  unfold primePowerBoundaryIntegralRead primePowerBoundaryState
    runtimeJointRelationGeneratorValue runtimeJointIntegralFace
    runtimeJointStateInclusion runtimeJointSourceBoundaryAmbientAt
    runtimeJointInputAt
  exact primePowerSourceBoundary_integralFace
    observation nontrivial prime exponent positive

def primePowerSelectedCharacterReadFromSource
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    (source : ZeroOwnedAllPrimeWeilQuadraticPayload observation nontrivial)
    (prime : Nat.Primes) (exponent : Nat) : ℂ :=
  selectedGraphCharacterEvaluationFromSource source.1
    (primePowerBoundaryIntegralReadFromSource source prime exponent)

def primePowerReversalCharacterReadFromSource
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    (source : ZeroOwnedAllPrimeWeilQuadraticPayload observation nontrivial)
    (prime : Nat.Primes) (exponent : Nat) : ℂ :=
  reversalGraphCharacterEvaluationFromSource source.1
    (primePowerBoundaryIntegralReadFromSource source prime exponent)

theorem primePowerSelectedCharacterReadFromSource_root_eq
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (prime : Nat.Primes) (exponent : Nat) (positive : 0 < exponent) :
    primePowerSelectedCharacterReadFromSource
        (zeroOwnedAllPrimeWeilQuadraticOccurrence
          observation nontrivial).root prime exponent =
      1 - complexPowerCharacter observation.coordinate
        (primePowerUnit prime exponent) := by
  unfold primePowerSelectedCharacterReadFromSource
  change selectedGraphCharacterEvaluationFromSource
      (zeroOwnedJointStateModuleOccurrence observation nontrivial).root
        (primePowerBoundaryIntegralReadFromSource
          (zeroOwnedAllPrimeWeilQuadraticOccurrence
            observation nontrivial).root prime exponent) = _
  rw [selectedGraphCharacterEvaluationFromSource_root_eq,
    primePowerBoundaryIntegralReadFromSource_root_eq,
    primePowerBoundaryIntegralRead_eq observation nontrivial
      prime exponent positive,
    map_sub, selectedGraphCharacterEvaluation_eq_integralOccurrence,
    zeroOwnedIntegralCharacterOccurrence_root_selected,
    characterEvaluation_delta, characterEvaluation_delta,
    zeroOwnedMultiplicativeCharacterOccurrence_root_selected]
  simp

theorem primePowerReversalCharacterReadFromSource_root_eq
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (prime : Nat.Primes) (exponent : Nat) (positive : 0 < exponent) :
    primePowerReversalCharacterReadFromSource
        (zeroOwnedAllPrimeWeilQuadraticOccurrence
          observation nontrivial).root prime exponent =
      1 - complexPowerCharacter (coordinateReversal observation.coordinate)
        (primePowerUnit prime exponent) := by
  unfold primePowerReversalCharacterReadFromSource
  change reversalGraphCharacterEvaluationFromSource
      (zeroOwnedJointStateModuleOccurrence observation nontrivial).root
        (primePowerBoundaryIntegralReadFromSource
          (zeroOwnedAllPrimeWeilQuadraticOccurrence
            observation nontrivial).root prime exponent) = _
  rw [reversalGraphCharacterEvaluationFromSource_root_eq,
    primePowerBoundaryIntegralReadFromSource_root_eq,
    primePowerBoundaryIntegralRead_eq observation nontrivial
      prime exponent positive,
    map_sub, reversalGraphCharacterEvaluation_eq_integralOccurrence,
    zeroOwnedIntegralCharacterOccurrence_root_reversal,
    characterEvaluation_delta, characterEvaluation_delta,
    zeroOwnedMultiplicativeCharacterOccurrence_root_reversal]
  simp

theorem primePowerSelectedCharacterReadFromSource_root_cpow
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (prime : Nat.Primes) (exponent : Nat) (positive : 0 < exponent) :
    primePowerSelectedCharacterReadFromSource
        (zeroOwnedAllPrimeWeilQuadraticOccurrence
          observation nontrivial).root prime exponent =
      1 - ((thetaDistributionPrimePower prime exponent : Nat) : ℂ) ^
        (-observation.coordinate) := by
  rw [primePowerSelectedCharacterReadFromSource_root_eq
    observation nontrivial prime exponent positive]
  unfold primePowerUnit
  rw [complexPowerCharacter_apply]
  norm_cast

theorem primePowerReversalCharacterReadFromSource_root_cpow
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (prime : Nat.Primes) (exponent : Nat) (positive : 0 < exponent) :
    primePowerReversalCharacterReadFromSource
        (zeroOwnedAllPrimeWeilQuadraticOccurrence
          observation nontrivial).root prime exponent =
      1 - ((thetaDistributionPrimePower prime exponent : Nat) : ℂ) ^
        (-(coordinateReversal observation.coordinate)) := by
  rw [primePowerReversalCharacterReadFromSource_root_eq
    observation nontrivial prime exponent positive]
  unfold primePowerUnit
  rw [complexPowerCharacter_apply]
  norm_cast

end
end Source
end PrimePower
end WeilQuadratic
end AllPlace
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
