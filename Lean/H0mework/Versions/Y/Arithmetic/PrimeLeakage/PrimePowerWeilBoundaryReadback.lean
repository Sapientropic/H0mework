import H0mework.Versions.Y.Arithmetic.PrimeLeakage.ZeroOwnedPrimePowerWeilBoundaryOccurrence
import H0mework.Versions.Y.Arithmetic.SonineSource.PairedOmegaJointRelationDisposition

/-!
# Prime-power Weil boundary readback

The generated boundary occurrence reads back to the installed runtime state,
the exact prime-power characters and Euler weight, and the root-owned history,
whole-ledger, and next-current contract.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace AllPlace
namespace WeilQuadratic
namespace PrimePower
namespace Occurrence

open ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.AllPlace.WeilQuadratic.Occurrence
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.AllPlace.WeilQuadratic.PrimePower.Quadratic
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.AllPlace.WeilQuadratic.PrimePower.Runtime
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.AllPlace.WeilQuadratic.PrimePower.Source

noncomputable section

theorem zeroOwnedPrimePowerWeilBoundaryOccurrence_root_boundaryState
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (prime : Nat.Primes) (exponent : Nat) (positive : 0 < exponent) :
    (zeroOwnedPrimePowerWeilBoundaryOccurrence observation nontrivial
      prime exponent positive).root.2.boundaryState =
        primePowerBoundaryState observation nontrivial prime exponent := by
  change primePowerBoundaryStateFromSource
      (zeroOwnedAllPrimeWeilQuadraticOccurrence
        observation nontrivial).root prime exponent = _
  exact primePowerBoundaryStateFromSource_root_eq
    observation nontrivial prime exponent

theorem zeroOwnedPrimePowerWeilBoundaryOccurrence_root_coherentRead
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (prime : Nat.Primes) (exponent : Nat) (positive : 0 < exponent) :
    (zeroOwnedPrimePowerWeilBoundaryOccurrence observation nontrivial
      prime exponent positive).root.2.coherentRead =
        primePowerBoundaryCoherentRead
          observation nontrivial prime exponent := by
  change primePowerBoundaryCoherentReadFromSource
      (zeroOwnedAllPrimeWeilQuadraticOccurrence
        observation nontrivial).root prime exponent = _
  unfold primePowerBoundaryCoherentReadFromSource
    primePowerBoundaryCoherentRead
  rw [primePowerBoundaryStateFromSource_root_eq]

theorem zeroOwnedPrimePowerWeilBoundaryOccurrence_root_integralRead
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (prime : Nat.Primes) (exponent : Nat) (positive : 0 < exponent) :
    (zeroOwnedPrimePowerWeilBoundaryOccurrence observation nontrivial
      prime exponent positive).root.2.integralRead =
        SourceGeneratedIntegralCharacterGroupRing.delta 1 -
        SourceGeneratedIntegralCharacterGroupRing.delta
            (ClozelGeneralizedDual.ThetaJRoleRepresentation.primePowerUnit
              prime exponent) := by
  change primePowerBoundaryIntegralReadFromSource
      (zeroOwnedAllPrimeWeilQuadraticOccurrence
        observation nontrivial).root prime exponent = _
  rw [primePowerBoundaryIntegralReadFromSource_root_eq]
  exact primePowerBoundaryIntegralRead_eq
    observation nontrivial prime exponent positive

theorem zeroOwnedPrimePowerWeilBoundaryOccurrence_root_characterReads
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (prime : Nat.Primes) (exponent : Nat) (positive : 0 < exponent) :
    (zeroOwnedPrimePowerWeilBoundaryOccurrence observation nontrivial
        prime exponent positive).root.2.selectedRead =
        1 - ((ClozelGeneralizedDual.thetaDistributionPrimePower
          prime exponent : Nat) : ℂ) ^ (-observation.coordinate) ∧
      (zeroOwnedPrimePowerWeilBoundaryOccurrence observation nontrivial
        prime exponent positive).root.2.reversalRead =
        1 - ((ClozelGeneralizedDual.thetaDistributionPrimePower
          prime exponent : Nat) : ℂ) ^
            (-(CanonicalUnitArithmeticCoordinateProjectionObstruction.coordinateReversal
              observation.coordinate)) := by
  constructor
  · change primePowerSelectedCharacterReadFromSource
      (zeroOwnedAllPrimeWeilQuadraticOccurrence
        observation nontrivial).root prime exponent = _
    exact primePowerSelectedCharacterReadFromSource_root_cpow
      observation nontrivial prime exponent positive
  · change primePowerReversalCharacterReadFromSource
      (zeroOwnedAllPrimeWeilQuadraticOccurrence
        observation nontrivial).root prime exponent = _
    exact primePowerReversalCharacterReadFromSource_root_cpow
      observation nontrivial prime exponent positive

theorem zeroOwnedPrimePowerWeilBoundaryOccurrence_root_eulerWeight
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (prime : Nat.Primes) (exponent : Nat) (positive : 0 < exponent) :
    (zeroOwnedPrimePowerWeilBoundaryOccurrence observation nontrivial
      prime exponent positive).root.2.eulerWeight =
        Real.log ((prime : Nat) : ℝ) := by
  change primePowerEulerWeightFromSource
    (zeroOwnedAllPrimeWeilQuadraticOccurrence
      observation nontrivial).root prime exponent = _
  exact primePowerEulerWeightFromSource_root_eq
    observation nontrivial prime exponent positive

theorem zeroOwnedPrimePowerWeilBoundaryOccurrence_root_quadratic_nonnegative
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (prime : Nat.Primes) (exponent : Nat) (positive : 0 < exponent) :
    0 ≤ (zeroOwnedPrimePowerWeilBoundaryOccurrence observation nontrivial
      prime exponent positive).root.2.quadraticCoordinate := by
  change 0 ≤ primePowerEulerWeightedQuadraticFromSource
    (zeroOwnedAllPrimeWeilQuadraticOccurrence
      observation nontrivial).root prime exponent
  exact primePowerEulerWeightedQuadraticFromSource_root_nonnegative
    observation nontrivial prime exponent positive

theorem zeroOwnedPrimePowerWeilBoundaryOccurrence_root_one
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (prime : Nat.Primes) :
    (zeroOwnedPrimePowerWeilBoundaryOccurrence observation nontrivial
      prime 1 Nat.zero_lt_one).root.2.quadraticCoordinate =
        EulerDiagonal.eulerWeightedPrimeLeakage observation prime := by
  change primePowerEulerWeightedQuadraticFromSource
    (zeroOwnedAllPrimeWeilQuadraticOccurrence
      observation nontrivial).root prime 1 = _
  exact primePowerEulerWeightedQuadraticFromSource_root_one
    observation nontrivial prime

theorem zeroOwnedPrimePowerWeilBoundaryOccurrence_root_ledger_next
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (prime : Nat.Primes) (exponent : Nat) (positive : 0 < exponent) :
    let stage := primePowerRuntimeStage prime exponent
    (zeroOwnedPrimePowerWeilBoundaryOccurrence observation nontrivial
        prime exponent positive).root.2.boundaryState =
          runtimeJointRelationGeneratorValue observation nontrivial
            (stage, .sourceBoundary) ∧
      (type_of% (primePowerRuntime_actualReceipt prime exponent positive)) ∧
        runtimeJointSourceBoundaryPresentedEvent stage ∈
            ((runtimeJointFaithfulStepAt observation nontrivial stage
              ).history.observation 0).trace ∧
          (type_of% (runtimeJointFaithfulStep_factorizes
            observation nontrivial stage)) := by
  dsimp only
  exact ⟨by
      rw [zeroOwnedPrimePowerWeilBoundaryOccurrence_root_boundaryState]
      rfl,
    primePowerRuntime_actualReceipt prime exponent positive,
    runtimeJointFaithfulObservation_sourceBoundary_mem
      observation nontrivial (primePowerRuntimeStage prime exponent) 0,
    runtimeJointFaithfulStep_factorizes observation nontrivial
      (primePowerRuntimeStage prime exponent)⟩

end
end Occurrence
end PrimePower
end WeilQuadratic
end AllPlace
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
