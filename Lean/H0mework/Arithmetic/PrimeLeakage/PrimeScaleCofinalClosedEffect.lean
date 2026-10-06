import H0mework.Arithmetic.PrimeLeakage.PrimeScaleRuntimeActivation

/-!
# Every prime-scale raw effect is closed in one cofinal history

The all-row runtime alignment is strengthened from one visit per prime to one
source-generated cofinal history at depth zero.  Every actual prime-row
`.sourceBoundary` is already in that history's trace and is not its open
frontier.  The frontier is the next balance occurrence; it is not the same
debt renamed for another turn.

Consequently the raw Euler effect is an accounted dependent relation write,
not a candidate for finite Noetherian debt activation on the reused canonical
base row.  The whole joint
relation evaluates to zero while its integral source-boundary coordinate is
retained, so quotient soundness does not erase the raw update.
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
namespace PrimeScaleCofinal

open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationWholeHistorySolutionCarrier
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockWholeRelationDeterminant
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockAnalyticEndpointBoundaryEigenAction
open ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
open PrimeScaleRuntime

noncomputable section

/-- Different rational primes occupy different stages of the cofinal joint
history. -/
theorem primeRuntimeStage_injective :
    Function.Injective primeRuntimeStage := by
  intro left right stage_eq
  apply Subtype.ext
  have square_eq : (left : Nat) ^ 2 = (right : Nat) ^ 2 := by
    calc
      (left : Nat) ^ 2 = primeRuntimeStage left + 3 :=
        (primeRuntimeStage_add_three left).symm
      _ = primeRuntimeStage right + 3 := by rw [stage_eq]
      _ = (right : Nat) ^ 2 := primeRuntimeStage_add_three right
  nlinarith [left.property.pos, right.property.pos]

/-- At every observation stage, source boundary is a completed dependent
write.  The sole live frontier is the balance row. -/
theorem runtimeJointSourceBoundary_not_frontier
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth stage : Nat) :
    runtimeJointSourceBoundaryPresentedEvent (depth + stage) ∉
      ((runtimeJointFaithfulStepAt observation nontrivial depth
        ).history.observation stage).frontier := by
  rw [runtimeJointFaithfulObservation_frontier]
  change runtimeJointSourceBoundaryPresentedEvent (depth + stage) ∉
    [runtimeJointBalancePresentedEvent (depth + stage)]
  simp only [List.mem_singleton]
  intro event_eq
  injection event_eq with relation_eq
  have coordinate_eq := congrArg
    (fun relation : RuntimeJointRelationGenerator →₀ ℤ =>
      relation (depth + stage, .sourceSeed)) relation_eq
  simp [runtimeJointSourceBoundaryStageRelation,
    runtimeJointBalanceStageRelation,
    runtimeJointRelationAtom] at coordinate_eq

/-- Every actual block row occurs in the trace of the one cofinal history
generated at depth zero. -/
theorem blockPrimeCofinalSourceBoundary_mem
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) (row : FactorRow seedOccurrence.root stage) :
    runtimeJointSourceBoundaryPresentedEvent
        (primeRuntimeStage (rowPrime row)) ∈
      ((runtimeJointFaithfulStepAt observation nontrivial 0).history.observation
        (primeRuntimeStage (rowPrime row))).trace := by
  simpa using runtimeJointFaithfulObservation_sourceBoundary_mem
    observation nontrivial 0 (primeRuntimeStage (rowPrime row))

/-- Complete same-occurrence contract: the raw block effect is the integral
coordinate of a sound, closed relation write in one cofinal history, with the
initial root occurrence, whole-ledger write-back and generated next retained.
-/
theorem blockPrimeRawEffect_closed_in_initialCofinalHistory
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) (row : FactorRow seedOccurrence.root stage) :
    blockRelationIntegralCoordinate stage row
        (blockWholeRelationEulerOperator seedOccurrence.root stage
          (localBlockEndpointBoundaryRelation stage)) =
        runtimeJointIntegralFace
          (runtimeJointRelationGeneratorValue observation nontrivial
            (primeRuntimeStage (rowPrime row), .sourceBoundary)) ∧
      runtimeJointSourceBoundaryPresentedEvent
          (primeRuntimeStage (rowPrime row)) ∈
        ((runtimeJointFaithfulStepAt observation nontrivial 0).history.observation
          (primeRuntimeStage (rowPrime row))).trace ∧
      runtimeJointSourceBoundaryPresentedEvent
          (primeRuntimeStage (rowPrime row)) ∉
        ((runtimeJointFaithfulStepAt observation nontrivial 0).history.observation
          (primeRuntimeStage (rowPrime row))).frontier ∧
      (runtimeJointFaithfulStepAt observation nontrivial 0).faithful.freeEvaluation
          (runtimeJointSourceBoundaryStageRelation
            (primeRuntimeStage (rowPrime row))) = 0 ∧
      (type_of% (runtimeJointFaithfulStep_factorizes observation nontrivial 0)) := by
  exact ⟨blockEndpointRawEffect_runtimeSourceBoundary_integral
      observation nontrivial stage row,
    blockPrimeCofinalSourceBoundary_mem observation nontrivial stage row,
    by
      simpa using runtimeJointSourceBoundary_not_frontier
        observation nontrivial 0 (primeRuntimeStage (rowPrime row)),
    runtimeJointFaithful_freeEvaluation_sourceBoundary_zero
      observation nontrivial 0 (primeRuntimeStage (rowPrime row)),
    runtimeJointFaithfulStep_factorizes observation nontrivial 0⟩

end
end PrimeScaleCofinal
end RawEffect
end ActionCofiber
end AllPlace
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
