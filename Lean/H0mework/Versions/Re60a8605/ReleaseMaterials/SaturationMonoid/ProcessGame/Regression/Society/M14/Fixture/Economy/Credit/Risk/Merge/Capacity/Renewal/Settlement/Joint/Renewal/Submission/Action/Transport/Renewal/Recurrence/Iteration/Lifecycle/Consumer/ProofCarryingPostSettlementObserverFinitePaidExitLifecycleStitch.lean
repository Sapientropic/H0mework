import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.NoGo.SourceGeneratedPostSettlementObserverFinitePaidExitLifecycleStitchNoGo
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Consumer.ProofCarryingPostSettlementObserverFinitePaidSelfU8Iteration
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Consumer.Necessity.Lifecycle.ProofCarryingPaidExitLifecycleMaximumRegression

/-!
# Proof-carrying self-U8 / paid-exit lifecycle stitch

For one explicit fuel, every already generated self-U8 cycle is the stage-zero
mouth of the existing full paid-exit lifecycle at the same actual Payment
index.  The direct consumer retains leave execution, role-independent
continuation, services/future, external residual disposition and the
full-capture counterlife at every node.

The raw cycle-by-stage rectangle factors through its `fuel + 4` absolute
occurrences.  Equal absolute indices are one producer occurrence; different
absolute indices have one action readout but different outer authority, `K`
and Payment.  This bounded `Prop` audit stores no grid, schedule, history,
registry, root, ledger, runtime or completed future.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingPostSettlementObserverFinitePaidExitLifecycleStitch

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Observer Renewal UniversalRootGrammar
open Lifecycle Universal Relations Power Exchange Settlement Price Money UBI
open Capacity Space CrossingCost
open M14UBIPeriodicActualServiceCapacity
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityBirthBearerExit
open M14SourceGeneratedContributionCapacityPostSettlementExternalLiability
open M14SourceGeneratedPaidSuccessorBearerExerciseStandingRenewal
open M14SourceGeneratedPaidSuccessorBearerRoleIndependentContinuation
open M14SourceGeneratedPaidSuccessorPostContinuationExternalResidualDisposition
open M14SourceGeneratedPaidExitLifecycleTemporalSpine
open M14SourceGeneratedProofCarryingPaidExitLifecycleMaximum
open M14SourceGeneratedPaidExitLifecycleMaximumNoGo
open M14ProofCarryingPaidExitLifecycleMaximumRegression
open M14SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislation
open M14SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislation.SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
open M14SourceGeneratedPostSettlementObserverAuthorityRevisedDispositionMorphism
open M14SourceGeneratedPostSettlementObserverAuthorityRevisedDispositionMorphism.SourceGeneratedPostSettlementObserverAuthorityRevisedDispositionMorphismAt
open M14ProofCarryingPostSettlementObserverAuthorityRevisedDispositionMorphism
open M14SourceGeneratedPostSettlementObserverPaidSuccessorRenewal
open M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8Iteration
open M14ProofCarryingPostSettlementObserverFinitePaidSelfU8Iteration
open M14SourceGeneratedPostSettlementObserverFinitePaidExitLifecycleStitch
open M14SourceGeneratedPostSettlementObserverFinitePaidExitLifecycleStitchNoGo

structure ProofCarryingPostSettlementObserverFinitePaidExitLifecycleStitchAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (fuel : Nat) : Prop where
  private mk ::
  finiteIterationAudit :
    ProofCarryingPostSettlementObserverFinitePaidSelfU8IterationAt initial fuel
  everyCycleIndexExact : ∀ node : Fin (fuel + 1),
    cycleLifecycleIndex initial node.1 = boundary + node.1 + 2
  everyCycleMaximum : ∀ node : Fin (fuel + 1),
    Nonempty
      (ProofCarryingPaidExitLifecycleMaximumAt oldVisit sourceIndex
        (cycleLifecycleIndex initial node.1))
  everyCycleMaximumAudit : ∀ node : Fin (fuel + 1),
    PaidExitLifecycleMaximumAuditAt (cycleLifecycleMaximum initial node.1)
  everyCyclePaidRenewalIsLifecycleStageZero : ∀ node : Fin (fuel + 1),
    paidRenewalAt (cycleMorphism (cycleAt initial node.1)) =
      cycleLifecycle initial node.1
  everyCycleSourceEventIsSpanEvent : ∀ node : Fin (fuel + 1),
    HEq (cycleLifecycle initial node.1).sourceConsequence.outerRootEvent
      (sourceSubmission
        (legislationSpan
          (cycleMorphism (cycleAt initial node.1)))).exactEvent
  everyCycleSourcePaymentIsSpanPayment : ∀ node : Fin (fuel + 1),
    HEq (cycleLifecycle initial node.1
      ).sourceConsequence.actualExit.paymentOccurrence
      (targetPaymentOccurrence
        (legislationSpan (cycleMorphism (cycleAt initial node.1))))
  everyCycleLeaveExecution : ∀ node : Fin (fuel + 1),
    PaidExitLifecycleResponseExecutionAt oldVisit sourceIndex
      (cycleLifecycleIndex initial node.1)
  everyCycleRoleIndependentContinuation : ∀ node : Fin (fuel + 1),
    PaidExitLifecycleRoleIndependentContinuationAt oldVisit sourceIndex
      (cycleLifecycleIndex initial node.1)
      (cycleLifecycleMaximum initial node.1).actionableRenewal.code
  everyCycleExternalResidualDisposition : ∀ node : Fin (fuel + 1),
    PaidExitLifecycleExternalDispositionAt oldVisit sourceIndex
      (cycleLifecycleIndex initial node.1)
  everyCycleServicesAndFuture : ∀ node : Fin (fuel + 1),
    PaidExitLifecycleServicesAndFutureAt oldVisit sourceIndex
      (cycleLifecycleIndex initial node.1)
  everyCycleFullCaptureCounterlife : ∀ node : Fin (fuel + 1),
    Nonempty
      (ProofCarryingFullCapturePaidExitCounterlifeAt oldVisit sourceIndex
        (cycleLifecycleIndex initial node.1))
  everyCycleFullCaptureReportedMaximumEmpty : ∀ node : Fin (fuel + 1),
    IsEmpty
      (ExactFullCaptureReportedPaidExitLifecycleMaximumAt
        (cycleFullCaptureCounterlifeAt initial node.1))
  everyCycleActionReadoutLeftInverseEmpty : ∀ node : Fin (fuel + 1),
    IsEmpty
      (ExactPaidExitLifecycleActionReadoutLeftInverseAt
        (cycleLifecycleMaximum initial node.1))
  everyCycleSourceOwnershipDeletionEmpty : ∀ node : Fin (fuel + 1),
    IsEmpty
      (ExactPostContinuationSourceOwnershipDeletionAt
        (cycleLifecycleMaximum initial node.1).disposition)
  everyCycleRootConsumerDeletionEmpty : ∀ node : Fin (fuel + 1),
    IsEmpty
      (ExactPostContinuationRootConsumerDeletionAt
        (cycleLifecycleMaximum initial node.1).disposition)
  everyCycleLocalEmptyErasureEmpty : ∀ node : Fin (fuel + 1),
    IsEmpty
      (ExactPostContinuationLocalEmptyErasesExternalLiabilityAt
        (cycleLifecycleMaximum initial node.1).disposition)
  everyAdjacentStageOverlap : ∀ edge : Fin fuel,
    cycleLifecycleStageRenewalAt initial edge.1 cycleLifecycleStageOne =
      cycleLifecycleStageRenewalAt initial (edge.1 + 1)
        cycleLifecycleStageZero
  everyAdjacentEventOverlap : ∀ edge : Fin fuel,
    (cycleLifecycle initial edge.1).targetConsequence.outerRootEvent =
      (cycleLifecycle initial (edge.1 + 1)
        ).sourceConsequence.outerRootEvent
  everyAdjacentPaymentOverlap : ∀ edge : Fin fuel,
    (cycleLifecycle initial edge.1
      ).targetConsequence.actualExit.paymentOccurrence =
      (cycleLifecycle initial (edge.1 + 1)
        ).sourceConsequence.actualExit.paymentOccurrence
  everyAdjacentAuthorityOverlap : ∀ edge : Fin fuel,
    (cycleLifecycle initial edge.1).targetOuterAuthority =
      (cycleLifecycle initial (edge.1 + 1)).sourceOuterAuthority
  everyAdjacentKOverlap : ∀ edge : Fin fuel,
    (cycleLifecycle initial edge.1).targetActualServiceK =
      (cycleLifecycle initial (edge.1 + 1)).sourceActualServiceK
  rawAbsoluteSurjective : Function.Surjective
    (rawFiniteLifecycleAbsoluteStageAt (fuel := fuel))
  everyRawStageFactors : ∀ raw : RawFinitePaidExitLifecycleStageAt fuel,
    HEq (cycleLifecycleStageRenewalAt initial raw.1.1 raw.2)
      (absoluteLifecycleRenewalAt initial
        (rawFiniteLifecycleAbsoluteStageAt raw))
  everyOverlapRawCoordinatesDistinct : ∀ edge : Fin fuel,
    overlapLeftRawAt edge ≠ overlapRightRawAt edge
  everyOverlapSameAbsolute : ∀ edge : Fin fuel,
    rawFiniteLifecycleAbsoluteStageAt (overlapLeftRawAt edge) =
      rawFiniteLifecycleAbsoluteStageAt (overlapRightRawAt edge)
  everyOverlapSameRenewalOccurrence : ∀ edge : Fin fuel,
    cycleLifecycleStageRenewalAt initial edge.1 cycleLifecycleStageOne =
      cycleLifecycleStageRenewalAt initial (edge.1 + 1)
        cycleLifecycleStageZero
  everySameAbsoluteClaimedDifferentEmpty :
    ∀ left right : RawFinitePaidExitLifecycleStageAt fuel,
      IsEmpty
        (ExactSameAbsoluteClaimedDifferentLifecycleOccurrenceAt initial left
          right)
  absoluteOuterAuthorityInjective : Function.Injective
    (absoluteLifecycleOuterAuthorityAt (fuel := fuel) initial)
  absoluteKInjective : Function.Injective
    (absoluteLifecycleKAt (fuel := fuel) initial)
  absolutePaymentInjective : Function.Injective
    (absoluteLifecyclePaymentOccurrenceAt (fuel := fuel) initial)
  everyAbsolutePairSameOrStrongKernel :
    ∀ left right : AbsoluteFinitePaidExitLifecycleStageAt fuel,
      (left = right ∧
          absoluteLifecycleOuterAuthorityAt initial left =
            absoluteLifecycleOuterAuthorityAt initial right ∧
          absoluteLifecycleKAt initial left =
            absoluteLifecycleKAt initial right ∧
          absoluteLifecyclePaymentOccurrenceAt initial left =
            absoluteLifecyclePaymentOccurrenceAt initial right) ∨
        (left ≠ right ∧
          absoluteLifecycleActionAt initial left =
            absoluteLifecycleActionAt initial right ∧
          absoluteLifecycleOuterAuthorityAt initial left ≠
            absoluteLifecycleOuterAuthorityAt initial right ∧
          absoluteLifecycleKAt initial left ≠
            absoluteLifecycleKAt initial right ∧
          absoluteLifecyclePaymentOccurrenceAt initial left ≠
            absoluteLifecyclePaymentOccurrenceAt initial right)
  absoluteActionNoOccurrenceReconstruction :
    ¬ ∃ reconstruct : birthBearerExitExerciseController.ExactActionSeed →
        AbsoluteFinitePaidExitLifecycleStageAt fuel,
      Function.LeftInverse reconstruct
        (absoluteLifecycleActionObserverAt (fuel := fuel) initial).forget
  absoluteActionNoAuthorityFactorization :
    ¬ Nonempty
      (AuthorityFactorization
        (absoluteLifecycleActionObserverAt (fuel := fuel) initial))
  absoluteActionNoFaithfulReconstruction :
    ¬ Nonempty
      (FaithfulAuthorityReconstruction
        (absoluteLifecycleActionObserverAt (fuel := fuel) initial))
  finalOneMoreLifecycleAudit :
    PaidExitLifecycleMaximumAuditAt (cycleLifecycleMaximum initial (fuel + 1))
  finalOneMorePaidRenewalIsLifecycleStageZero :
    paidRenewalAt (cycleMorphism (cycleAt initial (fuel + 1))) =
      cycleLifecycle initial (fuel + 1)

theorem proofCarryingPostSettlementObserverFinitePaidExitLifecycleStitch
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (fuel : Nat) :
    ProofCarryingPostSettlementObserverFinitePaidExitLifecycleStitchAt initial
      fuel where
  finiteIterationAudit :=
    proofCarryingPostSettlementObserverFinitePaidSelfU8Iteration initial fuel
  everyCycleIndexExact := fun node => cycleLifecycleIndex_exact initial node.1
  everyCycleMaximum := fun node => ⟨cycleLifecycleMaximum initial node.1⟩
  everyCycleMaximumAudit := fun node =>
    paidExitLifecycleMaximumAuditAt oldVisit sourceIndex
      (cycleLifecycleIndex initial node.1)
  everyCyclePaidRenewalIsLifecycleStageZero := fun node =>
    cycleMorphismPaidRenewal_eq_cycleLifecycle initial node.1
  everyCycleSourceEventIsSpanEvent := fun node =>
    heq_of_eq
      (cycleLifecycle_sourceEvent_isCycleSpanSourceEvent initial node.1)
  everyCycleSourcePaymentIsSpanPayment := fun node =>
    heq_of_eq
      (cycleLifecycle_sourcePayment_isCycleSpanPayment initial node.1)
  everyCycleLeaveExecution := fun node =>
    (cycleLifecycleMaximum initial node.1).rooted.responseExecution
  everyCycleRoleIndependentContinuation := fun node =>
    (cycleLifecycleMaximum initial node.1).rooted.roleIndependentContinuation
  everyCycleExternalResidualDisposition := fun node =>
    (cycleLifecycleMaximum initial node.1).rooted.externalDisposition
  everyCycleServicesAndFuture := fun node =>
    (cycleLifecycleMaximum initial node.1).rooted.servicesAndFuture
  everyCycleFullCaptureCounterlife := fun node =>
    ⟨cycleFullCaptureCounterlifeAt initial node.1⟩
  everyCycleFullCaptureReportedMaximumEmpty := fun node =>
    cycleFullCaptureReportedMaximum_isEmpty initial node.1
  everyCycleActionReadoutLeftInverseEmpty := fun node =>
    cycleActionReadoutLeftInverse_isEmpty initial node.1
  everyCycleSourceOwnershipDeletionEmpty := fun node =>
    cycleSourceOwnershipDeletion_isEmpty initial node.1
  everyCycleRootConsumerDeletionEmpty := fun node =>
    cycleRootConsumerDeletion_isEmpty initial node.1
  everyCycleLocalEmptyErasureEmpty := fun node =>
    cycleLocalEmptyErasure_isEmpty initial node.1
  everyAdjacentStageOverlap := fun edge =>
    cycleLifecycleStageOne_eq_nextStageZero initial edge.1
  everyAdjacentEventOverlap := fun edge =>
    cycleLifecycleTargetEvent_eq_nextSourceEvent initial edge.1
  everyAdjacentPaymentOverlap := fun edge =>
    cycleLifecycleTargetPayment_eq_nextSourcePayment initial edge.1
  everyAdjacentAuthorityOverlap := fun edge =>
    cycleLifecycleTargetAuthority_eq_nextSourceAuthority initial edge.1
  everyAdjacentKOverlap := fun edge =>
    cycleLifecycleTargetK_eq_nextSourceK initial edge.1
  rawAbsoluteSurjective := rawFiniteLifecycleAbsoluteStage_surjective fuel
  everyRawStageFactors := rawLifecycleStageRenewal_factors initial
  everyOverlapRawCoordinatesDistinct := overlapRawCoordinates_ne
  everyOverlapSameAbsolute := overlapRawCoordinates_sameAbsolute
  everyOverlapSameRenewalOccurrence :=
    overlapRawCoordinates_sameRenewalProducer initial
  everySameAbsoluteClaimedDifferentEmpty :=
    sameAbsoluteClaimedDifferentLifecycleOccurrence_isEmpty initial
  absoluteOuterAuthorityInjective :=
    absoluteLifecycleOuterAuthority_injective initial
  absoluteKInjective := absoluteLifecycleK_injective initial
  absolutePaymentInjective :=
    absoluteLifecyclePaymentOccurrence_injective initial
  everyAbsolutePairSameOrStrongKernel :=
    absoluteLifecycleSameOrStrongKernel initial
  absoluteActionNoOccurrenceReconstruction :=
    absoluteLifecycleAction_noOccurrenceReconstruction initial
  absoluteActionNoAuthorityFactorization :=
    absoluteLifecycleAction_noAuthorityFactorization initial
  absoluteActionNoFaithfulReconstruction :=
    absoluteLifecycleAction_noFaithfulReconstruction initial
  finalOneMoreLifecycleAudit :=
    paidExitLifecycleMaximumAuditAt oldVisit sourceIndex
      (cycleLifecycleIndex initial (fuel + 1))
  finalOneMorePaidRenewalIsLifecycleStageZero :=
    cycleMorphismPaidRenewal_eq_cycleLifecycle initial (fuel + 1)

abbrev AnyProofCarryingPostSettlementObserverFinitePaidExitLifecycleStitchAt
    (oldVisit : OldVisit) (sourceIndex boundary fuel : Nat) :=
  { initial : CycleAt oldVisit sourceIndex boundary //
    ProofCarryingPostSettlementObserverFinitePaidExitLifecycleStitchAt initial
      fuel }

def canonicalProofCarryingPostSettlementObserverFinitePaidExitLifecycleStitchAt
    (oldVisit : OldVisit) (sourceIndex boundary fuel : Nat) :
    AnyProofCarryingPostSettlementObserverFinitePaidExitLifecycleStitchAt
      oldVisit sourceIndex boundary fuel :=
  let initial :=
    canonicalProofCarryingPostSettlementObserverAuthorityRevisedDispositionMorphismAt
      oldVisit sourceIndex boundary
  ⟨initial,
    proofCarryingPostSettlementObserverFinitePaidExitLifecycleStitch initial
      fuel⟩

end
end M14ProofCarryingPostSettlementObserverFinitePaidExitLifecycleStitch
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingPostSettlementObserverFinitePaidExitLifecycleStitch.proofCarryingPostSettlementObserverFinitePaidExitLifecycleStitch
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingPostSettlementObserverFinitePaidExitLifecycleStitch.canonicalProofCarryingPostSettlementObserverFinitePaidExitLifecycleStitchAt
