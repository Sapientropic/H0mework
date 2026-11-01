import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.CrossCompiler.Readout.Recognition.Admission.Constitution.Universal.Consumer.ProofCarryingCanonicalSocietyUniversalGrammarTotality
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Payment.Novelty.PostSettlement.Execution.Runtime.Consumer.ProofCarryingContributionCapacityCofinalNoveltySelfU8
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Bootstrap.SourceGeneratedPostSettlementObserverSubmissionBootstrap

/-!
# Universal failed bearer to external paid self-U8 splice

The universal full-capture search failure does not receive actual-write
authority.  Its generated residual bearer is instead the exact actual exit of
the cofinal right Payment at the same universal index.  That external
joint-root Payment already owns the rooted failure, minimal coface, named U8
runtime, first write, two-row recovery and revised next.

The cycle alignment has a mandatory offset:

    i = cycleCanonicalRootLawIndex initial depth
    right replay at i = cycle replay at depth + 2.

Consequently the lawful cycle tick is
`ExactCanonicalSelfU8TickAt initial (depth + 2)`, never the current-depth
tick.  This module is a cross-occurrence consumer/transporter; search remains
diagnostic.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingCanonicalSocietyUniversalFailurePaidSelfU8Splice

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Observer Renewal UniversalRootGrammar
open Lifecycle Universal Relations Power Exchange Settlement Price Money UBI
open Capacity Space CrossingCost
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityPostSettlementPaidReplay
open M14SourceGeneratedContributionCapacityJointSettlementWorld
open M14SourceGeneratedContributionCapacityPostSettlementRenewalRoot
open M14SourceGeneratedPostSettlementObserverSubmissionU8
open M14SourceGeneratedPostSettlementObserverPaidSelfU8Recurrence.SourceGeneratedPostSettlementObserverPaidSelfU8RecurrenceAt
open M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8Iteration
open M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8IterationNoGo
open M14SourceGeneratedPostSettlementObserverFinitePaidExitLifecycleStitch
open M14SourceGeneratedCycleCanonicalRootLawStep
open M14SourceGeneratedCanonicalSocietyCofinalReadout
open M14SourceGeneratedContributionCapacityCofinalProductiveNovelty
open M14SourceGeneratedContributionCapacityCofinalNoveltyRootedFailure
open M14SourceGeneratedContributionCapacityCofinalNoveltyU8Revision
open M14SourceGeneratedContributionCapacityCofinalNoveltyU8Compilation
open M14SourceGeneratedContributionCapacityCofinalNoveltyU8Runtime
open M14ProofCarryingContributionCapacityCofinalNoveltySelfU8
open M14ProofCarryingCanonicalSocietyFivefoldConstitution
open M14ProofCarryingCanonicalSocietyUniversalGrammarTotality

def universalFailureBoundaryAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) : Nat :=
  cycleCanonicalRootLawIndex initial depth

def universalFailureExternalNoveltyAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :=
  sourceGeneratedContributionCapacitySourceProductiveNoveltyAt oldVisit
    sourceIndex (universalFailureBoundaryAt initial depth)

def universalFailureExternalRootedBridgeAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :=
  sourceGeneratedContributionCapacityCofinalNoveltyRootedFailureAt
    (universalFailureExternalNoveltyAt initial depth)

def universalFailureExternalRevisionBridgeAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :=
  sourceGeneratedContributionCapacityCofinalNoveltyU8RevisionAt
    (universalFailureExternalRootedBridgeAt initial depth)

def universalFailureExternalExecutionAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :=
  sourceGeneratedContributionCapacityCofinalNoveltyU8CompilationAt
    (universalFailureExternalRevisionBridgeAt initial depth)

def universalFailureExternalSelfU8At
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :=
  selfU8 (universalFailureExternalExecutionAt initial depth)

def universalFailureExternalRevisedNextAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :=
  (universalFailureExternalSelfU8At initial depth).revisedNext

/-- The incidence anchor: the failed search face and the cofinal right replay
select the same exact post-root event.  This is definitional after restoring
the generated failure; it is not inferred from the exit carrier's
`Subsingleton` instance. -/
theorem universalFailureExactEvent_eq_externalRightPostRootEvent
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    {constitution :
      ProofCarryingCanonicalSocietyFivefoldConstitutionAt initial}
    {observerFuel depth : Nat}
    (point :
      ProofCarryingCanonicalSocietyUniversalGrammarPointAt constitution
        observerFuel depth) :
    point.fullCaptureFailure.grammar.searchGrammar.exactEvent =
      (rightReplayAt oldVisit sourceIndex
        (universalFailureBoundaryAt initial depth)).2.rootEvent := by
  rw [point.fullCaptureFailureExact]
  rfl

theorem universalFailureResidualBearer_eq_externalRightActualExit
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    {constitution :
      ProofCarryingCanonicalSocietyFivefoldConstitutionAt initial}
    {observerFuel depth : Nat}
    (point :
      ProofCarryingCanonicalSocietyUniversalGrammarPointAt constitution
        observerFuel depth) :
    point.fullCaptureFailure.residualBearer =
      (rightReplayAt oldVisit sourceIndex
        (universalFailureBoundaryAt initial depth)).2.futureBirth.actualExit :=
  by
    rw [point.fullCaptureFailureExact]
    rfl

theorem universalFailureResidualPayment_eq_externalRightPayment
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    {constitution :
      ProofCarryingCanonicalSocietyFivefoldConstitutionAt initial}
    {observerFuel depth : Nat}
    (point :
      ProofCarryingCanonicalSocietyUniversalGrammarPointAt constitution
        observerFuel depth) :
    point.fullCaptureFailure.residualBearer.paymentOccurrence =
      ((rightReplayAt oldVisit sourceIndex
        (universalFailureBoundaryAt initial depth)).2.futureBirth.actualExit
          ).paymentOccurrence :=
  congrArg (fun exit => exit.paymentOccurrence)
    (universalFailureResidualBearer_eq_externalRightActualExit point)

theorem depthPlusTwoCycleReplay_eq_externalRightReplay
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    cycleReplayAt initial (depth + 2) =
      rightReplayAt oldVisit sourceIndex
        (universalFailureBoundaryAt initial depth) := by
  rw [cycleReplayAt_exact]
  change
    contributionCapacityPostSettlementPaidReplayAt oldVisit sourceIndex
        (boundary + (depth + 2) + 2) =
      contributionCapacityPostSettlementPaidReplayAt oldVisit sourceIndex
        (cycleCanonicalRootLawIndex initial depth + 2)
  unfold cycleCanonicalRootLawIndex
  rw [cycleLifecycleIndex_exact]
  congr 1

theorem depthPlusTwoSelfU8OldRight_eq_externalRightReplay
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    (nextNovelty (stepAt initial (depth + 2))).leftReplay =
      rightReplayAt oldVisit sourceIndex
        (universalFailureBoundaryAt initial depth) := by
  let tick := everyExactCanonicalSelfU8Tick initial (depth + 2)
  have exactOldRight := tick.oldRightIsNextLeft
  convert exactOldRight using 1
  rfl

theorem universalFailureExternalGeneratedNext_isSelfU8RevisedNext
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    (legislation (universalFailureExternalExecutionAt initial depth)
      ).generatedNext =
      universalFailureExternalRevisedNextAt initial depth :=
  rfl

structure ProofCarryingCanonicalSocietyUniversalFailurePaidSelfU8SpliceAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    (constitution :
      ProofCarryingCanonicalSocietyFivefoldConstitutionAt initial)
    (observerFuel depth : Nat) : Type 32 where
  private mk ::
  universalPoint :
    ProofCarryingCanonicalSocietyUniversalGrammarPointAt constitution
      observerFuel depth
  failureEventIsExternalRightPostRootEvent :
    universalPoint.fullCaptureFailure.grammar.searchGrammar.exactEvent =
      (rightReplayAt oldVisit sourceIndex
        (universalFailureBoundaryAt initial depth)).2.rootEvent
  failureBearerIsExternalRightExit :
    universalPoint.fullCaptureFailure.residualBearer =
      (rightReplayAt oldVisit sourceIndex
        (universalFailureBoundaryAt initial depth)).2.futureBirth.actualExit
  failurePaymentIsExternalRightPayment :
    universalPoint.fullCaptureFailure.residualBearer.paymentOccurrence =
      ((rightReplayAt oldVisit sourceIndex
        (universalFailureBoundaryAt initial depth)).2.futureBirth.actualExit
          ).paymentOccurrence
  sourceTargetOccurrencesDistinct :
    type_of% universalPoint.fullCaptureFailure.externalLiability.crossRootOccurrenceDistinct
  searchHasNoActualWrite :
    type_of% universalPoint.fullCaptureFailure.searchNoActualWrite
  searchWorldWritingSelfU8Empty :
    type_of% universalPoint.searchWorldWritingSelfU8Empty
  externalSelfU8Certificate :
    ProofCarryingContributionCapacityCofinalNoveltySelfU8CertificateAt oldVisit
      sourceIndex (universalFailureBoundaryAt initial depth)
  rightPaymentRootOccurrenceExact :
    type_of% (M14SourceGeneratedPostSettlementObserverSubmissionU8.rightPaymentRootOccurrence_exact
      oldVisit sourceIndex (universalFailureBoundaryAt initial depth))
  rightRootedOccurrenceIsPayment :
    type_of% (M14SourceGeneratedPostSettlementObserverSubmissionU8.rootedOccurrence_isRightPaymentOccurrence
      oldVisit sourceIndex (universalFailureBoundaryAt initial depth))
  selfU8OccurrenceIsRightPayment :
    type_of% externalSelfU8Certificate.selfU8OccurrenceIsRightPayment
  selfU8UsesExistingFailure :
    type_of% externalSelfU8Certificate.sameRootExistingFailure
  runtimeConsumesExactCore :
    type_of% externalSelfU8Certificate.runtimeConsumesCore
  firstWriteAndRecovery :
    type_of% externalSelfU8Certificate.firstWriteAndRecovery
  postRootCannotFakeActualFailure :
    ∀ {support : (JointSettlementNAt oldVisit).Support},
      ∀ obstruction : (JointSettlementNAt oldVisit).ObstructionAt support,
        IsEmpty
          (ActualExpressibilityFailure
            (ContributionCapacityPostSettlementRenewalRootAt oldVisit
              sourceIndex).source.base.lawSurface obstruction)
  depthPlusTwoSelfU8 :
    ExactCanonicalSelfU8TickAt initial (depth + 2)
  depthPlusTwoCycleReplayIsExternalRightReplay :
    cycleReplayAt initial (depth + 2) =
      rightReplayAt oldVisit sourceIndex
        (universalFailureBoundaryAt initial depth)
  depthPlusTwoSelfU8OldRightIsExternalRightReplay :
    (nextNovelty (stepAt initial (depth + 2))).leftReplay =
      rightReplayAt oldVisit sourceIndex
        (universalFailureBoundaryAt initial depth)
  externalGeneratedNextIsSelfU8RevisedNext :
    (legislation (universalFailureExternalExecutionAt initial depth)
      ).generatedNext =
      universalFailureExternalRevisedNextAt initial depth

def proofCarryingCanonicalSocietyUniversalFailurePaidSelfU8Splice
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    (constitution :
      ProofCarryingCanonicalSocietyFivefoldConstitutionAt initial)
    (observerFuel depth : Nat) :
    ProofCarryingCanonicalSocietyUniversalFailurePaidSelfU8SpliceAt
      constitution observerFuel depth := by
  let point :=
    proofCarryingCanonicalSocietyUniversalGrammarPoint constitution
      observerFuel depth
  let certificate :=
    proofCarryingContributionCapacityCofinalNoveltySelfU8At oldVisit
      sourceIndex (universalFailureBoundaryAt initial depth)
  exact
    { universalPoint := point
      failureEventIsExternalRightPostRootEvent :=
        universalFailureExactEvent_eq_externalRightPostRootEvent point
      failureBearerIsExternalRightExit :=
        universalFailureResidualBearer_eq_externalRightActualExit point
      failurePaymentIsExternalRightPayment :=
        universalFailureResidualPayment_eq_externalRightPayment point
      sourceTargetOccurrencesDistinct :=
        point.fullCaptureFailure.externalLiability.crossRootOccurrenceDistinct
      searchHasNoActualWrite := point.fullCaptureFailure.searchNoActualWrite
      searchWorldWritingSelfU8Empty :=
        point.searchWorldWritingSelfU8Empty
      externalSelfU8Certificate := certificate
      rightPaymentRootOccurrenceExact :=
        M14SourceGeneratedPostSettlementObserverSubmissionU8.rightPaymentRootOccurrence_exact
          oldVisit sourceIndex (universalFailureBoundaryAt initial depth)
      rightRootedOccurrenceIsPayment :=
        M14SourceGeneratedPostSettlementObserverSubmissionU8.rootedOccurrence_isRightPaymentOccurrence
          oldVisit sourceIndex (universalFailureBoundaryAt initial depth)
      selfU8OccurrenceIsRightPayment :=
        certificate.selfU8OccurrenceIsRightPayment
      selfU8UsesExistingFailure := certificate.sameRootExistingFailure
      runtimeConsumesExactCore := certificate.runtimeConsumesCore
      firstWriteAndRecovery := certificate.firstWriteAndRecovery
      postRootCannotFakeActualFailure := certificate.postRootCannotFakeFailure
      depthPlusTwoSelfU8 :=
        constitution.everySelfU8Tick (depth + 2) observerFuel
      depthPlusTwoCycleReplayIsExternalRightReplay :=
        depthPlusTwoCycleReplay_eq_externalRightReplay initial depth
      depthPlusTwoSelfU8OldRightIsExternalRightReplay :=
        depthPlusTwoSelfU8OldRight_eq_externalRightReplay initial depth
      externalGeneratedNextIsSelfU8RevisedNext :=
        universalFailureExternalGeneratedNext_isSelfU8RevisedNext initial
          depth }

structure ProofCarryingCanonicalSocietyUniversalFailurePaidSelfU8TotalityAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    (constitution :
      ProofCarryingCanonicalSocietyFivefoldConstitutionAt initial) : Prop where
  private mk ::
  everyDepth : ∀ observerFuel depth,
    Nonempty
      (ProofCarryingCanonicalSocietyUniversalFailurePaidSelfU8SpliceAt
        constitution observerFuel depth)

theorem proofCarryingCanonicalSocietyUniversalFailurePaidSelfU8Totality
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    (constitution :
      ProofCarryingCanonicalSocietyFivefoldConstitutionAt initial) :
    ProofCarryingCanonicalSocietyUniversalFailurePaidSelfU8TotalityAt
      constitution where
  everyDepth := fun observerFuel depth =>
    ⟨proofCarryingCanonicalSocietyUniversalFailurePaidSelfU8Splice
      constitution observerFuel depth⟩

theorem universalSearchFailure_externalPaymentSelfU8_strictAuthoritySeparation
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    {constitution :
      ProofCarryingCanonicalSocietyFivefoldConstitutionAt initial}
    {observerFuel depth : Nat}
    (splice :
      ProofCarryingCanonicalSocietyUniversalFailurePaidSelfU8SpliceAt
        constitution observerFuel depth) :
    splice.universalPoint.fullCaptureFailure.grammar.searchGrammar.exactEvent =
        (rightReplayAt oldVisit sourceIndex
          (universalFailureBoundaryAt initial depth)).2.rootEvent ∧
      splice.universalPoint.fullCaptureFailure.residualBearer =
        (rightReplayAt oldVisit sourceIndex
          (universalFailureBoundaryAt initial depth)).2.futureBirth.actualExit ∧
      type_of% splice.failurePaymentIsExternalRightPayment ∧
      type_of%
        splice.universalPoint.fullCaptureFailure.sameRootLedgerAndNext ∧
      type_of% splice.sourceTargetOccurrencesDistinct ∧
      type_of% splice.searchHasNoActualWrite ∧
      type_of% splice.searchWorldWritingSelfU8Empty ∧
      (∀ {support : (JointSettlementNAt oldVisit).Support},
        ∀ obstruction : (JointSettlementNAt oldVisit).ObstructionAt support,
          IsEmpty
            (ActualExpressibilityFailure
              (ContributionCapacityPostSettlementRenewalRootAt oldVisit
                sourceIndex).source.base.lawSurface obstruction)) ∧
      type_of% splice.rightPaymentRootOccurrenceExact ∧
      type_of% splice.rightRootedOccurrenceIsPayment ∧
      type_of% splice.externalSelfU8Certificate.sameNormalDifferentK ∧
      type_of% splice.runtimeConsumesExactCore ∧
      type_of% splice.externalSelfU8Certificate.runtimeSpliceExact ∧
      type_of% splice.externalSelfU8Certificate.exactSelfU8 ∧
      type_of% splice.selfU8OccurrenceIsRightPayment ∧
      type_of% splice.selfU8UsesExistingFailure ∧
      type_of% splice.firstWriteAndRecovery ∧
      ExactCanonicalSelfU8TickAt initial (depth + 2) ∧
      cycleReplayAt initial (depth + 2) =
        rightReplayAt oldVisit sourceIndex
          (universalFailureBoundaryAt initial depth) ∧
      (nextNovelty (stepAt initial (depth + 2))).leftReplay =
        rightReplayAt oldVisit sourceIndex
          (universalFailureBoundaryAt initial depth) ∧
      (legislation (universalFailureExternalExecutionAt initial depth)
        ).generatedNext =
        universalFailureExternalRevisedNextAt initial depth :=
  ⟨splice.failureEventIsExternalRightPostRootEvent,
    splice.failureBearerIsExternalRightExit,
    splice.failurePaymentIsExternalRightPayment,
    splice.universalPoint.fullCaptureFailure.sameRootLedgerAndNext,
    splice.sourceTargetOccurrencesDistinct,
    splice.searchHasNoActualWrite,
    splice.searchWorldWritingSelfU8Empty,
    splice.postRootCannotFakeActualFailure,
    splice.rightPaymentRootOccurrenceExact,
    splice.rightRootedOccurrenceIsPayment,
    splice.externalSelfU8Certificate.sameNormalDifferentK,
    splice.runtimeConsumesExactCore,
    splice.externalSelfU8Certificate.runtimeSpliceExact,
    splice.externalSelfU8Certificate.exactSelfU8,
    splice.selfU8OccurrenceIsRightPayment,
    splice.selfU8UsesExistingFailure,
    splice.firstWriteAndRecovery,
    splice.depthPlusTwoSelfU8,
    splice.depthPlusTwoCycleReplayIsExternalRightReplay,
    splice.depthPlusTwoSelfU8OldRightIsExternalRightReplay,
    splice.externalGeneratedNextIsSelfU8RevisedNext⟩

theorem canonicalSocietyUniversalFailurePaidSelfU8_directConsumer
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    (constitution :
      ProofCarryingCanonicalSocietyFivefoldConstitutionAt initial) :
    ProofCarryingCanonicalSocietyUniversalFailurePaidSelfU8TotalityAt
        constitution ∧
      (∀ observerFuel depth,
        Nonempty
          (ProofCarryingCanonicalSocietyUniversalFailurePaidSelfU8SpliceAt
            constitution observerFuel depth)) :=
  let totality :=
    proofCarryingCanonicalSocietyUniversalFailurePaidSelfU8Totality
      constitution
  ⟨totality, totality.everyDepth⟩

end
end M14ProofCarryingCanonicalSocietyUniversalFailurePaidSelfU8Splice
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingCanonicalSocietyUniversalFailurePaidSelfU8Splice.universalFailureResidualBearer_eq_externalRightActualExit
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingCanonicalSocietyUniversalFailurePaidSelfU8Splice.universalFailureExactEvent_eq_externalRightPostRootEvent
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingCanonicalSocietyUniversalFailurePaidSelfU8Splice.depthPlusTwoCycleReplay_eq_externalRightReplay
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingCanonicalSocietyUniversalFailurePaidSelfU8Splice.proofCarryingCanonicalSocietyUniversalFailurePaidSelfU8Splice
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingCanonicalSocietyUniversalFailurePaidSelfU8Splice.universalSearchFailure_externalPaymentSelfU8_strictAuthoritySeparation
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingCanonicalSocietyUniversalFailurePaidSelfU8Splice.canonicalSocietyUniversalFailurePaidSelfU8_directConsumer
