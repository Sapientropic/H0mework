import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.Preservation.Producer.SourceGeneratedCycleMaximalCanonicalPaidStep
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Payment.Novelty.PostSettlement.Representation.Incidence.SourceGeneratedContributionCapacityFinitePrefixResponsibilityDifference

/-! Responsibility-relevant novelty on the very same paid lifecycle edge.
The source and target are not chosen independently.  Caller Payment proofs
remain distinct values; their generated next has the original coherence. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.CanonicalSocietyProgress

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8Iteration
open M14SourceGeneratedPostSettlementObserverFinitePaidExitLifecycleStitch
open M14SourceGeneratedCycleMaximalCanonicalPaidStep
open M14SourceGeneratedContributionCapacityPostSettlementOccurrencePayment
open M14SourceGeneratedContributionCapacityPostSettlementCanonicalCurrent
open M14SourceGeneratedContributionCapacityPostSettlementCanonicalPaidStep
open M14SourceGeneratedContributionCapacityPostSettlementPaidReplay
open M14SourceGeneratedContributionCapacityFinitePrefixResponsibilityDifference
open M14SourceGeneratedContributionCapacityPostSettlementExternalLiability
open M14SourceGeneratedContributionCapacityEssentialAccessChannel
open M14UBIPeriodicActualServiceCapacity

variable {oldVisit : OldVisit} {sourceIndex boundary : Nat}
  (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat)

def sameEdgeNoveltyBoundary : Nat := cycleLifecycleIndex initial depth - 1

@[simp] theorem sameEdgeNoveltyBoundary_exact :
    sameEdgeNoveltyBoundary initial depth = boundary + depth + 1 := by
  unfold sameEdgeNoveltyBoundary
  rw [cycleLifecycleIndex_exact]
  omega

def sameEdgeResponsibilityDifference :
    SourceGeneratedFinitePrefixResponsibilityDifferenceAt oldVisit sourceIndex
      (sameEdgeNoveltyBoundary initial depth) :=
  sourceGeneratedFinitePrefixResponsibilityDifferenceAt oldVisit sourceIndex
    (sameEdgeNoveltyBoundary initial depth)

private theorem sameEdgeIndices :
    sameEdgeNoveltyBoundary initial depth + 1 = cycleLifecycleIndex initial depth ∧
    sameEdgeNoveltyBoundary initial depth + 2 = cycleLifecycleIndex initial depth + 1 := by
  rw [sameEdgeNoveltyBoundary_exact, cycleLifecycleIndex_exact]
  omega

theorem sameEdge_leftReplay_exact :
    (sameEdgeResponsibilityDifference initial depth).leftReplay =
      contributionCapacityPostSettlementPaidReplayAt oldVisit sourceIndex
        (cycleLifecycleIndex initial depth) := by
  change contributionCapacityPostSettlementPaidReplayAt oldVisit sourceIndex
    (sameEdgeNoveltyBoundary initial depth + 1) = _
  rw [(sameEdgeIndices initial depth).1]

theorem sameEdge_rightReplay_exact :
    (sameEdgeResponsibilityDifference initial depth).rightReplay =
      contributionCapacityPostSettlementPaidReplayAt oldVisit sourceIndex
        (cycleLifecycleIndex initial depth + 1) := by
  change contributionCapacityPostSettlementPaidReplayAt oldVisit sourceIndex
    (sameEdgeNoveltyBoundary initial depth + 2) = _
  rw [(sameEdgeIndices initial depth).2]

theorem sameEdge_authorityK_exact :
    (sameEdgeResponsibilityDifference initial depth).leftReplay.2.authorityK =
      periodicActualServiceExitOccurrenceAt
        (contributionCapacityPostSettlementCanonicalCurrentDepthAt oldVisit sourceIndex
          (cycleLifecycleIndex initial depth)) ∧
    (sameEdgeResponsibilityDifference initial depth).rightReplay.2.authorityK =
      periodicActualServiceExitOccurrenceAt
        (contributionCapacityPostSettlementCanonicalCurrentDepthAt oldVisit sourceIndex
          (cycleLifecycleIndex initial depth + 1)) := by
  rw [sameEdge_leftReplay_exact, sameEdge_rightReplay_exact]
  exact ⟨rfl, rfl⟩

variable (payment : CanonicalPostSettlementOccurrencePaymentAt oldVisit sourceIndex
  (cycleLifecycleIndex initial depth))

theorem sameEdge_rootEvents_align_paidStep :
    HEq (sameEdgeResponsibilityDifference initial depth).leftReplay.2.rootEvent
      (SourceGeneratedContributionCapacityPostSettlementCanonicalCurrentAt.rootEvent
        (sourceGeneratedCycleMaximalCanonicalPaidStepForPayment initial depth payment).consumedStep.2.sourceCurrent) ∧
    HEq (sameEdgeResponsibilityDifference initial depth).rightReplay.2.rootEvent
      (SourceGeneratedContributionCapacityPostSettlementCanonicalCurrentAt.rootEvent
        (sourceGeneratedCycleMaximalCanonicalPaidStepForPayment initial depth payment).consumedStep.2.targetCurrent) := by
  rw [sameEdge_leftReplay_exact, sameEdge_rightReplay_exact]
  exact ⟨HEq.rfl, HEq.rfl⟩

/-- Only canonical source and target Payments are identified here.  The
arbitrary caller Payment is retained by the following coherence theorem. -/
theorem sameEdge_canonicalPayments_align_paidStep :
    HEq (sameEdgeResponsibilityDifference initial depth).leftPayment
      (SourceGeneratedContributionCapacityPostSettlementCanonicalCurrentAt.payment
        (sourceGeneratedCycleMaximalCanonicalPaidStepForPayment initial depth payment).consumedStep.2.sourceCurrent) ∧
    HEq (sameEdgeResponsibilityDifference initial depth).rightPayment
      (sourceGeneratedCycleMaximalCanonicalPaidStepForPayment initial depth payment).consumedStep.2.targetPayment := by
  change HEq
      (sourceGeneratedContributionCapacityPostSettlementOccurrencePaymentAt oldVisit sourceIndex
        (sameEdgeNoveltyBoundary initial depth + 1))
      (sourceGeneratedContributionCapacityPostSettlementOccurrencePaymentAt oldVisit sourceIndex
        (cycleLifecycleIndex initial depth)) ∧
    HEq
      (sourceGeneratedContributionCapacityPostSettlementOccurrencePaymentAt oldVisit sourceIndex
        (sameEdgeNoveltyBoundary initial depth + 2))
      (sourceGeneratedContributionCapacityPostSettlementOccurrencePaymentAt oldVisit sourceIndex
        (cycleLifecycleIndex initial depth + 1))
  rw [(sameEdgeIndices initial depth).1, (sameEdgeIndices initial depth).2]
  exact ⟨HEq.rfl, HEq.rfl⟩

theorem sameEdge_callerPayment_nextPaidBy :
    (sourceGeneratedCycleMaximalCanonicalPaidStepForPayment initial depth payment).consumedStep.2.sourcePayment = payment ∧
    HEq payment.nextPaidBy
      (sameEdgeResponsibilityDifference initial depth).rightReplay.2.rootEvent.occurrence := by
  constructor
  · exact (sourceGeneratedCycleMaximalCanonicalPaidStepForPayment initial depth payment).sourcePaymentExact
  · rw [sameEdge_rightReplay_exact]
    exact (sourceGeneratedCycleMaximalCanonicalPaidStepForPayment initial depth payment).paidNextExact

theorem sameEdge_wholeLedger_is_original :
    HEq (sameEdgeResponsibilityDifference initial depth).leftReplay.2.rootEvent.wholeLedgerWriteBack
      (sourceGeneratedCycleMaximalCanonicalPaidStepForPayment initial depth payment).consumedStep.1.sourceWholeLedgerWriteBack := by
  rw [sameEdge_leftReplay_exact]
  exact HEq.rfl

theorem sameEdge_actualAuthorities_align_paidStep :
    HEq (sameEdgeResponsibilityDifference initial depth).leftReplay.2.authorityK.2.actualExit
      (SourceGeneratedContributionCapacityPostSettlementCanonicalCurrentAt.actualExit
        (sourceGeneratedCycleMaximalCanonicalPaidStepForPayment initial depth payment).consumedStep.2.sourceCurrent) ∧
    HEq (sameEdgeResponsibilityDifference initial depth).rightReplay.2.authorityK.2.actualExit
      (SourceGeneratedContributionCapacityPostSettlementCanonicalCurrentAt.actualExit
        (sourceGeneratedCycleMaximalCanonicalPaidStepForPayment initial depth payment).consumedStep.2.targetCurrent) := by
  rw [sameEdge_leftReplay_exact, sameEdge_rightReplay_exact]
  exact ⟨heq_of_eq (periodicActualServiceExitAt_eq_canonical _).symm,
    heq_of_eq (periodicActualServiceExitAt_eq_canonical _).symm⟩

theorem sameEdge_rightActualExit_is_target :
    HEq (sameEdgeResponsibilityDifference initial depth).rightActualExit
      (SourceGeneratedContributionCapacityPostSettlementCanonicalCurrentAt.actualExit
        (sourceGeneratedCycleMaximalCanonicalPaidStepForPayment initial depth payment).consumedStep.2.targetCurrent) := by
  change HEq (sameEdgeResponsibilityDifference initial depth).rightReplay.2.futureBirth.actualExit _
  rw [sameEdge_rightReplay_exact]
  exact HEq.rfl

/-- The new authority retains its independent M9 root consumer and exact
installed source entry; a bare authority difference cannot supply these. -/
theorem sameEdge_independentConsumer_and_originalEntry :
    let difference := sameEdgeResponsibilityDifference initial depth
    Nonempty ContributionCapacityPostSettlementPaymentSourceOwnership ∧
    Nonempty (ContributionCapacityPostSettlementPaymentRootConsumerForExitAt difference.rightActualExit) ∧
    difference.rightActualExit.paymentOccurrence.rootOccurrence = difference.rightExactRootEvent ∧
    difference.rightActualExit.paymentOccurrence.installed.payload.sourceEntry = RootInquiryU8CompletionRegression.entry := by
  let difference := sameEdgeResponsibilityDifference initial depth
  exact ⟨difference.sourceOwnedResidual, difference.rootConsumerIsInstalled,
    difference.rightPaymentRootOccurrence_exact, difference.rightPaymentSourceEntry_exact⟩

theorem sameEdge_channels_return_to_original_sources (channel : EssentialAccessChannel) :
    let difference := sameEdgeResponsibilityDifference initial depth
    ((difference.consumed).2.leftWitnessReturn channel).1.actor
        M14EssentialAccessRelationFixture.essentialAccessRelationCompiler = channelActor channel ∧
    M14EssentialAccessRelationFixture.essentialAccessRelationCompiler.relationOf
        ((difference.consumed).2.leftWitnessReturn channel).1 = channelRelation channel ∧
    ((difference.consumed).2.rightWitnessReturn channel).1.actor
        M14EssentialAccessRelationFixture.essentialAccessRelationCompiler = channelActor channel ∧
    M14EssentialAccessRelationFixture.essentialAccessRelationCompiler.relationOf
        ((difference.consumed).2.rightWitnessReturn channel).1 = channelRelation channel :=
  (sameEdgeResponsibilityDifference initial depth).channelWitnessesReturnToEachSource channel

theorem sameEdge_paidChannelPayments_exact (channel : EssentialAccessChannel) :
    let difference := sameEdgeResponsibilityDifference initial depth
    (difference.leftChannel channel).2.rootReadCarrier.existingPaymentOccurrence =
        difference.leftReplay.2.futureBirth.actualExit.paymentOccurrence ∧
    (difference.rightChannel channel).2.rootReadCarrier.existingPaymentOccurrence =
        difference.rightReplay.2.futureBirth.actualExit.paymentOccurrence :=
  (sameEdgeResponsibilityDifference initial depth).channelPaymentsReturnToEachActualExit channel

end

#print axioms sameEdgeResponsibilityDifference
#print axioms sameEdge_authorityK_exact
#print axioms sameEdge_rootEvents_align_paidStep
#print axioms sameEdge_canonicalPayments_align_paidStep
#print axioms sameEdge_callerPayment_nextPaidBy
#print axioms sameEdge_wholeLedger_is_original
#print axioms sameEdge_actualAuthorities_align_paidStep
#print axioms sameEdge_rightActualExit_is_target
#print axioms sameEdge_independentConsumer_and_originalEntry
#print axioms sameEdge_channels_return_to_original_sources

end SaturationMonoid.ProcessGame.Society.CanonicalSocietyProgress
