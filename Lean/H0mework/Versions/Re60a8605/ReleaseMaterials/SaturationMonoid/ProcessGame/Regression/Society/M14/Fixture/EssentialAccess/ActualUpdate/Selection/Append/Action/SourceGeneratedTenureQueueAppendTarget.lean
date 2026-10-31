import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.Source.SourceGeneratedTenureQueueActionAtRevisedRoot
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.Root.SourceGeneratedEssentialAccessCriticalActionAppendRoot

/-!
# Tenure queue append target

The first named queue carrier consumes the revised root's exact depth-two
occurrence and generates one append root.  Source tether, historical UBI
purpose, inherited projection outcomes, selected tenure renewal and the first
whole-ledger successor remain in the action receipt.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedTenureQueueAppendTarget

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open Renewal
open M14EssentialAccessRelationFixture
open M14EssentialAccessPaymentPurposeLaw
open M14EssentialAccessPaymentPurposeFixture
open M14UBIProofCarryingRootRestriction
open M14SourceEssentialAccessCriticalRenewal
open M14SourceGeneratedEssentialAccessCriticalAction
open M14SourceGeneratedEssentialAccessCriticalTerminal
open M14SourceGeneratedSelectedEssentialAccessCriticalEvent
open M14SourceGeneratedCriticalEventSelectionRevisedLedger
open M14SourceGeneratedCriticalEventSelectionRevisedRoot
open M14SourceGeneratedCriticalEventSelectionRevisedInquiry
open M14SourceGeneratedCriticalEventSelectionRevisedContinuation
open M14SourceGeneratedTenureQueueActionAtRevisedRoot
open M14SourceGeneratedEssentialAccessCriticalActionAppendLedger
open M14SourceGeneratedEssentialAccessCriticalActionAppendSelection
open M14SourceGeneratedEssentialAccessCriticalActionAppendRoot

def tenureAppendSource := sourceGeneratedTenureQueueActionAtRevisedRoot

def tenureAppendPrior : EssentialAccessCriticalSelectionCurrent :=
  (revisedSelectionTemporalVisitAt 2).current

def tenureQueueAction := tenureAppendSource.queueAction

def tenureAppendTargetRoot :=
  appendLivingRoot revisedLivingRoot revisedDepthTwoEvent.occurrence
    tenureAppendPrior tenureQueueAction

def tenureAppendIdentityTranslation :
    TypedSemanticWorldNetworkTranslationAt NewN NewN where
  support :=
    { forward := id
      backward := id
      backward_forward := fun _ => rfl }
  anchor :=
    { forward := id
      backward := id
      backward_forward := fun _ => rfl }
  incidence :=
    { forward := id
      backward := id
      backward_forward := fun _ => rfl }
  lineage :=
    { forward := id
      backward := id
      backward_forward := fun _ => rfl }
  responsibility :=
    { forward := id
      backward := id
      backward_forward := fun _ => rfl }
  claim :=
    { forward := id
      backward := id
      backward_forward := fun _ => rfl }
  anchor_commutes := fun _ => rfl
  incidence_commutes := fun _ => rfl
  lineage_commutes := fun _ => rfl
  oldOpenLedger := fun _ =>
    { forward := id
      backward := id
      backward_forward := fun _ => rfl }
  oldOpenClaim_commutes := fun _ _ => rfl
  oldOpenProgressBudget_commutes := fun _ _ => rfl
  oldHoldsSurvives := fun _ _ proof => proof
  oldDispositionSurvives := fun _ _ proof => proof

def tenureAppendOccurrencePresentation : ConstructivePresentation
    (revisedAuthoritativeRoot.toRoot.actual.OccurrenceAt tenureAppendPrior)
    (tenureAppendTargetRoot.toAuthoritativeRoot.toRoot.actual.OccurrenceAt
      tenureAppendTargetRoot.toAuthoritativeRoot.toRoot.source.initial) :=
  ConstructivePresentation.refl _

theorem tenureAppendOccurrencePresentation_commutes
    (exactSource : ExactTemporalCausalRootEventAt
      revisedAuthoritativeRoot.toLedgerRoot
        (revisedSelectionTemporalVisitAt 2)) :
    tenureAppendOccurrencePresentation.forward exactSource.occurrence =
      tenureAppendTargetRoot.emitted
        tenureAppendTargetRoot.toAuthoritativeRoot.toRoot.source.initial := by
  rw [exactSource.eq_generated]
  rfl

def tenureAppendTargetInitialVisit : SourceNativeTemporalVisitAt
    tenureAppendTargetRoot.toAuthoritativeRoot.toLedgerRoot :=
  .finite tenureAppendTargetRoot.toAuthoritativeRoot.toRoot.initialVisit

def tenureAppendTargetInitialGenerated :=
  tenureAppendTargetRoot.toAuthoritativeRoot.toLedgerRoot
    |>.generatedAtTemporalVisit tenureAppendTargetInitialVisit

def tenureAppendTargetNewEntryRow :
    tenureAppendTargetInitialGenerated.GeneratedEntryRowAt newRevisedEntry :=
  (tenureAppendTargetInitialGenerated.canonicalGeneratedEntryRow?
    newRevisedEntry).get (by rfl)

def tenureAppendTargetFirstSuccessor : SourceNativeLedgerGeneratedSuccessorAt
    tenureAppendTargetInitialGenerated.occurrence
      tenureAppendTargetInitialGenerated.wholeLedgerWriteBack :=
  (SourceNativeLedgerGeneratedSuccessorAt.ofGenerated?
    tenureAppendTargetInitialGenerated.wholeLedgerWriteBack).get (by rfl)

@[simp] theorem tenureAppendTargetFirstSuccessor_current_exact :
    tenureAppendTargetFirstSuccessor.targetCurrent =
      appendedCriticalSelectionCurrent tenureAppendPrior tenureQueueAction := by
  change appendNativeTarget tenureAppendPrior tenureQueueAction
    tenureAppendPrior = _
  exact appendNativeTarget_initial tenureAppendPrior tenureQueueAction

def tenureAppendInstalledRenewal :=
  installedAppendedCriticalRenewal revisedLivingRoot
    revisedDepthTwoEvent.occurrence tenureAppendPrior tenureQueueAction

structure TenureQueueAppendReceiptProvenanceAt
    (exactSource : ExactTemporalCausalRootEventAt
      revisedAuthoritativeRoot.toLedgerRoot
        (revisedSelectionTemporalVisitAt 2)) : Prop where
  sourceCanonical : exactSource = revisedDepthTwoEvent
  sourceTether : tenureAppendSource =
    sourceGeneratedTenureQueueActionAtRevisedRoot
  priorFromSource : tenureAppendPrior =
    (revisedSelectionTemporalVisitAt 2).current
  queueTenure : tenureQueueAction.event = EssentialAccessEvent.tenure
  queueActionSeed : tenureQueueAction.action.criticalBearer.bearerLineage.seed =
    exactEssentialAccessSeed EssentialAccessEvent.tenure
  historicalUBI : tenureAppendSource.historicalUBIPayload =
    revisedDepthTwoInheritedUBIPayload
  historicalUBIFactorization :
    oldHealthTargetDepthOneInstalledUBI.RootAnswerAndNextFactorizes
  tenurePurpose :
    sourceGeneratedUBIDisposition.sourceFailure.paymentPurpose =
      exactTenurePaymentPurpose
  occurrenceCommutes : tenureAppendOccurrencePresentation.forward
      exactSource.occurrence = tenureAppendTargetRoot.emitted tenureAppendPrior
  targetAppendCurrent : tenureAppendTargetFirstSuccessor.targetCurrent =
    appendedCriticalSelectionCurrent tenureAppendPrior tenureQueueAction
  selectedEvent : tenureAppendInstalledRenewal.selected.selectedEvent =
    EssentialAccessEvent.tenure
  selectedAction : tenureAppendInstalledRenewal.payload.consumer.action =
    tenureQueueAction.action
  selectedUpdate : tenureAppendInstalledRenewal.payload.disposition.update =
    sourceGeneratedEssentialAccessCriticalActualUpdateAt .tenure
  inheritedOutcomes : ∀ projection :
      revisedLivingRoot.toAuthoritativeRoot.source.projectionLaw.Projection,
    HEq ((appendProjectionLaw revisedLivingRoot revisedDepthTwoEvent.occurrence
      tenureAppendPrior tenureQueueAction).outcomeAt (.inherited projection)
        (appendEmitted tenureAppendPrior tenureQueueAction tenureAppendPrior))
      (revisedLivingRoot.toAuthoritativeRoot.source.projectionLaw.outcomeAt
        projection revisedDepthTwoEvent.occurrence)
  firstWholeSuccessor : Nonempty (SourceNativeLedgerGeneratedSuccessorAt
    tenureAppendTargetInitialGenerated.occurrence
      tenureAppendTargetInitialGenerated.wholeLedgerWriteBack)

theorem tenureQueueAppendReceiptProvenanceAt
    (exactSource : ExactTemporalCausalRootEventAt
      revisedAuthoritativeRoot.toLedgerRoot
        (revisedSelectionTemporalVisitAt 2)) :
    TenureQueueAppendReceiptProvenanceAt exactSource := by
  have sourceCanonical := exactSource.eq_generated
  subst exactSource
  exact
    { sourceCanonical := rfl
      sourceTether := rfl
      priorFromSource := rfl
      queueTenure := rfl
      queueActionSeed := tenureAppendSource.actionSeedExact
      historicalUBI := tenureAppendSource.historicalUBIPayloadExact
      historicalUBIFactorization := tenureAppendSource.historicalUBIFactorization
      tenurePurpose := tenureAppendSource.tenurePurposeExact
      occurrenceCommutes := rfl
      targetAppendCurrent := tenureAppendTargetFirstSuccessor_current_exact
      selectedEvent := tenureAppendInstalledRenewal.selectedEventExact
      selectedAction := by
        rw [tenureAppendInstalledRenewal.payloadExact]
        exact (sourceEssentialAccessCriticalRenewalLaw_directConsumer
          tenureQueueAction.event
          (appendCriticalRenewalRootShell tenureAppendPrior tenureQueueAction)
          (appendEmitted tenureAppendPrior tenureQueueAction
            (appendedCriticalSelectionCurrent tenureAppendPrior
              tenureQueueAction)) ⟨rfl⟩).2.1 |>.trans
            tenureQueueAction.actionExact.symm
      selectedUpdate := rfl
      inheritedOutcomes := fun projection =>
        appendInheritedProjection_outcome_exact revisedLivingRoot
          revisedDepthTwoEvent.occurrence tenureAppendPrior tenureQueueAction
          projection (appendEmitted tenureAppendPrior tenureQueueAction
            tenureAppendPrior)
      firstWholeSuccessor := ⟨tenureAppendTargetFirstSuccessor⟩ }

def ExactTenureQueueAppendReceiptAt
    (exactSource : ExactTemporalCausalRootEventAt
      revisedAuthoritativeRoot.toLedgerRoot
        (revisedSelectionTemporalVisitAt 2)) (_answer : PUnit) : Type 3 :=
  ULift.{3, 0} (PLift (TenureQueueAppendReceiptProvenanceAt exactSource))

def exactTenureQueueAppendReceiptAt
    (exactSource : ExactTemporalCausalRootEventAt
      revisedAuthoritativeRoot.toLedgerRoot
        (revisedSelectionTemporalVisitAt 2)) (answer : PUnit) :
    ExactTenureQueueAppendReceiptAt exactSource answer :=
  ULift.up (PLift.up (tenureQueueAppendReceiptProvenanceAt exactSource))

def tenureQueueAppendTargetAt
    (exactSource : ExactTemporalCausalRootEventAt
      revisedAuthoritativeRoot.toLedgerRoot
        (revisedSelectionTemporalVisitAt 2)) :
    SourceNativeSequentialActualActionTargetAt revisedLivingRoot
      (revisedSelectionTemporalVisitAt 2) exactSource
      tenureAppendSource.sourceEntry tenureAppendSource.sourceAuthority := by
  rw [exactSource.eq_generated]
  exact
    { TargetN := NewN
      translation := tenureAppendIdentityTranslation
      TargetV := AppendVAt tenureAppendPrior tenureQueueAction
      targetRoot := tenureAppendTargetRoot
      targetTheory := revisedInquiryTheory
      lawSurface_heq := HEq.rfl
      targetTheory_rootSemantic :=
        { compile := id
          commuting := fun _ => rfl }
      occurrencePresentation := tenureAppendOccurrencePresentation
      occurrence_commutes := tenureAppendOccurrencePresentation_commutes
        revisedDepthTwoEvent
      initialSupport_heq := HEq.rfl
      initialOpenLedger := tenureAppendIdentityTranslation.oldOpenLedger
        minimalCoface.cofaceSupport
      initialOpenLedger_heq := HEq.rfl
      initialLedger_responsibility_commutes := fun _ => rfl
      initialLedger_claim_commutes := fun _ => rfl
      initialLedger_budget_conservative := fun _ => Nat.le_refl _
      initialLedgerNoFresh := fun targetEntry =>
        ⟨⟨targetEntry, PLift.up rfl⟩⟩
      translatedSourceEntryRow := tenureAppendTargetNewEntryRow
      firstSuccessor := tenureAppendTargetFirstSuccessor
      canonical_targetNextVisit_eq := rfl
      Answer := PUnit
      answer := PUnit.unit
      Receipt := ExactTenureQueueAppendReceiptAt revisedDepthTwoEvent
      receipt := exactTenureQueueAppendReceiptAt revisedDepthTwoEvent PUnit.unit }

end
end M14SourceGeneratedTenureQueueAppendTarget
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedTenureQueueAppendTarget.tenureQueueAppendReceiptProvenanceAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedTenureQueueAppendTarget.tenureQueueAppendTargetAt
