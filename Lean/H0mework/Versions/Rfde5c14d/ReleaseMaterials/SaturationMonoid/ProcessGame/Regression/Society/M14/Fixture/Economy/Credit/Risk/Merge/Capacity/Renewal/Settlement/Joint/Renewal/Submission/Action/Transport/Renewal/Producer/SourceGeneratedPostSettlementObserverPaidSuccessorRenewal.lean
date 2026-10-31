import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.NoGo.SourceGeneratedPostSettlementObserverFirstRowNoFreeEternity
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Necessity.Renewal.Producer.SourceGeneratedPaidSuccessorBearerExerciseStandingRenewal

/-!
# Fresh paid successor after the observer first row

The revised observer coordinate cannot install again after current zero.  Its
lawful continuation is therefore read from the exact paid replay already
retained by the authority-incidence morphism.  The replay's source index
selects the existing paid-successor renewal; no occurrence, Payment, action,
authority, K, consumer or next is accepted from the caller.

The source event and source Payment are proved to be the same endpoints as
the morphism span.  The target then generates its own Payment root read,
action authority, external consumer and next.  Action content may agree, but
outer authority and actual-service K cannot be replayed.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedPostSettlementObserverPaidSuccessorRenewal

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open Renewal UniversalRootGrammar
open M14UBIPeriodicRootHistory
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityBirthBearerExit
open M14SourceGeneratedContributionCapacityPostSettlementRenewalCompiler
open M14SourceGeneratedContributionCapacityPostSettlementExternalLiability
open M14SourceGeneratedContributionCapacityPostSettlementOccurrencePayment
open M14SourceGeneratedBearerActionPaidConsequenceIndependentNecessity
open M14SourceGeneratedPostSettlementObserverSubmissionU8
open M14SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislation
open M14SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislation.SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
open M14SourceGeneratedPostSettlementObserverAuthorityRevisedDispositionMorphism
open M14SourceGeneratedPostSettlementObserverAuthorityRevisedDispositionMorphism.SourceGeneratedPostSettlementObserverAuthorityRevisedDispositionMorphismAt
open M14SourceGeneratedPostSettlementObserverFirstRowNoFreeEternity
open M14SourceGeneratedPaidSuccessorBearerExerciseStandingRenewal
open M14SourceGeneratedPaidSuccessorBearerExerciseStandingRenewal.SourceGeneratedPaidSuccessorBearerExerciseStandingRenewalAt

variable {oldVisit : OldVisit} {sourceIndex boundary : Nat}
variable
  {span :
    SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
      oldVisit sourceIndex boundary}
  {authority :
    SourceNativeObserverConsumerRootedAuthorityAt (sourceSubmission span)}
  (morphism :
    SourceGeneratedPostSettlementObserverAuthorityRevisedDispositionMorphismAt
      span authority)

/-- Exact paid index already fixed by the span's right replay. -/
def paidIndexAt : Nat := by
  cases morphism
  exact (rightReplayAt oldVisit sourceIndex boundary).1

/-- Existing paid-successor producer selected by that exact replay index. -/
def paidRenewalAt :
    SourceGeneratedPaidSuccessorBearerExerciseStandingRenewalAt oldVisit
      sourceIndex (paidIndexAt morphism) :=
  sourceGeneratedPaidSuccessorBearerExerciseStandingRenewalAt oldVisit
    sourceIndex (paidIndexAt morphism)

/-- The paid renewal starts at the exact source event retained by the span. -/
theorem paidRenewal_sourceEvent_isSpanSourceEvent :
    (paidRenewalAt morphism).sourceConsequence.outerRootEvent =
      (sourceSubmission (legislationSpan morphism)).exactEvent := by
  cases morphism
  rfl

/-- Its source actual-exit Payment is the span's existing external Payment. -/
theorem paidRenewal_sourcePayment_isSpanTargetPayment :
    (paidRenewalAt morphism).sourceConsequence.actualExit.paymentOccurrence =
      targetPaymentOccurrence (legislationSpan morphism) := by
  cases morphism
  rfl

/-- No revised successor visit can re-install the observer first-row
coordinate. -/
theorem firstRowObserverRenewal_afterSuccessor_isEmpty
    (laterIndex : Nat) :
    IsEmpty
      (SourceInstalledRenewalAt
        (renewalRecognitionAt oldVisit sourceIndex boundary)
        (revisedTemporalVisitAt oldVisit sourceIndex boundary
          (laterIndex + 1))) :=
  observerSubmissionRenewal_afterFirst_isEmpty oldVisit sourceIndex boundary
    laterIndex

include morphism

/-- The already generated first successor is retained while the observer
coordinate itself cannot replay there. -/
theorem firstSuccessorAndNoObserverReplay (laterIndex : Nat) :
    HEq
        (activatedSubmissionAt oldVisit sourceIndex boundary).payload.successor
        (generatedFirstSuccessorAt oldVisit sourceIndex boundary) ∧
      IsEmpty
        (SourceInstalledRenewalAt
          (renewalRecognitionAt oldVisit sourceIndex boundary)
          (revisedTemporalVisitAt oldVisit sourceIndex boundary
            (laterIndex + 1))) :=
  ⟨installedDisposition_successor_isGeneratedFirstSuccessor morphism,
    firstRowObserverRenewal_afterSuccessor_isEmpty
      (oldVisit := oldVisit) (sourceIndex := sourceIndex)
      (boundary := boundary) laterIndex⟩

/-- Target Payment renewal generated inside the paid target occurrence. -/
def targetInstalledRenewal :=
  (paidRenewalAt morphism).targetConsequence.actualExit.paymentOccurrence
    |>.installed

theorem targetInstalledRenewal_exact :
    targetInstalledRenewal morphism =
      installedUBIAt (paidRenewalAt morphism).targetAuthorityCurrent :=
  (paidRenewalAt morphism).targetConsequence.externalLiability
    |>.paymentInstalledExact

theorem targetInstalledRenewal_rootFactorizes :
    (targetInstalledRenewal morphism).RootAnswerAndNextFactorizes :=
  (paidRenewalAt morphism).targetConsequence.externalLiability
    |>.rootFactorization

theorem targetInstalledRenewal_hasConsumer :
    Nonempty
      (ContributionCapacityPostSettlementPaymentRootConsumerForExitAt
        (paidRenewalAt morphism).targetConsequence.actualExit) :=
  (paidRenewalAt morphism).targetConsequence.externalLiability.rootConsumer

/-- Exact existing paid-renewal interface specialized to this morphism's
right-replay index. -/
abbrev PaidSuccessorRenewalExactAt : Prop :=
  let renewal := paidRenewalAt morphism
  HEq renewal.sourcePayment.nextPaidBy
        renewal.targetConsequence.outerRootEvent.occurrence ∧
    renewal.sourceConsequence.exerciseAction =
      renewal.targetConsequence.exerciseAction ∧
    renewal.sourceConsequence.exerciseAction =
      birthBearerExactExitExerciseAction ∧
    renewal.sourceAuthorityCurrent < renewal.targetAuthorityCurrent ∧
    renewal.sourceOuterAuthority ≠ renewal.targetOuterAuthority ∧
    renewal.sourceActualServiceK ≠ renewal.targetActualServiceK ∧
    Nonempty
      (PostSettlementPaymentBearerExerciseCarrierAt
        renewal.sourceConsequence.outerRootEvent) ∧
    Nonempty
      (PostSettlementPaymentBearerExerciseCarrierAt
        renewal.targetConsequence.outerRootEvent) ∧
    Nonempty ContributionCapacityPostSettlementPaymentSourceOwnership ∧
    Nonempty
      (ContributionCapacityPostSettlementPaymentRootConsumerForExitAt
        renewal.sourceConsequence.actualExit) ∧
    Nonempty
      (ContributionCapacityPostSettlementPaymentRootConsumerForExitAt
        renewal.targetConsequence.actualExit)

/-- Existing strongest positive: same action content, fresh outer authority,
fresh actual-service K, two own-root-read authorities and independent
external consumers. -/
theorem paidSuccessorRenewal_exact : PaidSuccessorRenewalExactAt morphism :=
  (paidRenewalAt morphism).paidSuccessorBearerExerciseStandingRenewal_exact

/-- Existing strongest negative against transporting the source outer
authority into the paid target. -/
theorem paidSuccessorUnrenewedReplay_isEmpty :
    IsEmpty
      (ExactPaidSuccessorBearerExerciseStandingUnrenewedReplayAt oldVisit
        sourceIndex (paidIndexAt morphism)) :=
  paidSuccessorBearerExerciseStandingUnrenewedReplay_isEmpty oldVisit
    sourceIndex (paidIndexAt morphism)

/-- The target action is generated from the target Payment's own root read. -/
theorem targetOwnRootReadAction :
    Nonempty
        (PostSettlementPaymentBearerExerciseCarrierAt
          (paidRenewalAt morphism).targetConsequence.outerRootEvent) ∧
      (paidRenewalAt morphism).targetConsequence.exerciseAction =
        birthBearerExactExitExerciseAction :=
  ⟨(paidRenewalAt morphism).targetRootReadAuthority_nonempty,
    (paidRenewalAt morphism).targetAction_eq_canonical⟩

/-- Exact continuing-target interface specialized to this morphism. -/
abbrev TargetPaidOccurrenceContinuesAt : Prop :=
  let renewal := paidRenewalAt morphism
  renewal.targetConsequence.nativeWrite = renewal.targetPayment.write ∧
    HEq renewal.targetConsequence.externalLiability
      renewal.targetPayment.liability ∧
    HEq renewal.targetConsequence.successor
      renewal.targetPayment.successor ∧
    renewal.targetPayment.nextPaidBy =
      contributionCapacityPostSettlementRenewalEmitted oldVisit sourceIndex
        (renewal.targetAuthorityCurrent + 1)

/-- The paid target remains an externally accountable continuing occurrence. -/
theorem targetPaidOccurrenceContinues :
    TargetPaidOccurrenceContinuesAt morphism :=
  (paidRenewalAt morphism).targetPaymentContinues

end
end M14SourceGeneratedPostSettlementObserverPaidSuccessorRenewal
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverPaidSuccessorRenewal.paidRenewal_sourceEvent_isSpanSourceEvent
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverPaidSuccessorRenewal.paidRenewal_sourcePayment_isSpanTargetPayment
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverPaidSuccessorRenewal.firstRowObserverRenewal_afterSuccessor_isEmpty
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverPaidSuccessorRenewal.targetInstalledRenewal_exact
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverPaidSuccessorRenewal.paidSuccessorRenewal_exact
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverPaidSuccessorRenewal.paidSuccessorUnrenewedReplay_isEmpty
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverPaidSuccessorRenewal.targetPaidOccurrenceContinues
