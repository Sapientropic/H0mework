import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Necessity.Consequence.Producer.SourceGeneratedBearerActionPaidConsequenceIndependentNecessity
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Payment.Preservation.PostSettlement.Step.Producer.SourceGeneratedContributionCapacityPostSettlementCanonicalPaidStep

/-!
# Paid-successor renewal of bearer exercise standing

The source Payment's own successor lands on the next exact outer occurrence.
That target occurrence regenerates its own `.birthBearerExit` root read and
therefore reauthorizes the same fixed `.leave` action content.  The action
value is deliberately unchanged; the outer authority occurrence and the
actual-service occurrence are both strictly new.

The public producer accepts only the existing root indices.  It accepts no
Payment, action, target, root read, occurrence, actual-service witness, future,
registry, or equality proof.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedPaidSuccessorBearerExerciseStandingRenewal

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open Lifecycle Universal Relations Power Exchange Settlement Price Money UBI
open Renewal Capacity Space CrossingCost
open UBI.Capacity UBI.Capacity.SourceOwnedExitGeometryCompilerAt
open M14UBIPeriodicActualServiceCapacity
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityBirthBearerExit
open M14SourceGeneratedContributionCapacityJointSettlementWorld
open M14SourceGeneratedContributionCapacityJointSettlementConsumer
open M14SourceGeneratedContributionCapacityPostSettlementRenewalCompiler
open M14SourceGeneratedContributionCapacityPostSettlementRenewalRoot
open M14SourceGeneratedContributionCapacityPostSettlementExternalLiability
open M14SourceGeneratedContributionCapacityPostSettlementOccurrencePayment
open M14SourceGeneratedContributionCapacityPostSettlementCanonicalCurrent
open M14SourceGeneratedContributionCapacityPostSettlementCanonicalPaidStep
open M14SourceGeneratedBearerActionPaidConsequenceIndependentNecessity

/-- Zero-payload certificate that one paid successor regenerates bearer-owned
exercise authority at its own outer occurrence. -/
inductive SourceGeneratedPaidSuccessorBearerExerciseStandingRenewalAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) : Type 27
  | private renewed

/-- Sole producer from the already generated post-root indices. -/
def sourceGeneratedPaidSuccessorBearerExerciseStandingRenewalAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    SourceGeneratedPaidSuccessorBearerExerciseStandingRenewalAt oldVisit
      sourceIndex index :=
  .renewed

namespace SourceGeneratedPaidSuccessorBearerExerciseStandingRenewalAt

variable {oldVisit : OldVisit} {sourceIndex index : Nat}
  (renewal : SourceGeneratedPaidSuccessorBearerExerciseStandingRenewalAt
    oldVisit sourceIndex index)

include renewal

theorem eq_renewed :
    renewal =
      sourceGeneratedPaidSuccessorBearerExerciseStandingRenewalAt oldVisit
        sourceIndex index := by
  cases renewal
  rfl

/-- Source action-bearing Payment incidence. -/
def sourceConsequence
    (_certificate : SourceGeneratedPaidSuccessorBearerExerciseStandingRenewalAt
      oldVisit sourceIndex index) :
    ExactBearerActionPaidConsequenceAt oldVisit sourceIndex index :=
  exactBearerActionPaidConsequenceAt oldVisit sourceIndex index

def sourcePayment
    (certificate : SourceGeneratedPaidSuccessorBearerExerciseStandingRenewalAt
      oldVisit sourceIndex index) :
    CanonicalPostSettlementOccurrencePaymentAt oldVisit
    sourceIndex index :=
  (sourceConsequence certificate).payment

/-- The source Payment generates this exact paid step. -/
def paidStep
    (certificate : SourceGeneratedPaidSuccessorBearerExerciseStandingRenewalAt
      oldVisit sourceIndex index) :
    SourceGeneratedContributionCapacityPostSettlementCanonicalPaidStepAt
      oldVisit sourceIndex index (sourcePayment certificate) :=
  sourceGeneratedContributionCapacityPostSettlementCanonicalPaidStepAt
    oldVisit sourceIndex index (sourcePayment certificate)

/-- Target incidence is regenerated from the next root occurrence, not stored
inside the source certificate. -/
def targetConsequence
    (_certificate : SourceGeneratedPaidSuccessorBearerExerciseStandingRenewalAt
      oldVisit sourceIndex index) :
    ExactBearerActionPaidConsequenceAt oldVisit sourceIndex (index + 1) :=
  exactBearerActionPaidConsequenceAt oldVisit sourceIndex (index + 1)

def targetPayment
    (certificate : SourceGeneratedPaidSuccessorBearerExerciseStandingRenewalAt
      oldVisit sourceIndex index) :
    CanonicalPostSettlementOccurrencePaymentAt oldVisit
    sourceIndex (index + 1) :=
  (targetConsequence certificate).payment

def sourceAuthorityCurrent
    (_certificate : SourceGeneratedPaidSuccessorBearerExerciseStandingRenewalAt
      oldVisit sourceIndex index) : Nat :=
  contributionCapacityPostSettlementReachableCurrentAt oldVisit sourceIndex
    index

def targetAuthorityCurrent
    (_certificate : SourceGeneratedPaidSuccessorBearerExerciseStandingRenewalAt
      oldVisit sourceIndex index) : Nat :=
  contributionCapacityPostSettlementReachableCurrentAt oldVisit sourceIndex
    (index + 1)

/-- Existing dependent package for the source outer occurrence. -/
def sourceOuterAuthority
    (certificate : SourceGeneratedPaidSuccessorBearerExerciseStandingRenewalAt
      oldVisit sourceIndex index) :
    AnyContributionCapacityPostSettlementRenewalOccurrenceAt oldVisit
      sourceIndex :=
  ⟨sourceAuthorityCurrent certificate,
    (sourceConsequence certificate).outerRootEvent.occurrence⟩

/-- Existing dependent package for the target outer occurrence. -/
def targetOuterAuthority
    (certificate : SourceGeneratedPaidSuccessorBearerExerciseStandingRenewalAt
      oldVisit sourceIndex index) :
    AnyContributionCapacityPostSettlementRenewalOccurrenceAt oldVisit
      sourceIndex :=
  ⟨targetAuthorityCurrent certificate,
    (targetConsequence certificate).outerRootEvent.occurrence⟩

/-- Existing actual-service occurrence identity at the source current. -/
def sourceActualServiceK
    (certificate : SourceGeneratedPaidSuccessorBearerExerciseStandingRenewalAt
      oldVisit sourceIndex index) : AnyPeriodicActualServiceExit :=
  contributionCapacityPostSettlementRenewalActualServiceOccurrenceAt oldVisit
    sourceIndex (sourceAuthorityCurrent certificate)

/-- Existing actual-service occurrence identity at the paid target current. -/
def targetActualServiceK
    (certificate : SourceGeneratedPaidSuccessorBearerExerciseStandingRenewalAt
      oldVisit sourceIndex index) : AnyPeriodicActualServiceExit :=
  contributionCapacityPostSettlementRenewalActualServiceOccurrenceAt oldVisit
    sourceIndex (targetAuthorityCurrent certificate)

theorem sourcePayment_exact :
    sourcePayment renewal =
      canonicalBearerActionPostPaymentAt oldVisit sourceIndex index :=
  (sourceConsequence renewal).paymentExact

theorem targetPayment_exact :
    targetPayment renewal =
      canonicalBearerActionPostPaymentAt oldVisit sourceIndex (index + 1) :=
  (targetConsequence renewal).paymentExact

/-- The target incidence and the paid step identify one canonical target
Payment; no second target Payment is introduced. -/
theorem targetPayment_isPaidStepTarget :
    targetPayment renewal = (paidStep renewal).targetPayment := by
  rfl

theorem sourcePayment_isPaidStepSource :
    sourcePayment renewal = (paidStep renewal).sourcePayment := by
  rfl

theorem targetRootEvent_isPaidStepTarget :
    (targetConsequence renewal).outerRootEvent =
      (paidStep renewal).targetRootEvent := by
  rfl

theorem sourceOuterAuthority_eq_canonical :
    sourceOuterAuthority renewal =
      contributionCapacityPostSettlementRenewalOccurrenceAt oldVisit
        sourceIndex (sourceAuthorityCurrent renewal) := by
  rfl

theorem targetOuterAuthority_eq_canonical :
    targetOuterAuthority renewal =
      contributionCapacityPostSettlementRenewalOccurrenceAt oldVisit
        sourceIndex (targetAuthorityCurrent renewal) := by
  rfl

/-- The paid successor advances the actual registered current by exactly one. -/
theorem targetAuthorityCurrent_eq_source_add_one :
    targetAuthorityCurrent renewal = sourceAuthorityCurrent renewal + 1 := by
  rw [show targetAuthorityCurrent renewal =
      contributionCapacityPostSettlementReachableCurrentAt oldVisit
        sourceIndex (index + 1) from rfl,
    show sourceAuthorityCurrent renewal =
      contributionCapacityPostSettlementReachableCurrentAt oldVisit
        sourceIndex index from rfl,
    contributionCapacityPostSettlementReachableCurrentAt_exact,
    contributionCapacityPostSettlementReachableCurrentAt_exact]
  omega

theorem sourceAuthorityCurrent_lt_target :
    sourceAuthorityCurrent renewal < targetAuthorityCurrent renewal := by
  rw [targetAuthorityCurrent_eq_source_add_one renewal]
  exact Nat.lt_succ_self _

/-- The two root-read authorities live at different outer occurrences even
though their local action values will agree. -/
theorem sourceOuterAuthority_ne_target :
    sourceOuterAuthority renewal ≠ targetOuterAuthority renewal := by
  intro equality
  have currentEquality := congrArg Sigma.fst equality
  exact Nat.ne_of_lt (sourceAuthorityCurrent_lt_target renewal)
    currentEquality

/-- The existing actual-service identity/K also changes at the paid
successor. -/
theorem sourceActualServiceK_ne_target :
    sourceActualServiceK renewal ≠ targetActualServiceK renewal := by
  intro equality
  have currentEquality :=
    contributionCapacityPostSettlementRenewalActualServiceOccurrenceAt_injective
      oldVisit sourceIndex equality
  exact Nat.ne_of_lt (sourceAuthorityCurrent_lt_target renewal)
    currentEquality

/-- Each K is aligned with the actual-exit authority selected by its own
Payment occurrence. -/
theorem sourceActualServiceK_actualExit_eq_payment :
    (sourceActualServiceK renewal).2.actualExit =
      (sourceConsequence renewal).actualExit := by
  exact Subsingleton.elim _ _

theorem targetActualServiceK_actualExit_eq_payment :
    (targetActualServiceK renewal).2.actualExit =
      (targetConsequence renewal).actualExit := by
  exact Subsingleton.elim _ _

theorem sourceAction_eq_canonical :
    (sourceConsequence renewal).exerciseAction =
      birthBearerExactExitExerciseAction := by
  calc
    (sourceConsequence renewal).exerciseAction =
        (sourceConsequence renewal).exerciseCarrier.exitExerciseAction :=
      (sourceConsequence renewal).exerciseActionFromCarrier
    _ = birthBearerExactExitExerciseAction :=
      (sourceConsequence renewal).exerciseCarrier.exitExerciseActionExact

theorem targetAction_eq_canonical :
    (targetConsequence renewal).exerciseAction =
      birthBearerExactExitExerciseAction := by
  calc
    (targetConsequence renewal).exerciseAction =
        (targetConsequence renewal).exerciseCarrier.exitExerciseAction :=
      (targetConsequence renewal).exerciseActionFromCarrier
    _ = birthBearerExactExitExerciseAction :=
      (targetConsequence renewal).exerciseCarrier.exitExerciseActionExact

/-- Content equality does not identify the two authority occurrences. -/
theorem sourceAction_eq_targetAction :
    (sourceConsequence renewal).exerciseAction =
      (targetConsequence renewal).exerciseAction :=
  (sourceAction_eq_canonical renewal).trans
    (targetAction_eq_canonical renewal).symm

/-- The source successor lands on the exact target outer occurrence. -/
theorem sourcePaidNext_isTargetOuterOccurrence :
    HEq (sourcePayment renewal).nextPaidBy
      (targetConsequence renewal).outerRootEvent.occurrence := by
  exact (paidStep renewal).nextPaidBy_isTargetCanonicalOccurrence

theorem sourceRootReadAuthority_nonempty :
    Nonempty
      (PostSettlementPaymentBearerExerciseCarrierAt
        (sourceConsequence renewal).outerRootEvent) :=
  (sourceConsequence renewal).exerciseRootRead.down

theorem targetRootReadAuthority_nonempty :
    Nonempty
      (PostSettlementPaymentBearerExerciseCarrierAt
        (targetConsequence renewal).outerRootEvent) :=
  (targetConsequence renewal).exerciseRootRead.down

/-- Both action authorities are reads of their own Payment occurrence.  The
target read is therefore a new incidence, not a transported source read. -/
theorem sourceAndTargetOwnRootReadIncidence :
    HEq (sourceConsequence renewal).exerciseRootRead
        (sourcePayment renewal).exerciseRootRead ∧
      HEq (targetConsequence renewal).exerciseRootRead
        (targetPayment renewal).exerciseRootRead ∧
      (sourceConsequence renewal).exerciseCarrier =
        Classical.choice (sourceConsequence renewal).exerciseRootRead.down ∧
      (targetConsequence renewal).exerciseCarrier =
        Classical.choice (targetConsequence renewal).exerciseRootRead.down ∧
      (sourceConsequence renewal).exerciseAction =
        (sourceConsequence renewal).exerciseCarrier.exitExerciseAction ∧
      (targetConsequence renewal).exerciseAction =
        (targetConsequence renewal).exerciseCarrier.exitExerciseAction :=
  ⟨(sourceConsequence renewal).exerciseRootReadFromPayment,
    (targetConsequence renewal).exerciseRootReadFromPayment,
    (sourceConsequence renewal).exerciseCarrierFromRootRead,
    (targetConsequence renewal).exerciseCarrierFromRootRead,
    (sourceConsequence renewal).exerciseActionFromCarrier,
    (targetConsequence renewal).exerciseActionFromCarrier⟩

theorem sourceAndTargetPaymentIncidence :
    (sourcePayment renewal).exerciseFace.projection =
          ContributionCapacityPostSettlementRenewalProjection.birthBearerExit ∧
      (targetPayment renewal).exerciseFace.projection =
          ContributionCapacityPostSettlementRenewalProjection.birthBearerExit ∧
      birthBearerExitExerciseController.ControllerAt
          (sourcePayment renewal).exerciseAction birthBearerWorker ∧
      birthBearerExitExerciseController.ControllerAt
          (targetPayment renewal).exerciseAction birthBearerWorker := by
  have sourcePaid := (sourcePayment renewal).bearerExercisePaidConsequence_exact
  have targetPaid := (targetPayment renewal).bearerExercisePaidConsequence_exact
  exact ⟨sourcePaid.1, targetPaid.1, sourcePaid.2.2.2.1,
    targetPaid.2.2.2.1⟩

theorem sourceAndTargetExternalConsumers :
    Nonempty ContributionCapacityPostSettlementPaymentSourceOwnership ∧
      Nonempty
        (ContributionCapacityPostSettlementPaymentRootConsumerForExitAt
          (sourceConsequence renewal).actualExit) ∧
      Nonempty
        (ContributionCapacityPostSettlementPaymentRootConsumerForExitAt
          (targetConsequence renewal).actualExit) :=
  ⟨(sourceConsequence renewal).externalSourceOwnership,
    (sourceConsequence renewal).externalRootConsumer,
    (targetConsequence renewal).externalRootConsumer⟩

theorem sourceAndTargetLocalLedgers_empty :
    IsEmpty
        (OpenResponsibilityAt (JointSettlementNAt oldVisit)
          (sourceConsequence renewal).outerRootEvent.occurrence.1) ∧
      IsEmpty
        (OpenResponsibilityAt (JointSettlementNAt oldVisit)
          (targetConsequence renewal).outerRootEvent.occurrence.1) :=
  ⟨(sourceConsequence renewal).localLedgerEmpty,
    (targetConsequence renewal).localLedgerEmpty⟩

/-- The renewed target is itself a paid, externally consumed, recursively
continuing occurrence rather than an endpoint shell. -/
theorem targetPaymentContinues :
    (targetConsequence renewal).nativeWrite =
        (targetPayment renewal).write ∧
      HEq (targetConsequence renewal).externalLiability
        (targetPayment renewal).liability ∧
      HEq (targetConsequence renewal).successor
        (targetPayment renewal).successor ∧
      (targetPayment renewal).nextPaidBy =
        contributionCapacityPostSettlementRenewalEmitted oldVisit sourceIndex
          (targetAuthorityCurrent renewal + 1) := by
  exact ⟨(targetConsequence renewal).nativeWriteFromPayment,
    (targetConsequence renewal).externalLiabilityFromPayment,
    (targetConsequence renewal).successorFromPayment,
    (targetConsequence renewal).nextPaidByExact⟩

/-- Main seal: one paid successor preserves action content while renewing both
outer authority identity and actual-service occurrence identity. -/
theorem paidSuccessorBearerExerciseStandingRenewal_exact :
    HEq (sourcePayment renewal).nextPaidBy
        (targetConsequence renewal).outerRootEvent.occurrence ∧
      (sourceConsequence renewal).exerciseAction =
        (targetConsequence renewal).exerciseAction ∧
      (sourceConsequence renewal).exerciseAction =
        birthBearerExactExitExerciseAction ∧
      sourceAuthorityCurrent renewal < targetAuthorityCurrent renewal ∧
      sourceOuterAuthority renewal ≠ targetOuterAuthority renewal ∧
      sourceActualServiceK renewal ≠ targetActualServiceK renewal ∧
      Nonempty
        (PostSettlementPaymentBearerExerciseCarrierAt
          (sourceConsequence renewal).outerRootEvent) ∧
      Nonempty
        (PostSettlementPaymentBearerExerciseCarrierAt
          (targetConsequence renewal).outerRootEvent) ∧
      Nonempty ContributionCapacityPostSettlementPaymentSourceOwnership ∧
      Nonempty
        (ContributionCapacityPostSettlementPaymentRootConsumerForExitAt
          (sourceConsequence renewal).actualExit) ∧
      Nonempty
        (ContributionCapacityPostSettlementPaymentRootConsumerForExitAt
          (targetConsequence renewal).actualExit) := by
  have consumers := sourceAndTargetExternalConsumers renewal
  exact ⟨sourcePaidNext_isTargetOuterOccurrence renewal,
    sourceAction_eq_targetAction renewal,
    sourceAction_eq_canonical renewal,
    sourceAuthorityCurrent_lt_target renewal,
    sourceOuterAuthority_ne_target renewal,
    sourceActualServiceK_ne_target renewal,
    sourceRootReadAuthority_nonempty renewal,
    targetRootReadAuthority_nonempty renewal,
    consumers.1, consumers.2.1, consumers.2.2⟩

end SourceGeneratedPaidSuccessorBearerExerciseStandingRenewalAt

/-! ## Exact false replay fibre -/

/-- Retains the complete positive paid-successor renewal and adds only the
claim that its source outer authority can be replayed as the target one. -/
structure ExactPaidSuccessorBearerExerciseStandingUnrenewedReplayAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) : Type 28 where
  private mk ::
  renewal : SourceGeneratedPaidSuccessorBearerExerciseStandingRenewalAt
    oldVisit sourceIndex index
  outerAuthorityReplayed :
    renewal.sourceOuterAuthority = renewal.targetOuterAuthority

theorem paidSuccessorBearerExerciseStandingUnrenewedReplay_isEmpty
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    IsEmpty
      (ExactPaidSuccessorBearerExerciseStandingUnrenewedReplayAt oldVisit
        sourceIndex index) :=
  ⟨fun replay =>
    replay.renewal.sourceOuterAuthority_ne_target
      replay.outerAuthorityReplayed⟩

theorem paidSuccessorBearerExerciseStandingRenewal_hasNoCallerPayload
    (oldVisit : OldVisit) (sourceIndex index : Nat) : True := by
  let renewal :=
    sourceGeneratedPaidSuccessorBearerExerciseStandingRenewalAt oldVisit
      sourceIndex index
  fail_if_success exact renewal.payment
  fail_if_success exact renewal.action
  fail_if_success exact renewal.target
  fail_if_success exact renewal.rootRead
  fail_if_success exact renewal.occurrence
  fail_if_success exact renewal.actualService
  fail_if_success exact renewal.future
  fail_if_success exact renewal.registry
  trivial

end
end M14SourceGeneratedPaidSuccessorBearerExerciseStandingRenewal
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPaidSuccessorBearerExerciseStandingRenewal.sourceGeneratedPaidSuccessorBearerExerciseStandingRenewalAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPaidSuccessorBearerExerciseStandingRenewal.SourceGeneratedPaidSuccessorBearerExerciseStandingRenewalAt.paidSuccessorBearerExerciseStandingRenewal_exact
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPaidSuccessorBearerExerciseStandingRenewal.paidSuccessorBearerExerciseStandingUnrenewedReplay_isEmpty
