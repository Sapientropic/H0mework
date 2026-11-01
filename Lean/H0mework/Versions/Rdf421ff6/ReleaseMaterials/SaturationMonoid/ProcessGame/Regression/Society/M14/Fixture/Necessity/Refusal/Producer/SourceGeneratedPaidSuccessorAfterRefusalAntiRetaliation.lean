import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Necessity.Renewal.Producer.SourceGeneratedPaidSuccessorBearerExerciseStandingRenewal

/-!
# Paid-successor structural anti-retaliation

The paid successor now owns an action-indexed response face in the existing
post-settlement root.  Its target Payment reads that face beside its own
bearer-exercise face and every essential-access channel.  The exact `.leave`
action remains uncaptured and capacity one while a real employment-loss action
power remains present.  The existing full-price capture compiler supplies the
same-action, capacity-zero countermodel.

“After refusal” here means a response indexed by the exact bearer-exercise
authority.  It does not claim that leave has executed, that refusal caused a
retaliation event, or that exit is complete.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedPaidSuccessorAfterRefusalAntiRetaliation

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open Lifecycle Universal Relations Power Exchange Settlement Price Money UBI
open Renewal Capacity Space CrossingCost
open UBI.Capacity UBI.Capacity.SourceOwnedExitGeometryCompilerAt
open Settlement.SourceOwnedSettlementCompiler
open M3FiniteExchangeFixture M3ExchangeSettlementPriceRegression
open M10OccurrenceCapacityDebitedRunFixture
open M14UBIExitCapacityFixture
open M14UBIProofCarryingRootRestriction
open M14UBIPeriodicRootHistory
open M14UBIPeriodicActualServiceCapacity
open M14EssentialAccessRelationFixture
open M14EssentialAccessSectorRegression
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityBirthBearerExit
open M14SourceGeneratedContributionCapacityBearerExerciseNoncaptureResponse
open M14SourceGeneratedContributionCapacityJointSettlementWorld
open M14SourceGeneratedContributionCapacityJointSettlementConsumer
open M14SourceGeneratedContributionCapacityPostSettlementRenewalCompiler
open M14SourceGeneratedContributionCapacityPostSettlementRenewalRoot
open M14SourceGeneratedContributionCapacityPostSettlementExternalLiability
open M14SourceGeneratedContributionCapacityPostSettlementOccurrencePayment
open M14SourceGeneratedContributionCapacityEssentialAccessChannel
open M14SourceGeneratedContributionCapacityPostSettlementEssentialAccessChannel
open M14ProofCarryingContributionCapacityPostSettlementChannelFamily
open M14SourceGeneratedContributionCapacityPostSettlementCanonicalCurrent
open M14SourceGeneratedContributionCapacityPostSettlementCanonicalPaidStep
open M14SourceGeneratedPaidSuccessorBearerExerciseStandingRenewal

abbrev BirthBearerCaptureCompiler :=
  SourceOwnedPriceCaptureCompilerAt birthBearerExitRelationCompiler
    (OpenSettlementAt settlementCompiler openOccurrence)
    (exactOpenSettlement exactResidualActivation)

/-- Zero-payload cross-current certificate. -/
inductive SourceGeneratedPaidSuccessorAfterRefusalAntiRetaliationAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) : Type 28
  | private sealed

def sourceGeneratedPaidSuccessorAfterRefusalAntiRetaliationAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    SourceGeneratedPaidSuccessorAfterRefusalAntiRetaliationAt oldVisit
      sourceIndex index :=
  .sealed

namespace SourceGeneratedPaidSuccessorAfterRefusalAntiRetaliationAt

variable {oldVisit : OldVisit} {sourceIndex index : Nat}
  (antiRetaliation :
    SourceGeneratedPaidSuccessorAfterRefusalAntiRetaliationAt oldVisit
      sourceIndex index)

include antiRetaliation

theorem eq_sealed :
    antiRetaliation =
      sourceGeneratedPaidSuccessorAfterRefusalAntiRetaliationAt oldVisit
        sourceIndex index := by
  cases antiRetaliation
  rfl

def standingRenewal
    (_certificate :
      SourceGeneratedPaidSuccessorAfterRefusalAntiRetaliationAt oldVisit
        sourceIndex index) :
    SourceGeneratedPaidSuccessorBearerExerciseStandingRenewalAt oldVisit
      sourceIndex index :=
  sourceGeneratedPaidSuccessorBearerExerciseStandingRenewalAt oldVisit
    sourceIndex index

def sourcePayment
    (certificate :
      SourceGeneratedPaidSuccessorAfterRefusalAntiRetaliationAt oldVisit
        sourceIndex index) :=
  (standingRenewal certificate).sourcePayment

def targetConsequence
    (certificate :
      SourceGeneratedPaidSuccessorAfterRefusalAntiRetaliationAt oldVisit
        sourceIndex index) :=
  (standingRenewal certificate).targetConsequence

def targetPayment
    (certificate :
      SourceGeneratedPaidSuccessorAfterRefusalAntiRetaliationAt oldVisit
        sourceIndex index) :=
  (standingRenewal certificate).targetPayment

def targetResponseFace
    (certificate :
      SourceGeneratedPaidSuccessorAfterRefusalAntiRetaliationAt oldVisit
        sourceIndex index) :=
  (targetPayment certificate).responseFace

def targetResponseRootRead
    (certificate :
      SourceGeneratedPaidSuccessorAfterRefusalAntiRetaliationAt oldVisit
        sourceIndex index) :=
  (targetPayment certificate).responseRootRead

def targetResponseCarrier
    (certificate :
      SourceGeneratedPaidSuccessorAfterRefusalAntiRetaliationAt oldVisit
        sourceIndex index) :=
  (targetPayment certificate).responseCarrier

def targetResponseAction
    (certificate :
      SourceGeneratedPaidSuccessorAfterRefusalAntiRetaliationAt oldVisit
        sourceIndex index) :=
  (targetPayment certificate).responseAction

def targetChannel
    (certificate :
      SourceGeneratedPaidSuccessorAfterRefusalAntiRetaliationAt oldVisit
        sourceIndex index)
    (channel : EssentialAccessChannel) :=
  ((standingRenewal certificate).paidStep).targetChannel channel

def targetTenureChannel
    (certificate :
      SourceGeneratedPaidSuccessorAfterRefusalAntiRetaliationAt oldVisit
        sourceIndex index) :=
  targetChannel certificate tenureAuthority

def targetHealthChannel
    (certificate :
      SourceGeneratedPaidSuccessorAfterRefusalAntiRetaliationAt oldVisit
        sourceIndex index) :=
  targetChannel certificate healthAuthority

theorem sourcePaidNext_isTargetOuterOccurrence :
    HEq (sourcePayment antiRetaliation).nextPaidBy
      (targetConsequence antiRetaliation).outerRootEvent.occurrence :=
  (standingRenewal antiRetaliation).sourcePaidNext_isTargetOuterOccurrence

theorem sourceAndTargetOuterAuthorities_distinct :
    (standingRenewal antiRetaliation).sourceOuterAuthority ≠
      (standingRenewal antiRetaliation).targetOuterAuthority :=
  (standingRenewal antiRetaliation).sourceOuterAuthority_ne_target

theorem sourceAndTargetActualServiceK_distinct :
    (standingRenewal antiRetaliation).sourceActualServiceK ≠
      (standingRenewal antiRetaliation).targetActualServiceK :=
  (standingRenewal antiRetaliation).sourceActualServiceK_ne_target

/-- The target response is installed and read by the target Payment itself. -/
theorem targetOwnResponseIncidence :
    (targetResponseFace antiRetaliation).projection =
        ContributionCapacityPostSettlementRenewalProjection.bearerExerciseResponse ∧
      targetResponseCarrier antiRetaliation =
        Classical.choice (targetResponseRootRead antiRetaliation).down ∧
      targetResponseAction antiRetaliation =
        (targetResponseCarrier antiRetaliation).exerciseActionValue ∧
      targetResponseAction antiRetaliation =
        (targetPayment antiRetaliation).exerciseAction ∧
      ¬ birthBearerNoCapture.Captures
        (targetResponseAction antiRetaliation).1 := by
  have response :=
    (targetPayment antiRetaliation).bearerExerciseNoncaptureResponse_exact
  exact ⟨response.1, response.2.1, response.2.2.1,
    response.2.2.2.1, response.2.2.2.2.1⟩

theorem targetResponseAction_eq_canonical :
    targetResponseAction antiRetaliation =
      birthBearerExactExitExerciseAction := by
  exact (targetResponseCarrier antiRetaliation).exerciseActionExact

theorem targetResponseActionSourceTrace :
    ∃ state ∈ Lifecycle.actualEventGame.occurrence.trace,
      state = birthBearerExitExerciseController.actionState
          Lifecycle.actualEventGame.source ∧
        birthBearerExitExerciseController.actionAdmittedAt
          (targetResponseAction antiRetaliation).1 :=
  (targetResponseCarrier antiRetaliation).exerciseActionSourceTrace

theorem realEmploymentLossAndControllerRemain :
    (targetResponseCarrier antiRetaliation).employmentLoss =
        birthBearerEmploymentLoss ∧
      (targetResponseCarrier antiRetaliation).employmentLoss.power.action =
        birthBearerExactEmploymentAction ∧
      birthBearerEmploymentController.ControllerAt
        (targetResponseCarrier antiRetaliation).employmentLoss.power.action
          birthBearerEmployer ∧
      birthBearerEmployer ≠ birthBearerWorker :=
  (targetResponseCarrier antiRetaliation).realEmploymentLossRemains

theorem realEmploymentActionSourceTrace :
    ∃ state ∈ Lifecycle.actualEventGame.occurrence.trace,
      state = birthBearerEmploymentController.actionState
          Lifecycle.actualEventGame.source ∧
        birthBearerEmploymentController.actionAdmittedAt
          (targetResponseCarrier antiRetaliation).employmentLoss.power.action.1 :=
  (targetResponseCarrier antiRetaliation).employmentActionSourceTrace

/-- The exact action is uncaptured only under the installed noncapture
compiler.  The existing full-capture replacement captures that same action and
collapses its geometry. -/
theorem installedAndFullCaptureGeometry :
    (¬ birthBearerNoCapture.Captures
        (targetResponseAction antiRetaliation).1) ∧
      birthBearerFullCapture.Captures
        (targetResponseAction antiRetaliation).1 ∧
      (birthBearerGeometryCompilerAt
        (standingRenewal antiRetaliation).targetAuthorityCurrent
        ).actionableExitCapacity = 1 ∧
      (birthBearerCapturedGeometryCompilerAt
        (standingRenewal antiRetaliation).targetAuthorityCurrent
        ).actionableExitCapacity = 0 :=
  ⟨(targetPayment antiRetaliation).responseActionUncaptured,
    (targetPayment antiRetaliation).responseActionFullCaptured,
    (targetPayment antiRetaliation).responseExactCapacity,
    (targetPayment antiRetaliation).responseFullCapturedCapacity⟩

theorem targetChannelServiceAndNext
    (channel : EssentialAccessChannel) :
    let consumed := targetChannel antiRetaliation channel
    Nonempty
        (ConsumedContributionCapacityPostSettlementChannelAt oldVisit
          sourceIndex (index + 1) channel) ∧
      consumed.1.actualExit =
        (targetConsequence antiRetaliation).actualExit ∧
      consumed.2.rootReadCarrier.existingPaymentOccurrence =
        consumed.1.actualExit.paymentOccurrence ∧
      consumed.2.rootReadCarrier.existingActualSettlement =
        consumed.1.actualExit.actualSettlement ∧
      consumed.1.actualExit.paymentOccurrence.installed.RootAnswerAndNextFactorizes ∧
      consumed.2.actualNext =
        (targetPayment antiRetaliation).nextPaidBy := by
  let consumed := targetChannel antiRetaliation channel
  exact ⟨⟨consumed⟩, Subsingleton.elim _ _,
    consumed.2.paymentOccurrence_exact,
    consumed.2.actualSettlement_exact,
    consumed.2.rootFactorization,
    consumed.2.paymentNext_is_consumerNext.symm⟩

theorem everyTargetChannelServiceAndNext :
    ∀ channel : EssentialAccessChannel,
      let consumed := targetChannel antiRetaliation channel
      Nonempty
          (ConsumedContributionCapacityPostSettlementChannelAt oldVisit
            sourceIndex (index + 1) channel) ∧
        consumed.2.actualNext =
          (targetPayment antiRetaliation).nextPaidBy := by
  intro channel
  have channelSeal := targetChannelServiceAndNext antiRetaliation channel
  exact ⟨channelSeal.1, channelSeal.2.2.2.2.2⟩

theorem targetExternalConsumerSuccessorAndNextRemain :
    Nonempty ContributionCapacityPostSettlementPaymentSourceOwnership ∧
      Nonempty
        (ContributionCapacityPostSettlementPaymentRootConsumerForExitAt
          (targetConsequence antiRetaliation).actualExit) ∧
      HEq (targetConsequence antiRetaliation).successor
        (targetPayment antiRetaliation).successor ∧
      (targetPayment antiRetaliation).nextPaidBy =
        contributionCapacityPostSettlementRenewalEmitted oldVisit sourceIndex
          ((standingRenewal antiRetaliation).targetAuthorityCurrent + 1) :=
  ⟨(targetConsequence antiRetaliation).externalSourceOwnership,
    (targetConsequence antiRetaliation).externalRootConsumer,
    (targetConsequence antiRetaliation).successorFromPayment,
    (targetConsequence antiRetaliation).nextPaidByExact⟩

omit antiRetaliation in
theorem targetProtectedInterest_noChannelAuthority :
    ¬ Nonempty
      (Observer.AuthorityFactorization
        (M14SourceGeneratedContributionCapacityPostSettlementEssentialAccessChannelNoSection.contributionCapacityPostSettlementEssentialAccessChannelObserverAt
          oldVisit sourceIndex (index + 1))) :=
  SourceGeneratedContributionCapacityPostSettlementCanonicalCurrentAt.protectedInterest_noAuthorityFactorization
    (oldVisit := oldVisit) (sourceIndex := sourceIndex) (index := index + 1)

/-- Main structural anti-retaliation seal. -/
theorem paidSuccessorAfterRefusalAntiRetaliation_exact :
    HEq (sourcePayment antiRetaliation).nextPaidBy
        (targetConsequence antiRetaliation).outerRootEvent.occurrence ∧
      targetResponseAction antiRetaliation =
        (targetPayment antiRetaliation).exerciseAction ∧
      ¬ birthBearerNoCapture.Captures
        (targetResponseAction antiRetaliation).1 ∧
      (targetResponseCarrier antiRetaliation).employmentLoss =
        birthBearerEmploymentLoss ∧
      birthBearerEmployer ≠ birthBearerWorker ∧
      (standingRenewal antiRetaliation).sourceOuterAuthority ≠
        (standingRenewal antiRetaliation).targetOuterAuthority ∧
      (standingRenewal antiRetaliation).sourceActualServiceK ≠
        (standingRenewal antiRetaliation).targetActualServiceK ∧
      (birthBearerGeometryCompilerAt
        (standingRenewal antiRetaliation).targetAuthorityCurrent
        ).actionableExitCapacity = 1 ∧
      (birthBearerCapturedGeometryCompilerAt
        (standingRenewal antiRetaliation).targetAuthorityCurrent
        ).actionableExitCapacity = 0 ∧
      (∀ channel : EssentialAccessChannel,
        Nonempty
          (ConsumedContributionCapacityPostSettlementChannelAt oldVisit
            sourceIndex (index + 1) channel)) ∧
      Nonempty
        (ContributionCapacityPostSettlementPaymentRootConsumerForExitAt
          (targetConsequence antiRetaliation).actualExit) := by
  have response := targetOwnResponseIncidence antiRetaliation
  have employment := realEmploymentLossAndControllerRemain antiRetaliation
  have geometry := installedAndFullCaptureGeometry antiRetaliation
  have external := targetExternalConsumerSuccessorAndNextRemain antiRetaliation
  exact ⟨sourcePaidNext_isTargetOuterOccurrence antiRetaliation,
    response.2.2.2.1, response.2.2.2.2,
    employment.1, employment.2.2.2,
    sourceAndTargetOuterAuthorities_distinct antiRetaliation,
    sourceAndTargetActualServiceK_distinct antiRetaliation,
    geometry.2.2.1, geometry.2.2.2,
    fun channel => (targetChannelServiceAndNext antiRetaliation channel).1,
    external.2.1⟩

end SourceGeneratedPaidSuccessorAfterRefusalAntiRetaliationAt

/-! ## Compiler-indexed positive and full-capture countermodel -/

structure ExactPaidSuccessorBearerExerciseNoncaptureAt
    {oldVisit : OldVisit} {sourceIndex index : Nat}
    (antiRetaliation :
      SourceGeneratedPaidSuccessorAfterRefusalAntiRetaliationAt oldVisit
        sourceIndex index)
    (capture : BirthBearerCaptureCompiler) : Prop where
  actionUncaptured : ¬ capture.Captures
    antiRetaliation.targetResponseAction.1

theorem exactPaidSuccessorBearerExerciseNoncaptureAt
    {oldVisit : OldVisit} {sourceIndex index : Nat}
    (antiRetaliation :
      SourceGeneratedPaidSuccessorAfterRefusalAntiRetaliationAt oldVisit
        sourceIndex index) :
    ExactPaidSuccessorBearerExerciseNoncaptureAt antiRetaliation
      birthBearerNoCapture :=
  ⟨antiRetaliation.targetPayment.responseActionUncaptured⟩

theorem fullCaptureNoncapture_isEmpty
    {oldVisit : OldVisit} {sourceIndex index : Nat}
    (antiRetaliation :
      SourceGeneratedPaidSuccessorAfterRefusalAntiRetaliationAt oldVisit
        sourceIndex index) :
    IsEmpty
      (ExactPaidSuccessorBearerExerciseNoncaptureAt antiRetaliation
        birthBearerFullCapture) :=
  ⟨fun falseNoncapture =>
    falseNoncapture.actionUncaptured
      antiRetaliation.targetPayment.responseActionFullCaptured⟩

structure ExactPaidSuccessorFullCaptureRetaliationCountermodelAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) : Type 29 where
  private mk ::
  antiRetaliation :
    SourceGeneratedPaidSuccessorAfterRefusalAntiRetaliationAt oldVisit
      sourceIndex index
  sameActionCaptured : birthBearerFullCapture.Captures
    antiRetaliation.targetResponseAction.1
  installedCapacityOne :
    (birthBearerGeometryCompilerAt
      antiRetaliation.standingRenewal.targetAuthorityCurrent
      ).actionableExitCapacity = 1
  replacedCapacityZero :
    (birthBearerCapturedGeometryCompilerAt
      antiRetaliation.standingRenewal.targetAuthorityCurrent
      ).actionableExitCapacity = 0
  fullCaptureNoncaptureDeleted : IsEmpty
    (ExactPaidSuccessorBearerExerciseNoncaptureAt antiRetaliation
      birthBearerFullCapture)

def exactPaidSuccessorFullCaptureRetaliationCountermodelAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    ExactPaidSuccessorFullCaptureRetaliationCountermodelAt oldVisit sourceIndex
      index :=
  let antiRetaliation :=
    sourceGeneratedPaidSuccessorAfterRefusalAntiRetaliationAt oldVisit
      sourceIndex index
  { antiRetaliation := antiRetaliation
    sameActionCaptured :=
      antiRetaliation.targetPayment.responseActionFullCaptured
    installedCapacityOne :=
      antiRetaliation.targetPayment.responseExactCapacity
    replacedCapacityZero :=
      antiRetaliation.targetPayment.responseFullCapturedCapacity
    fullCaptureNoncaptureDeleted :=
      fullCaptureNoncapture_isEmpty antiRetaliation }

theorem paidSuccessorAfterRefusalAntiRetaliation_hasNoCallerPayload
    (oldVisit : OldVisit) (sourceIndex index : Nat) : True := by
  let antiRetaliation :=
    sourceGeneratedPaidSuccessorAfterRefusalAntiRetaliationAt oldVisit
      sourceIndex index
  fail_if_success exact antiRetaliation.payment
  fail_if_success exact antiRetaliation.action
  fail_if_success exact antiRetaliation.response
  fail_if_success exact antiRetaliation.capture
  fail_if_success exact antiRetaliation.target
  fail_if_success exact antiRetaliation.occurrence
  fail_if_success exact antiRetaliation.registry
  fail_if_success exact antiRetaliation.future
  trivial

end
end M14SourceGeneratedPaidSuccessorAfterRefusalAntiRetaliation
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPaidSuccessorAfterRefusalAntiRetaliation.sourceGeneratedPaidSuccessorAfterRefusalAntiRetaliationAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPaidSuccessorAfterRefusalAntiRetaliation.SourceGeneratedPaidSuccessorAfterRefusalAntiRetaliationAt.paidSuccessorAfterRefusalAntiRetaliation_exact
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPaidSuccessorAfterRefusalAntiRetaliation.fullCaptureNoncapture_isEmpty
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPaidSuccessorAfterRefusalAntiRetaliation.exactPaidSuccessorFullCaptureRetaliationCountermodelAt
