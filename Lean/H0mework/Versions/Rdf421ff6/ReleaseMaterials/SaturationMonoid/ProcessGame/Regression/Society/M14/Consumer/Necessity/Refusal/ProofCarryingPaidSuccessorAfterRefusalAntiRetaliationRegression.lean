import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Necessity.Refusal.NoGo.SourceGeneratedPaidSuccessorAfterRefusalRetypingNoGo
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Consumer.Necessity.Renewal.ProofCarryingPaidSuccessorBearerExerciseStandingRenewalRegression

/-!
# Direct consumer of paid-successor structural anti-retaliation

The audit consumes the target Payment's own response root read, both real
action traces, the installed/full-capture geometry split, every existing
target service channel, external responsibility and recursive next.  It also
consumes the administrative observer kernel and all exact retyping no-gos.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingPaidSuccessorAfterRefusalAntiRetaliationRegression

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open Lifecycle Universal Relations Power Exchange Settlement Price Money UBI
open Renewal Capacity Space CrossingCost Observer
open UBI.Capacity UBI.Capacity.SourceOwnedExitGeometryCompilerAt
open M3FiniteExchangeFixture M3ExchangeSettlementPriceRegression
open M14UBIExitCapacityFixture
open M14UBIProofCarryingRootRestriction
open M14UBIPeriodicActualServiceCapacity
open M14EssentialAccessRelationFixture
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityBirthBearerExit
open M14SourceGeneratedContributionCapacityBearerExerciseNoncaptureResponse
open M14SourceGeneratedContributionCapacityPostSettlementRenewalCompiler
open M14SourceGeneratedContributionCapacityPostSettlementRenewalRoot
open M14SourceGeneratedContributionCapacityPostSettlementExternalLiability
open M14SourceGeneratedContributionCapacityPostSettlementOccurrencePayment
open M14SourceGeneratedContributionCapacityEssentialAccessChannel
open M14ProofCarryingContributionCapacityPostSettlementChannelFamily
open M14SourceGeneratedPaidSuccessorBearerExerciseStandingRenewal
open M14ProofCarryingPaidSuccessorBearerExerciseStandingRenewalRegression
open M14SourceGeneratedPaidSuccessorAfterRefusalAntiRetaliation
open M14SourceGeneratedPaidSuccessorAfterRefusalRetypingNoGo

abbrev CanonicalPaidSuccessorAfterRefusalAntiRetaliationAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :=
  SourceGeneratedPaidSuccessorAfterRefusalAntiRetaliationAt oldVisit
    sourceIndex index

def canonicalPaidSuccessorAfterRefusalAntiRetaliationAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    CanonicalPaidSuccessorAfterRefusalAntiRetaliationAt oldVisit sourceIndex
      index :=
  sourceGeneratedPaidSuccessorAfterRefusalAntiRetaliationAt oldVisit
    sourceIndex index

structure PaidSuccessorAfterRefusalAntiRetaliationAuditAt
    {oldVisit : OldVisit} {sourceIndex index : Nat}
    (antiRetaliation :
      CanonicalPaidSuccessorAfterRefusalAntiRetaliationAt oldVisit sourceIndex
        index) : Prop where
  canonicalExact : antiRetaliation =
    canonicalPaidSuccessorAfterRefusalAntiRetaliationAt oldVisit sourceIndex
      index
  priorStandingRenewalAudit :
    PaidSuccessorBearerExerciseStandingRenewalAuditAt
      antiRetaliation.standingRenewal
  targetOwnResponse :
    antiRetaliation.targetResponseFace.projection =
          ContributionCapacityPostSettlementRenewalProjection.bearerExerciseResponse ∧
      antiRetaliation.targetResponseCarrier =
        Classical.choice antiRetaliation.targetResponseRootRead.down ∧
      antiRetaliation.targetResponseAction =
        antiRetaliation.targetResponseCarrier.exerciseActionValue ∧
      antiRetaliation.targetResponseAction =
        antiRetaliation.targetPayment.exerciseAction ∧
      ¬ birthBearerNoCapture.Captures
        antiRetaliation.targetResponseAction.1
  responseActionSourceTrace :
    ∃ state ∈ Lifecycle.actualEventGame.occurrence.trace,
      state = birthBearerExitExerciseController.actionState
          Lifecycle.actualEventGame.source ∧
        birthBearerExitExerciseController.actionAdmittedAt
          antiRetaliation.targetResponseAction.1
  realEmploymentLossAndTrace :
    antiRetaliation.targetResponseCarrier.employmentLoss =
          birthBearerEmploymentLoss ∧
      antiRetaliation.targetResponseCarrier.employmentLoss.power.action =
          birthBearerExactEmploymentAction ∧
      birthBearerEmploymentController.ControllerAt
        antiRetaliation.targetResponseCarrier.employmentLoss.power.action
          birthBearerEmployer ∧
      birthBearerEmployer ≠ birthBearerWorker ∧
      (∃ state ∈ Lifecycle.actualEventGame.occurrence.trace,
        state = birthBearerEmploymentController.actionState
            Lifecycle.actualEventGame.source ∧
          birthBearerEmploymentController.actionAdmittedAt
            antiRetaliation.targetResponseCarrier.employmentLoss.power.action.1)
  installedAndFullCaptureGeometry :
    (¬ birthBearerNoCapture.Captures
        antiRetaliation.targetResponseAction.1) ∧
      birthBearerFullCapture.Captures
        antiRetaliation.targetResponseAction.1 ∧
      (birthBearerGeometryCompilerAt
        antiRetaliation.standingRenewal.targetAuthorityCurrent
        ).actionableExitCapacity = 1 ∧
      (birthBearerCapturedGeometryCompilerAt
        antiRetaliation.standingRenewal.targetAuthorityCurrent
        ).actionableExitCapacity = 0
  everyTargetChannelServiceAndNext :
    ∀ channel : EssentialAccessChannel,
      let consumed := antiRetaliation.targetChannel channel
      Nonempty
          (ConsumedContributionCapacityPostSettlementChannelAt oldVisit
            sourceIndex (index + 1) channel) ∧
        consumed.1.actualExit = antiRetaliation.targetConsequence.actualExit ∧
        consumed.2.rootReadCarrier.existingPaymentOccurrence =
          consumed.1.actualExit.paymentOccurrence ∧
        consumed.2.rootReadCarrier.existingActualSettlement =
          consumed.1.actualExit.actualSettlement ∧
        consumed.1.actualExit.paymentOccurrence.installed.RootAnswerAndNextFactorizes ∧
        consumed.2.actualNext = antiRetaliation.targetPayment.nextPaidBy
  targetExternalConsumerSuccessorAndNext :
    Nonempty ContributionCapacityPostSettlementPaymentSourceOwnership ∧
      Nonempty
        (ContributionCapacityPostSettlementPaymentRootConsumerForExitAt
          antiRetaliation.targetConsequence.actualExit) ∧
      HEq antiRetaliation.targetConsequence.successor
        antiRetaliation.targetPayment.successor ∧
      antiRetaliation.targetPayment.nextPaidBy =
        contributionCapacityPostSettlementRenewalEmitted oldVisit sourceIndex
          (antiRetaliation.standingRenewal.targetAuthorityCurrent + 1)
  administrativeObserverNoGos :
    ∀ label : AdministrativeRetaliationOccurrenceAt oldVisit sourceIndex →
        Bool,
      (¬ Nonempty
        (AuthorityFactorization
          (administrativeRetaliationObserver oldVisit sourceIndex label))) ∧
      (¬ ∃ reconstruct : AdministrativeRetaliationVisible →
          AdministrativeRetaliationOccurrenceAt oldVisit sourceIndex,
        Function.LeftInverse reconstruct
          (administrativeRetaliationObserver oldVisit sourceIndex label
            ).forget) ∧
      (¬ Nonempty
        (FaithfulAuthorityReconstruction
          (administrativeRetaliationObserver oldVisit sourceIndex label)))
  protectedInterestNoChannelAuthority :
    ¬ Nonempty
      (AuthorityFactorization
        (M14SourceGeneratedContributionCapacityPostSettlementEssentialAccessChannelNoSection.contributionCapacityPostSettlementEssentialAccessChannelObserverAt
          oldVisit sourceIndex (index + 1)))
  installedCompilerNoncapture :
    ExactPaidSuccessorBearerExerciseNoncaptureAt antiRetaliation
      birthBearerNoCapture
  fullCaptureNoncaptureEmpty : IsEmpty
    (ExactPaidSuccessorBearerExerciseNoncaptureAt antiRetaliation
      birthBearerFullCapture)
  fullCaptureCountermodelNonempty : Nonempty
    (ExactPaidSuccessorFullCaptureRetaliationCountermodelAt oldVisit
      sourceIndex index)
  ownPolicyRecaptureEmpty : IsEmpty
    (ExactAfterRefusalOwnPolicyPriceRecaptureAt oldVisit sourceIndex index)
  everyServiceRecaptureEmpty : ∀ channel : EssentialAccessChannel,
    IsEmpty
      (ExactAfterRefusalServiceRecaptureAt oldVisit sourceIndex index channel)
  administrativeRecaptureEmpty : IsEmpty
    (ExactAfterRefusalAdministrativeRecaptureAt oldVisit sourceIndex index)
  employmentRetaliationRecaptureEmpty : IsEmpty
    (ExactAfterRefusalEmploymentRetaliationRecaptureAt oldVisit sourceIndex
      index)
  fullCaptureFalseReportEmpty : IsEmpty
    (ExactAfterRefusalFullCaptureReportedNonretaliatoryAt oldVisit sourceIndex
      index)
  countermodelCannotReconstructFalseReport : IsEmpty
    (ExactPaidSuccessorFullCaptureRetaliationCountermodelAt oldVisit
        sourceIndex index →
      ExactAfterRefusalFullCaptureReportedNonretaliatoryAt oldVisit sourceIndex
        index)

theorem paidSuccessorAfterRefusalAntiRetaliationAuditAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    PaidSuccessorAfterRefusalAntiRetaliationAuditAt
      (canonicalPaidSuccessorAfterRefusalAntiRetaliationAt oldVisit
        sourceIndex index) := by
  let antiRetaliation :=
    canonicalPaidSuccessorAfterRefusalAntiRetaliationAt oldVisit sourceIndex
      index
  have priorAudit :
      PaidSuccessorBearerExerciseStandingRenewalAuditAt
        antiRetaliation.standingRenewal := by
    exact paidSuccessorBearerExerciseStandingRenewalAuditAt oldVisit
      sourceIndex index
  have employment := antiRetaliation.realEmploymentLossAndControllerRemain
  exact
    { canonicalExact := rfl
      priorStandingRenewalAudit := priorAudit
      targetOwnResponse := antiRetaliation.targetOwnResponseIncidence
      responseActionSourceTrace :=
        antiRetaliation.targetResponseActionSourceTrace
      realEmploymentLossAndTrace :=
        ⟨employment.1, employment.2.1, employment.2.2.1,
          employment.2.2.2,
          antiRetaliation.realEmploymentActionSourceTrace⟩
      installedAndFullCaptureGeometry :=
        antiRetaliation.installedAndFullCaptureGeometry
      everyTargetChannelServiceAndNext :=
        antiRetaliation.targetChannelServiceAndNext
      targetExternalConsumerSuccessorAndNext :=
        antiRetaliation.targetExternalConsumerSuccessorAndNextRemain
      administrativeObserverNoGos := fun label =>
        ⟨administrativeRetaliation_noAuthorityFactorization antiRetaliation
            label,
          administrativeRetaliation_noOccurrenceLeftInverse antiRetaliation
            label,
          administrativeRetaliation_noFaithfulReconstruction antiRetaliation
            label⟩
      protectedInterestNoChannelAuthority :=
        SourceGeneratedPaidSuccessorAfterRefusalAntiRetaliationAt.targetProtectedInterest_noChannelAuthority
          (oldVisit := oldVisit) (sourceIndex := sourceIndex) (index := index)
      installedCompilerNoncapture :=
        exactPaidSuccessorBearerExerciseNoncaptureAt antiRetaliation
      fullCaptureNoncaptureEmpty :=
        fullCaptureNoncapture_isEmpty antiRetaliation
      fullCaptureCountermodelNonempty :=
        ⟨exactPaidSuccessorFullCaptureRetaliationCountermodelAt oldVisit
          sourceIndex index⟩
      ownPolicyRecaptureEmpty :=
        afterRefusalOwnPolicyPriceRecapture_isEmpty oldVisit sourceIndex index
      everyServiceRecaptureEmpty :=
        afterRefusalServiceRecapture_isEmpty oldVisit sourceIndex index
      administrativeRecaptureEmpty :=
        afterRefusalAdministrativeRecapture_isEmpty oldVisit sourceIndex index
      employmentRetaliationRecaptureEmpty :=
        afterRefusalEmploymentRetaliationRecapture_isEmpty oldVisit sourceIndex
          index
      fullCaptureFalseReportEmpty :=
        afterRefusalFullCaptureReportedNonretaliatory_isEmpty oldVisit
          sourceIndex index
      countermodelCannotReconstructFalseReport :=
        fullCaptureCountermodelCannotReconstructNonretaliatoryReplay oldVisit
          sourceIndex index }

structure ProofCarryingPaidSuccessorAfterRefusalAntiRetaliationCertificate :
    Prop where
  everyAntiRetaliation : ∀ oldVisit : OldVisit, ∀ sourceIndex index : Nat,
    Nonempty
      (CanonicalPaidSuccessorAfterRefusalAntiRetaliationAt oldVisit sourceIndex
        index)
  everyAudit : ∀ oldVisit : OldVisit, ∀ sourceIndex index : Nat,
    PaidSuccessorAfterRefusalAntiRetaliationAuditAt
      (canonicalPaidSuccessorAfterRefusalAntiRetaliationAt oldVisit
        sourceIndex index)
  everyFullCaptureCountermodel :
    ∀ oldVisit : OldVisit, ∀ sourceIndex index : Nat,
      Nonempty
        (ExactPaidSuccessorFullCaptureRetaliationCountermodelAt oldVisit
          sourceIndex index)
  everyFullCaptureFalseReportEmpty :
    ∀ oldVisit : OldVisit, ∀ sourceIndex index : Nat,
      IsEmpty
        (ExactAfterRefusalFullCaptureReportedNonretaliatoryAt oldVisit
          sourceIndex index)

theorem proofCarryingPaidSuccessorAfterRefusalAntiRetaliationDirectConsumer :
    ProofCarryingPaidSuccessorAfterRefusalAntiRetaliationCertificate where
  everyAntiRetaliation := fun oldVisit sourceIndex index =>
    ⟨canonicalPaidSuccessorAfterRefusalAntiRetaliationAt oldVisit sourceIndex
      index⟩
  everyAudit := paidSuccessorAfterRefusalAntiRetaliationAuditAt
  everyFullCaptureCountermodel := fun oldVisit sourceIndex index =>
    ⟨exactPaidSuccessorFullCaptureRetaliationCountermodelAt oldVisit sourceIndex
      index⟩
  everyFullCaptureFalseReportEmpty :=
    afterRefusalFullCaptureReportedNonretaliatory_isEmpty

end
end M14ProofCarryingPaidSuccessorAfterRefusalAntiRetaliationRegression
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingPaidSuccessorAfterRefusalAntiRetaliationRegression.paidSuccessorAfterRefusalAntiRetaliationAuditAt
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingPaidSuccessorAfterRefusalAntiRetaliationRegression.proofCarryingPaidSuccessorAfterRefusalAntiRetaliationDirectConsumer
