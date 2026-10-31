import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Celebration.Pulse.Producer.SourceGeneratedContributionCapacityPostSettlementFutureBirthPulse

/-!
# Direct consumer of canonical macro-history future birth

This certificate consumes the actual reopening-current-three birth, the
settlement action payment, the generated-residual receipt, both survivor-debt
receipts, the empty handoff, and every exact post-root payment/bearer-exit
event.  It also consumes the cross-settlement same-pulse/different-`K` and
different-next counterexample.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingContributionCapacityMacroFutureBirth

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open Lifecycle Universal Relations Power Exchange Settlement Price Money UBI
open UBI.Capacity
open Observer
open M3FiniteExchangeFixture
open M14UBIExitCapacityFixture
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityReopeningWorld
open M14SourceGeneratedContributionCapacityBirthBearerExit
open M14SourceGeneratedContributionCapacityNewCompatibleFutureBirth
open M14SourceGeneratedContributionCapacitySettlementCrossRootPayment
open M14SourceGeneratedContributionCapacitySettlementConsumer
open M14SourceGeneratedContributionCapacityJointSettlementWorld
open M14SourceGeneratedContributionCapacityJointSettlementConsumer
open M14SourceGeneratedContributionCapacityPostSettlementRenewalCompiler
open M14SourceGeneratedContributionCapacityPostSettlementRenewalRoot
open M14SourceGeneratedContributionCapacityPostSettlementExternalLiability
open M14SourceGeneratedContributionCapacityPostSettlementOccurrencePayment
open M14SourceGeneratedContributionCapacityPostSettlementFutureBirth
open M14SourceGeneratedContributionCapacityPostSettlementFutureBirthPulse
open M14SourceGeneratedContributionCapacityFutureBirthPulse
open M14UBIPeriodicActualServiceCapacity

structure CanonicalContributionCapacityMacroFutureBirthAuditAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) : Prop where
  futureBirth : Nonempty
    (SourceGeneratedContributionCapacityPostSettlementFutureBirthAt oldVisit
      sourceIndex index)
  currentExact :
    contributionCapacityPostSettlementFutureBirthCurrentAt oldVisit
        sourceIndex index =
      contributionCapacityPostSettlementRenewalInitialCurrentAt sourceIndex +
        index
  installedFace : Nonempty
    (SourceNativeRootSemanticFaceAt
      (ContributionCapacityPostSettlementRenewalRootAt oldVisit sourceIndex)
      (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
        index))
  installedBearerExitAuthority : Nonempty
    ((contributionCapacityPostSettlementFutureBirthBearerExitFaceAt oldVisit
      sourceIndex index).Restriction)
  actualExitFromNativeWrite :
    let birth :=
      sourceGeneratedContributionCapacityPostSettlementFutureBirthAt oldVisit
        sourceIndex index
    birth.actualExit = Classical.choice birth.postPayment.write.down
  bearerExitFromInstalledFace :
    let birth :=
      sourceGeneratedContributionCapacityPostSettlementFutureBirthAt oldVisit
        sourceIndex index
    birth.bearerExit =
      Classical.choice birth.installedBearerExitAuthority.down
  paymentExact :
    let birth :=
      sourceGeneratedContributionCapacityPostSettlementFutureBirthAt oldVisit
        sourceIndex index
    birth.bearerExit.existingPaymentOccurrence =
      birth.actualExit.paymentOccurrence
  serviceExact :
    let birth :=
      sourceGeneratedContributionCapacityPostSettlementFutureBirthAt oldVisit
        sourceIndex index
    birth.bearerExit.existingActualSettlement =
      birth.actualExit.actualSettlement
  sameBirthBearer :
    let birth :=
      sourceGeneratedContributionCapacityPostSettlementFutureBirthAt oldVisit
        sourceIndex index
    PurchasingPowerStandingAt.counterparty
        birthBearerExitCapacityProgram.purchasingPowerStanding =
        birthBearerWorker ∧
      exchangeLaw.bearerOfActor birthBearerWorker =
        birth.reopeningFutureBirth.birthAdmission.obligation.bearer
  refusalCapable :
    ExitFutureCode.work ∉
        birthBearerExitRelationCompiler.futureCodesAt
          birthBearerEmploymentRelation .target ∧
      birthBearerEmploymentRelation ≠
        birthBearerIndependentExitRelation ∧
      Nonempty (birthBearerExitRelationCompiler.FutureContinuationAt
        birthBearerIndependentExitRelation.1 .target ExitFutureCode.leave) ∧
      ¬ birthBearerExitRelationCompiler.futureIdle ExitFutureCode.leave ∧
      ¬ birthBearerNoCapture.Captures ExitFutureCode.leave ∧
      ExitFutureCode.leave ≠ ExitFutureCode.work
  capacityExact :
    (birthBearerGeometryCompilerAt
        (contributionCapacityPostSettlementFutureBirthCurrentAt oldVisit
          sourceIndex index)).actionableExitCapacity = 1 ∧
      (birthBearerCapturedGeometryCompilerAt
        (contributionCapacityPostSettlementFutureBirthCurrentAt oldVisit
          sourceIndex index)).actionableExitCapacity = 0
  localLedgerEmpty :
    let birth :=
      sourceGeneratedContributionCapacityPostSettlementFutureBirthAt oldVisit
        sourceIndex index
    IsEmpty
      (OpenResponsibilityAt (JointSettlementNAt oldVisit)
        birth.postRootEvent.occurrence.1)
  externalLiability :
    let birth :=
      sourceGeneratedContributionCapacityPostSettlementFutureBirthAt oldVisit
        sourceIndex index
    Nonempty ContributionCapacityPostSettlementPaymentSourceOwnership ∧
      Nonempty
        (ContributionCapacityPostSettlementPaymentRootConsumerForExitAt
          birth.actualExit)
  nextExact :
    let birth :=
      sourceGeneratedContributionCapacityPostSettlementFutureBirthAt oldVisit
        sourceIndex index
    birth.nextPaidOccurrence =
      contributionCapacityPostSettlementRenewalEmitted oldVisit sourceIndex
        (contributionCapacityPostSettlementFutureBirthCurrentAt oldVisit
            sourceIndex index +
          1)
  sourceBirthNotReplayed :
    periodicActualServiceExitOccurrenceAt
        (contributionCapacityFutureBirthDepth sourceIndex 2) ≠
      periodicActualServiceExitOccurrenceAt
        (contributionCapacityPostSettlementFutureBirthCurrentAt oldVisit
          sourceIndex index)

theorem canonicalContributionCapacityMacroFutureBirthAuditAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    CanonicalContributionCapacityMacroFutureBirthAuditAt oldVisit sourceIndex
      index := by
  let birth :=
    sourceGeneratedContributionCapacityPostSettlementFutureBirthAt oldVisit
      sourceIndex index
  exact
    { futureBirth := ⟨birth⟩
      currentExact :=
        SourceGeneratedContributionCapacityPostSettlementFutureBirthAt.current_exact
          (oldVisit := oldVisit) (sourceIndex := sourceIndex) (index := index)
      installedFace := ⟨birth.installedBearerExitFace⟩
      installedBearerExitAuthority :=
        ⟨birth.installedBearerExitAuthority⟩
      actualExitFromNativeWrite := birth.actualExitFromNativeWrite_exact
      bearerExitFromInstalledFace := birth.bearerExit_fromInstalledFace
      paymentExact := birth.bearerExitPayment_exact
      serviceExact := birth.bearerExitService_exact
      sameBirthBearer := birth.paymentWorkerBirthBearer_exact
      refusalCapable := birth.refusalCapable_nonWork_contract
      capacityExact := birth.exitCapacityOne_captureZero
      localLedgerEmpty := birth.localLedgerEmpty
      externalLiability := birth.externalLiabilityPresent
      nextExact := birth.nextPaidOccurrence_exact
      sourceBirthNotReplayed :=
        SourceGeneratedContributionCapacityPostSettlementFutureBirthAt.reopeningAndPostSettlementActualExitOccurrences_distinct
          (oldVisit := oldVisit) (sourceIndex := sourceIndex)
          (index := index) }

structure ProofCarryingContributionCapacityMacroFutureBirthAt
    (oldVisit : OldVisit) (sourceIndex : Nat) : Prop where
  reopeningCurrentThreeBirth : Nonempty
    (SourceGeneratedContributionCapacityNewCompatibleFutureBirthAt oldVisit
      sourceIndex 2)
  settlementActionPayment : Nonempty
    (CanonicalContributionCapacitySettlementCrossRootPaymentAt oldVisit
      sourceIndex)
  sourceBirthAndSettlementSamePayment :
    let bridge :=
      sourceGeneratedContributionCapacityPostSettlementFutureBirthAt oldVisit
        sourceIndex 0
    bridge.reopeningFutureBirth.runtimePayment =
      bridge.settlementCrossRootPayment.sourcePayment
  settlementMacroNextExact :
    let bridge :=
      sourceGeneratedContributionCapacityPostSettlementFutureBirthAt oldVisit
        sourceIndex 0
    bridge.settlementCrossRootPayment.nextPaidBy =
      ⟨(generatedContributionCapacitySettlementPaidActionAt oldVisit
          sourceIndex).target.TargetV,
        (generatedContributionCapacitySettlementPaidActionAt oldVisit
          sourceIndex).target.targetRoot.toAuthoritativeRoot,
        (generatedContributionCapacitySettlementPaidActionAt oldVisit
          sourceIndex).target.targetVisit⟩
  residualSettlement : Nonempty
    (SourceNativeRootDebtSettlementAt
      (settlementResidualCurrentAt oldVisit sourceIndex))
  carriedResidualIsSettledOrigin :
    let bridge :=
      sourceGeneratedContributionCapacityPostSettlementFutureBirthAt oldVisit
        sourceIndex 0
    bridge.reopeningFutureBirth.residualCarry.sourceEntry =
      (settlementResidualCurrentAt oldVisit sourceIndex).entry
  residualReceiptExact :
    generatedResidualTerminalReceiptAt oldVisit sourceIndex =
      (generatedResidualSettlementAt oldVisit sourceIndex).receipt
  survivorDebtSettlements : ∀ entryIndex : Fin 2,
    Nonempty
      (SourceNativeRootDebtSettlementAt
        (contributionCapacityJointSettlementDebtCurrentAt oldVisit sourceIndex
          entryIndex))
  jointSettlement :
    ProofCarryingContributionCapacityJointSettlementCertificateAt oldVisit
      sourceIndex
  postBirths : ∀ index : Nat,
    CanonicalContributionCapacityMacroFutureBirthAuditAt oldVisit sourceIndex
      index
  cofinalOnCanonicalMacroHistory : ∀ boundary : Nat,
    Nonempty
      (SourceGeneratedLaterContributionCapacityMacroFutureBirthAt oldVisit
        sourceIndex boundary)
  finitePulseExact : ∀ start horizon : Nat,
    sourceGeneratedContributionCapacityPostSettlementFutureBirthPulse
        oldVisit sourceIndex start horizon =
      horizon
  finiteFrontierNodup : ∀ start horizon : Nat,
    (sourceGeneratedFiniteContributionCapacityPostSettlementFutureBirthFrontier
      oldVisit sourceIndex start horizon).Nodup
  crossSettlementSamePulseDifferentK :
    let observer :=
      contributionCapacityCrossSettlementFutureBirthPulseObserver oldVisit
        sourceIndex
    observer.forget
        (contributionCapacityBeforeSettlementFutureBirth oldVisit sourceIndex) =
      observer.forget
        (contributionCapacityAfterSettlementFutureBirth oldVisit sourceIndex) ∧
    observer.authorityK
        (contributionCapacityBeforeSettlementFutureBirth oldVisit sourceIndex) ≠
      observer.authorityK
        (contributionCapacityAfterSettlementFutureBirth oldVisit sourceIndex)
  crossSettlementNoOccurrenceReconstruction :
    ¬ ∃ reconstruct : ContributionCapacityFutureBirthPulse →
        CrossSettlementContributionCapacityFutureBirth oldVisit sourceIndex,
      Function.LeftInverse reconstruct
        (contributionCapacityCrossSettlementFutureBirthPulseObserver oldVisit
          sourceIndex).forget
  crossSettlementNoAuthorityFactorization :
    ¬ Nonempty
      (AuthorityFactorization
        (contributionCapacityCrossSettlementFutureBirthPulseObserver oldVisit
          sourceIndex))
  crossSettlementNoFaithfulReconstruction :
    ¬ Nonempty
      (FaithfulAuthorityReconstruction
        (contributionCapacityCrossSettlementFutureBirthPulseObserver oldVisit
          sourceIndex))
  settlementActionActualMacroNextExact :
    (contributionCapacitySettlementActionActualMacroNextAt oldVisit
      sourceIndex).2 =
      (sourceGeneratedContributionCapacityPostSettlementFutureBirthAt oldVisit
        sourceIndex 0).settlementCrossRootPayment.nextPaidBy
  postPaymentActualMacroNextOccurrenceExact :
    (sourceGeneratedContributionCapacityPostSettlementFutureBirthAt oldVisit
        sourceIndex 0).nextPaidOccurrence =
      contributionCapacityPostSettlementRenewalEmitted oldVisit sourceIndex
        (show Nat from
          (contributionCapacityPostSettlementRenewalVisitAt oldVisit
            sourceIndex 1).current)
  actualMacroNextsDistinct :
    contributionCapacitySettlementActionActualMacroNextAt oldVisit
        sourceIndex ≠
      contributionCapacityPostSettlementPaymentActualMacroNextAt oldVisit
        sourceIndex
  crossSettlementNoNextFactorization :
    ¬ Nonempty
      (AuthorityFactorization
        (contributionCapacityCrossSettlementFutureBirthNextPulseObserver
          oldVisit sourceIndex))

theorem proofCarryingContributionCapacityMacroFutureBirthAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    ProofCarryingContributionCapacityMacroFutureBirthAt oldVisit
      sourceIndex := by
  exact
    { reopeningCurrentThreeBirth :=
        ⟨sourceGeneratedContributionCapacityNewCompatibleFutureBirthAt
          oldVisit sourceIndex 2⟩
      settlementActionPayment :=
        ⟨sourceGeneratedContributionCapacitySettlementCrossRootPaymentAt
          oldVisit sourceIndex⟩
      sourceBirthAndSettlementSamePayment :=
        (sourceGeneratedContributionCapacityPostSettlementFutureBirthAt
          oldVisit sourceIndex 0
          ).reopeningBirthPayment_eq_settlementActionSource
      settlementMacroNextExact :=
        (sourceGeneratedContributionCapacityPostSettlementFutureBirthAt
          oldVisit sourceIndex 0).settlementActionMacroNext_exact
      residualSettlement :=
        ⟨generatedResidualSettlementAt oldVisit sourceIndex⟩
      carriedResidualIsSettledOrigin :=
        (sourceGeneratedContributionCapacityPostSettlementFutureBirthAt
          oldVisit sourceIndex 0).carriedResidual_eq_settlementOrigin
      residualReceiptExact := rfl
      survivorDebtSettlements := fun entryIndex =>
        ⟨generatedContributionCapacityJointDebtSettlementAt oldVisit
          sourceIndex entryIndex⟩
      jointSettlement :=
        generatedContributionCapacityJointSettlement_closesBoth_renewsSociety
          oldVisit sourceIndex
      postBirths :=
        canonicalContributionCapacityMacroFutureBirthAuditAt oldVisit
          sourceIndex
      cofinalOnCanonicalMacroHistory :=
        sourceGeneratedContributionCapacityFutureBirth_cofinalOnCanonicalMacroHistory
          oldVisit sourceIndex
      finitePulseExact :=
        contributionCapacityPostSettlementFutureBirthPulse_eq_horizon oldVisit
          sourceIndex
      finiteFrontierNodup :=
        contributionCapacityPostSettlementFutureBirthFrontier_nodup oldVisit
          sourceIndex
      crossSettlementSamePulseDifferentK :=
        contributionCapacityCrossSettlement_samePulse_differentK oldVisit
          sourceIndex
      crossSettlementNoOccurrenceReconstruction :=
        contributionCapacityCrossSettlementPulse_noOccurrenceReconstruction
          oldVisit sourceIndex
      crossSettlementNoAuthorityFactorization :=
        contributionCapacityCrossSettlementPulse_noAuthorityFactorization
          oldVisit sourceIndex
      crossSettlementNoFaithfulReconstruction :=
        contributionCapacityCrossSettlementPulse_noFaithfulReconstruction
          oldVisit sourceIndex
      settlementActionActualMacroNextExact :=
        contributionCapacitySettlementActionActualMacroNext_exact oldVisit
          sourceIndex
      postPaymentActualMacroNextOccurrenceExact :=
        contributionCapacityPostSettlementPaymentActualMacroNextOccurrence_exact
          oldVisit sourceIndex
      actualMacroNextsDistinct :=
        contributionCapacityActualMacroNexts_distinct oldVisit sourceIndex
      crossSettlementNoNextFactorization :=
        contributionCapacityCrossSettlementPulse_noNextFactorization oldVisit
          sourceIndex }

theorem bareReceipt_payment_liability_orPulse_cannot_retype_asMacroFutureBirth
    (oldVisit : OldVisit) (sourceIndex index : Nat) : True := by
  let receipt := generatedResidualTerminalReceiptAt oldVisit sourceIndex
  let payment :=
    sourceGeneratedContributionCapacityPostSettlementOccurrencePaymentAt
      oldVisit sourceIndex index
  let liability := payment.liability
  let pulse := sourceGeneratedContributionCapacityPostSettlementFutureBirthPulse
    oldVisit sourceIndex index 1
  fail_if_success exact
    (receipt :
      SourceGeneratedContributionCapacityPostSettlementFutureBirthAt oldVisit
        sourceIndex index)
  fail_if_success exact
    (payment :
      SourceGeneratedContributionCapacityPostSettlementFutureBirthAt oldVisit
        sourceIndex index)
  fail_if_success exact
    (liability :
      SourceGeneratedContributionCapacityPostSettlementFutureBirthAt oldVisit
        sourceIndex index)
  fail_if_success exact
    (pulse :
      SourceGeneratedContributionCapacityPostSettlementFutureBirthAt oldVisit
        sourceIndex index)
  trivial

end
end M14ProofCarryingContributionCapacityMacroFutureBirth
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingContributionCapacityMacroFutureBirth.canonicalContributionCapacityMacroFutureBirthAuditAt
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingContributionCapacityMacroFutureBirth.proofCarryingContributionCapacityMacroFutureBirthAt
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingContributionCapacityMacroFutureBirth.bareReceipt_payment_liability_orPulse_cannot_retype_asMacroFutureBirth
