import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Root.Economy.Normalization.PeriodicDeathRepairNormalization

/-!
# M14 direct consumer for periodic death-repair normalization

This consumer verifies the whole diamond rather than merely re-exporting its
target.  The maintenance and capture deaths share the old root occurrence;
their distinct installed actions write through the same ledger and converge
to the same ordinary next.  Both receipts remain necessary, and the ordinary
normal form stays strictly separate from the existing fixed self-U8 landing.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingPeriodicDeathRepairNormalizationRegression

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Renewal UBI Capacity Space CrossingCost
open ConstructiveRoot.RootInquiryCompletion
open M9ProofCarryingRenewalInquiryRoot
open M14UBIExitCapacityFixture
open M14UBIProofCarryingRootRestriction
open M14UBIPeriodicRootHistory
open M14UBIPeriodicActualServiceCapacity
open M14EssentialAccessRelationFixture
open M14EssentialAccessSectorRegression
open M14SourceEssentialServiceRestoration
open M14ActionableFuturePortfolio
open M14GeneratedEconomicDisposition
open M14TenureCaptureRouteRepairNoGoRegression
open M14ProofCarryingExitRepairRegression
open M14ProofCarryingExitRepairRenewalRegression
open M14PortfolioMaintenanceDeath
open M14PortfolioCaptureDeath
open M14PeriodicEssentialServiceRestoration
open M14PeriodicDeathRepairNormalization
open M14UBISelfU8SameRootRegression

theorem normalization_occurrence_rows_and_ledger_commute (depth : Nat) :
    let step := sourceGeneratedPeriodicDeathRepairNormalizationAt depth
    step.service.sourceDeath.stable.paymentOccurrence.rootOccurrence =
        step.service.rootOccurrence ∧
      step.captureDeath.fullServices.paymentOccurrence.rootOccurrence =
        step.service.rootOccurrence ∧
      step.captureDeath.ordinaryRepair.depth = depth ∧
      HEq step.captureDeath.ordinaryRepair.renewal.rootOccurrence
        (jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
          (temporalVisitAt depth)) ∧
      jointEssentialServiceRestorationProjection ≠ jointUBIProjection ∧
      step.service.installed.payload.sourceEntry =
        RootInquiryU8CompletionRegression.entry ∧
      step.captureDeath.ordinaryRepair.renewal.source.installed.payload.sourceEntry =
        RootInquiryU8CompletionRegression.entry ∧
      HEq step.service.installed.payload.selectedRow
        (installedUBIAt depth).payload.selectedRow ∧
      HEq step.captureDeath.ordinaryRepair.renewal.source.installed.payload.selectedRow
        (installedUBIAt depth).payload.selectedRow ∧
      step.service.applied.selectedWrite.sourceRow.CommutesWithWorld ∧
      step.captureDeath.ordinaryRepair.renewal.ordinarySelectedWrite.sourceRow.CommutesWithWorld ∧
      step.service.applied.wholeLedgerWriteBack =
        step.captureDeath.ordinaryRepair.renewal.wholeLedgerWriteBack ∧
      step.service.installed.RootAnswerAndNextFactorizes ∧
      step.captureDeath.ordinaryRepair.renewal.source.installed.RootAnswerAndNextFactorizes := by
  let step := sourceGeneratedPeriodicDeathRepairNormalizationAt depth
  exact ⟨step.maintenanceRootExact, step.captureRootExact,
    step.normalForm.captureDepthExact,
    step.normalForm.captureRootOccurrenceExact,
    step.normalForm.coordinatesDistinct,
    step.normalForm.serviceEntryExact,
    step.normalForm.captureEntryExact,
    step.normalForm.serviceRowSharedWithUBI,
    step.normalForm.captureRowSharedWithUBI,
    step.normalForm.serviceSelectedWriteCommutes,
    step.normalForm.captureSelectedWriteCommutes,
    step.normalForm.wholeLedgerShared,
    step.normalForm.serviceRootFactorization,
    step.normalForm.captureRootFactorization⟩

theorem both_actual_paths_factor_through_one_normal_form (depth : Nat) :
    let step := sourceGeneratedPeriodicDeathRepairNormalizationAt depth
    Nonempty (SourceGeneratedOrdinaryEconomicNormalFormAt depth
      step.service step.captureDeath.ordinaryRepair
        step.service.applied.generatedNext) ∧
      step.normalForm.generatedNext = step.service.applied.generatedNext ∧
      step.normalForm.generatedNext =
        step.captureDeath.ordinaryRepair.renewal.generatedNext ∧
      step.normalForm.generatedNext =
        jointRoot.generatedNextCurrentAt (temporalVisitAt depth) ∧
      ordinaryEconomicLandingAt depth = some
        (⟨M9ProofCarryingRenewalInquiryRoot.N,
          step.normalForm.generatedNext⟩ :
          AnyAuthoritativeRootCurrent) := by
  let step := sourceGeneratedPeriodicDeathRepairNormalizationAt depth
  exact ⟨⟨step.normalForm⟩,
    step.normalForm.nextIsService,
    step.normalForm.nextIsCapture,
    step.normalForm.nextIsRoot,
    step.normalForm.ordinaryLandingExact⟩

theorem normalized_target_is_simultaneously_viable (depth : Nat) :
    let step := sourceGeneratedPeriodicDeathRepairNormalizationAt depth
    Nonempty (SourceGeneratedActionableFuturePortfolioAt (depth + 1)) ∧
      step.normalForm.targetPortfolio.paymentOccurrence.rootOccurrence =
        jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
          (temporalVisitAt (depth + 1)) ∧
      HEq step.normalForm.generatedNext.visit
        (temporalVisitAt (depth + 1)) ∧
      Nonempty (SourceGeneratedEssentialDomainActionableAt
        (depth + 1) tenureAuthority) ∧
      Nonempty (SourceGeneratedEssentialDomainActionableAt
        (depth + 1) healthAuthority) ∧
      (anomiePhaseAt (depth + 1)).served.get
          step.normalForm.targetHealth.serviceIncidence.slot =
        SourceAppliedEssentialServiceRestorationAt.unitAt
          step.service.installed.payload.disposition ∧
      SourceAppliedTenureCaptureRepairAt.targetProgramAt
          step.captureDeath.ordinaryRepair.renewal.source.installed.payload.disposition =
        exitCapacityProgram ∧
      ¬ noCapture.Captures ExitFutureCode.leave ∧
      (geometryCompilerAt (depth + 1)).actionableExitCapacity = 1 ∧
      step.normalForm.generatedNext.root.source.lawSurface =
        jointRoot.source.base.lawSurface := by
  let step := sourceGeneratedPeriodicDeathRepairNormalizationAt depth
  exact ⟨⟨step.normalForm.targetPortfolio⟩,
    step.normalForm.targetPortfolioRootExact,
    step.normalForm.nextVisitExact,
    ⟨step.normalForm.targetTenure⟩,
    ⟨step.normalForm.targetHealth⟩,
    step.normalForm.targetHealthServesAction,
    step.normalForm.targetProgramExact,
    step.normalForm.targetUncaptured,
    step.normalForm.targetCapacity,
    step.normalForm.lawSurfacePreserved⟩

/-- Removing either action leaves the other death mechanism untouched. -/
theorem ordinary_repairs_are_jointly_necessary (depth : Nat) :
    IsEmpty (SourceGeneratedStableDomainServiceIncidenceAt depth
      (exactEssentialAccessSeed .health)) ∧
      IsEmpty (CompletePortfolioAt depth (stablePortfolioSourceAt depth)) ∧
      IsEmpty (CapturedActionableFuturePortfolioAt depth) ∧
      (stableGeometryCompilerAt depth).actionableExitCapacity = 1 ∧
      (capturedGeometryCompilerAt depth).actionableExitCapacity = 0 ∧
      ¬ noCapture.Captures ExitFutureCode.leave ∧
      fullCapture.Captures ExitFutureCode.leave := by
  let step := sourceGeneratedPeriodicDeathRepairNormalizationAt depth
  exact ⟨step.maintenanceHealthEmpty,
    step.serviceCannotBeReplacedByCaptureRepair,
    step.captureCannotBeReplacedByServiceRepair,
    step.service.sourceDeathCapacityExact,
    step.captureDeath.capacityCollapse.2,
    step.maintenanceUncaptured,
    step.captureCaptured⟩

theorem fixed_normal_form_landing_is_not_u8 :
    let step := sourceGeneratedPeriodicDeathRepairNormalizationAt 0
    ordinaryEconomicLandingAt 0 = some
        (⟨M9ProofCarryingRenewalInquiryRoot.N,
          step.normalForm.generatedNext⟩ :
          AnyAuthoritativeRootCurrent) ∧
      ordinaryEconomicLandingAt 0 ≠ revolutionaryEconomicLanding ∧
      Nonempty (SourceGeneratedCaptureDeathPolicyU8At step.captureDeath) := by
  let step := sourceGeneratedPeriodicDeathRepairNormalizationAt 0
  let exits := captureDeathPolicyU8At step.captureDeath
  exact ⟨step.normalForm.ordinaryLandingExact,
    exits.landingsDistinct, ⟨exits⟩⟩

theorem adjacent_normalized_occurrences_are_distinct (depth : Nat) :
    periodicPaymentOccurrenceAt depth ≠
      periodicPaymentOccurrenceAt (depth + 1) := by
  let step := sourceGeneratedPeriodicDeathRepairNormalizationAt depth
  exact step.adjacentOccurrencesDistinct

/-! ## Canonical Prop sink -/

structure ProofCarryingPeriodicDeathRepairNormalizationCertificate : Prop where
  everyDepth : ∀ depth : Nat,
    Nonempty (SourceGeneratedPeriodicDeathRepairNormalizationAt depth)
  everyDepthCommuting : ∀ depth : Nat,
    let step := sourceGeneratedPeriodicDeathRepairNormalizationAt depth
    step.service.sourceDeath.stable.paymentOccurrence.rootOccurrence =
        step.service.rootOccurrence ∧
      step.captureDeath.fullServices.paymentOccurrence.rootOccurrence =
        step.service.rootOccurrence ∧
      step.captureDeath.ordinaryRepair.depth = depth ∧
      HEq step.captureDeath.ordinaryRepair.renewal.rootOccurrence
        (jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
          (temporalVisitAt depth)) ∧
      jointEssentialServiceRestorationProjection ≠ jointUBIProjection ∧
      step.service.installed.payload.sourceEntry =
        RootInquiryU8CompletionRegression.entry ∧
      step.captureDeath.ordinaryRepair.renewal.source.installed.payload.sourceEntry =
        RootInquiryU8CompletionRegression.entry ∧
      HEq step.service.installed.payload.selectedRow
        (installedUBIAt depth).payload.selectedRow ∧
      HEq step.captureDeath.ordinaryRepair.renewal.source.installed.payload.selectedRow
        (installedUBIAt depth).payload.selectedRow ∧
      step.service.applied.selectedWrite.sourceRow.CommutesWithWorld ∧
      step.captureDeath.ordinaryRepair.renewal.ordinarySelectedWrite.sourceRow.CommutesWithWorld ∧
      step.service.applied.wholeLedgerWriteBack =
        step.captureDeath.ordinaryRepair.renewal.wholeLedgerWriteBack ∧
      step.service.installed.RootAnswerAndNextFactorizes ∧
      step.captureDeath.ordinaryRepair.renewal.source.installed.RootAnswerAndNextFactorizes
  everyDepthTwoPathFactorization : ∀ depth : Nat,
    let step := sourceGeneratedPeriodicDeathRepairNormalizationAt depth
    Nonempty (SourceGeneratedOrdinaryEconomicNormalFormAt depth
      step.service step.captureDeath.ordinaryRepair
        step.service.applied.generatedNext) ∧
      step.normalForm.generatedNext = step.service.applied.generatedNext ∧
      step.normalForm.generatedNext =
        step.captureDeath.ordinaryRepair.renewal.generatedNext ∧
      step.normalForm.generatedNext =
        jointRoot.generatedNextCurrentAt (temporalVisitAt depth) ∧
      ordinaryEconomicLandingAt depth = some
        (⟨M9ProofCarryingRenewalInquiryRoot.N,
          step.normalForm.generatedNext⟩ :
          AnyAuthoritativeRootCurrent)
  everyDepthViableTarget : ∀ depth : Nat,
    let step := sourceGeneratedPeriodicDeathRepairNormalizationAt depth
    Nonempty (SourceGeneratedActionableFuturePortfolioAt (depth + 1)) ∧
      step.normalForm.targetPortfolio.paymentOccurrence.rootOccurrence =
        jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
          (temporalVisitAt (depth + 1)) ∧
      HEq step.normalForm.generatedNext.visit
        (temporalVisitAt (depth + 1)) ∧
      Nonempty (SourceGeneratedEssentialDomainActionableAt
        (depth + 1) tenureAuthority) ∧
      Nonempty (SourceGeneratedEssentialDomainActionableAt
        (depth + 1) healthAuthority) ∧
      (anomiePhaseAt (depth + 1)).served.get
          step.normalForm.targetHealth.serviceIncidence.slot =
        SourceAppliedEssentialServiceRestorationAt.unitAt
          step.service.installed.payload.disposition ∧
      SourceAppliedTenureCaptureRepairAt.targetProgramAt
          step.captureDeath.ordinaryRepair.renewal.source.installed.payload.disposition =
        exitCapacityProgram ∧
      ¬ noCapture.Captures ExitFutureCode.leave ∧
      (geometryCompilerAt (depth + 1)).actionableExitCapacity = 1 ∧
      step.normalForm.generatedNext.root.source.lawSurface =
        jointRoot.source.base.lawSurface
  everyDepthBothRepairsNecessary : ∀ depth : Nat,
    IsEmpty (SourceGeneratedStableDomainServiceIncidenceAt depth
      (exactEssentialAccessSeed .health)) ∧
      IsEmpty (CompletePortfolioAt depth (stablePortfolioSourceAt depth)) ∧
      IsEmpty (CapturedActionableFuturePortfolioAt depth) ∧
      (stableGeometryCompilerAt depth).actionableExitCapacity = 1 ∧
      (capturedGeometryCompilerAt depth).actionableExitCapacity = 0 ∧
      ¬ noCapture.Captures ExitFutureCode.leave ∧
      fullCapture.Captures ExitFutureCode.leave
  everyDepthAdjacentOccurrenceDistinct : ∀ depth : Nat,
    periodicPaymentOccurrenceAt depth ≠
      periodicPaymentOccurrenceAt (depth + 1)
  everyDepthNonterminal : ∀ depth : Nat, IsEmpty
    (SourceGeneratedGroundedEconomicTerminalAt
      (tenureRepairExposureAt depth) (tenureEconomicImageAt depth) none)
  fixedOrdinaryU8Separation :
    let step := sourceGeneratedPeriodicDeathRepairNormalizationAt 0
    ordinaryEconomicLandingAt 0 = some
        (⟨M9ProofCarryingRenewalInquiryRoot.N,
          step.normalForm.generatedNext⟩ :
          AnyAuthoritativeRootCurrent) ∧
      ordinaryEconomicLandingAt 0 ≠ revolutionaryEconomicLanding ∧
      Nonempty (SourceGeneratedCaptureDeathPolicyU8At step.captureDeath)
  mouthHasNoCompletedHistoryOrU8 : ∀ _depth : Nat, True

theorem proofCarryingPeriodicDeathRepairNormalizationDirectConsumer :
    ProofCarryingPeriodicDeathRepairNormalizationCertificate where
  everyDepth := every_generated_period_has_normalization
  everyDepthCommuting := normalization_occurrence_rows_and_ledger_commute
  everyDepthTwoPathFactorization :=
    both_actual_paths_factor_through_one_normal_form
  everyDepthViableTarget := normalized_target_is_simultaneously_viable
  everyDepthBothRepairsNecessary := ordinary_repairs_are_jointly_necessary
  everyDepthAdjacentOccurrenceDistinct :=
    adjacent_normalized_occurrences_are_distinct
  everyDepthNonterminal := fun depth =>
    (sourceGeneratedPeriodicDeathRepairNormalizationAt depth).groundedTerminalEmpty
  fixedOrdinaryU8Separation := by
    let separation := fixed_normal_form_landing_is_not_u8
    exact ⟨separation.1, separation.2.1, separation.2.2⟩
  mouthHasNoCompletedHistoryOrU8 :=
    periodic_normalization_mouth_has_no_forecast_or_u8_fields

end
end M14ProofCarryingPeriodicDeathRepairNormalizationRegression
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingPeriodicDeathRepairNormalizationRegression.both_actual_paths_factor_through_one_normal_form
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingPeriodicDeathRepairNormalizationRegression.ordinary_repairs_are_jointly_necessary
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingPeriodicDeathRepairNormalizationRegression.proofCarryingPeriodicDeathRepairNormalizationDirectConsumer
