import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Root.Economy.Attractor.PeriodicNormalizedViableDisposition

/-!
# M14 direct consumer for periodic normalized viable dispositions

For every generated finite depth, the action-indexed normalization enters the
unchanged viable summand at the next visit.  The consumer checks the actual
exit, mandate, consumers, fold occurrence/image, source deaths, and depth-zero
restriction.  It stores only pointwise propositions, never a completed future.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingPeriodicNormalizedViableDispositionRegression

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Renewal Revision UBI Capacity Space CrossingCost Observer Settlement Money
open Settlement.SourceOwnedSettlementCompiler
open ConstructiveRoot.ObstructionGeneratedMinimalCoface
open ConstructiveRoot.RootInquiryCompletion
open M3FiniteExchangeFixture M3ExchangeSettlementPriceRegression
open M3SettlementDispositionRegression
open M9ProofCarryingRenewalInquiryRoot
open M14UBIExitCapacityFixture
open M14UBIPeriodicRootHistory
open M14UBIPeriodicActualServiceCapacity
open M14EssentialAccessRelationFixture
open M14EssentialAccessSectorRegression
open M14ActionableFuturePortfolio
open M14EconomicSingleFold
open M14GeneratedEconomicDisposition
open M14PortfolioMaintenanceDeath
open M14PortfolioCaptureDeath
open M9ProofCarryingRenewalU8Revision
open M14PeriodicMandatePowerRenewal
open M14ProofCarryingRecognitionWitnessEscapeRegression
open M14UBIPolicyBreakingOccurrence
open M14UBIPolicySelfU8Regression
open M14PeriodicDeathRepairNormalization
open M14FixedOneStepViabilityAttractor
open M14PeriodicNormalizedViableDisposition

theorem every_period_enters_existing_viable_fibre (depth : Nat) :
    let entry := sourceGeneratedPeriodicNormalizedViableDispositionAt depth
    Nonempty (SourceGeneratedPeriodicNormalizedViableDispositionAt depth
      (sourceGeneratedPeriodicDeathRepairNormalizationAt depth)
      (portfolioViableEconomicDispositionAt depth)) ∧
      entry.viable.depth = depth ∧
      entry.viable.viable.depth = depth ∧
      HEq entry.normalization.normalForm.targetPortfolio
        entry.viable.portfolio ∧
      HEq entry.normalization.normalForm.targetPortfolio.paymentOccurrence
        entry.viable.viable.actualExit.paymentOccurrence ∧
      entry.normalization.normalForm.generatedNext =
        entry.viable.viable.ordinary.renewal.generatedNext ∧
      entry.normalization.normalForm.generatedNext =
        jointRoot.generatedNextCurrentAt (temporalVisitAt depth) ∧
      (postRepairViableExposureAt depth).root.erasedRootEvent =
        ⟨temporalVisitAt (depth + 1),
          entry.normalization.normalForm.targetPortfolio.paymentOccurrence.rootOccurrence⟩ ∧
      postRepairViableImageAt depth =
        economicImage (postRepairViableExposureAt depth) ∧
      entry.viableDisposition = .inl entry.viable.viable ∧
      Nonempty (EconomicDispositionAt (postRepairViableExposureAt depth)
        (postRepairViableImageAt depth)
          (ordinaryEconomicLandingAt depth)) := by
  let entry := sourceGeneratedPeriodicNormalizedViableDispositionAt depth
  exact ⟨⟨entry⟩,
    entry.viableDepthExact,
    entry.viable.viableDepthExact,
    entry.targetPortfolioExact,
    entry.targetPaymentIsViableExit,
    entry.targetNextExact,
    entry.targetNextIsRoot,
    entry.targetOccurrenceExact,
    entry.targetImageExact,
    entry.viableDispositionExact,
    ⟨entry.viableDisposition⟩⟩

theorem next_visit_viability_retains_actual_authorities (depth : Nat) :
    let entry := sourceGeneratedPeriodicNormalizedViableDispositionAt depth
    Nonempty (PeriodicActualServiceExitAt (depth + 1)) ∧
      Nonempty (SourceGeneratedProofCarryingPeriodicMandatePowerRenewalAt
        (depth + 1)) ∧
      entry.viable.viable.mandate.rootOccurrence =
        jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
          (temporalVisitAt (depth + 1)) ∧
      (geometryCompilerAt (depth + 1)).actionableExitCapacity = 1 ∧
      ¬ noCapture.Captures ExitFutureCode.leave ∧
      Nonempty (OpenSettlementAt.ActivatedResidualConsumerAt
        (exactOpenSettlement exactResidualActivation)) ∧
      Nonempty (SourceOwnsResponsibilityIncidence V
        (P.boundarySource
          capturedProgram.purchasingPowerStanding.activatedConsumer.activation)
        (exactOpenSettlement exactResidualActivation).obligation) ∧
      Nonempty (FaithfulAuthorityReconstruction
        sourceGeneratedProofCarryingRecognitionWitnessEscape.refinedObserver) ∧
      Nonempty (FaithfulCofaceMorphism u8Gate.minimalCoface
        jointCore.revision.generate.toAdmissibleMinimalCoface) ∧
      entry.normalization.normalForm.generatedNext.root.source.lawSurface =
        jointRoot.source.base.lawSurface := by
  let entry := sourceGeneratedPeriodicNormalizedViableDispositionAt depth
  exact ⟨⟨entry.viable.viable.actualExit⟩,
    ⟨entry.viable.viable.mandate⟩,
    entry.viable.viable.mandateRootExact,
    entry.targetCapacityExact,
    entry.targetUncaptured,
    entry.viable.viable.residualConsumer,
    entry.viable.viable.sourceOwnedResidual,
    entry.viable.viable.observerCorrection,
    entry.viable.viable.revisionRoute,
    entry.lawSurfacePreserved⟩

theorem periodic_basin_entry_does_not_delete_source_deaths (depth : Nat) :
    Nonempty (SourceGeneratedPortfolioMaintenanceDeathAt depth
      (stablePortfolioSourceAt depth)) ∧
      Nonempty (SourceGeneratedPortfolioCaptureDeathAt depth
        (fullPortfolioSourceAt depth) fullCapture) ∧
      IsEmpty (CompletePortfolioAt depth (stablePortfolioSourceAt depth)) ∧
      IsEmpty (CapturedActionableFuturePortfolioAt depth) ∧
      IsEmpty (SourceGeneratedGroundedEconomicTerminalAt
        (tenureRepairExposureAt depth) (tenureEconomicImageAt depth) none) ∧
      periodicPaymentOccurrenceAt depth ≠
        periodicPaymentOccurrenceAt (depth + 1) := by
  let entry := sourceGeneratedPeriodicNormalizedViableDispositionAt depth
  exact ⟨⟨entry.normalization.service.sourceDeath⟩,
    ⟨entry.normalization.captureDeath⟩,
    entry.sourceMaintenanceStillEmpty,
    entry.sourceCaptureStillEmpty,
    entry.groundedTerminalEmpty,
    entry.adjacentOccurrencesDistinct⟩

theorem depth_zero_is_the_existing_fixed_attractor :
    let periodic := sourceGeneratedPeriodicNormalizedViableDispositionAt 0
    let fixed := sourceGeneratedFixedOneStepViabilityAttractor
    periodic.normalization = fixed.normalization ∧
      periodic.viable = fixed.viable ∧
      periodic.viableDisposition = fixed.viableDisposition :=
  depthZero_periodic_restricts_to_fixed

structure ProofCarryingPeriodicNormalizedViableDispositionCertificate : Prop where
  everyDepthViableFibre : ∀ depth : Nat,
    let entry := sourceGeneratedPeriodicNormalizedViableDispositionAt depth
    Nonempty (SourceGeneratedPeriodicNormalizedViableDispositionAt depth
      (sourceGeneratedPeriodicDeathRepairNormalizationAt depth)
      (portfolioViableEconomicDispositionAt depth)) ∧
      entry.viable.depth = depth ∧
      entry.viable.viable.depth = depth ∧
      HEq entry.normalization.normalForm.targetPortfolio
        entry.viable.portfolio ∧
      HEq entry.normalization.normalForm.targetPortfolio.paymentOccurrence
        entry.viable.viable.actualExit.paymentOccurrence ∧
      entry.normalization.normalForm.generatedNext =
        entry.viable.viable.ordinary.renewal.generatedNext ∧
      entry.normalization.normalForm.generatedNext =
        jointRoot.generatedNextCurrentAt (temporalVisitAt depth) ∧
      (postRepairViableExposureAt depth).root.erasedRootEvent =
        ⟨temporalVisitAt (depth + 1),
          entry.normalization.normalForm.targetPortfolio.paymentOccurrence.rootOccurrence⟩ ∧
      postRepairViableImageAt depth =
        economicImage (postRepairViableExposureAt depth) ∧
      entry.viableDisposition = .inl entry.viable.viable ∧
      Nonempty (EconomicDispositionAt (postRepairViableExposureAt depth)
        (postRepairViableImageAt depth)
          (ordinaryEconomicLandingAt depth))
  everyDepthActualAuthorities : ∀ depth : Nat,
    let entry := sourceGeneratedPeriodicNormalizedViableDispositionAt depth
    Nonempty (PeriodicActualServiceExitAt (depth + 1)) ∧
      Nonempty (SourceGeneratedProofCarryingPeriodicMandatePowerRenewalAt
        (depth + 1)) ∧
      entry.viable.viable.mandate.rootOccurrence =
        jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
          (temporalVisitAt (depth + 1)) ∧
      (geometryCompilerAt (depth + 1)).actionableExitCapacity = 1 ∧
      ¬ noCapture.Captures ExitFutureCode.leave ∧
      Nonempty (OpenSettlementAt.ActivatedResidualConsumerAt
        (exactOpenSettlement exactResidualActivation)) ∧
      Nonempty (SourceOwnsResponsibilityIncidence V
        (P.boundarySource
          capturedProgram.purchasingPowerStanding.activatedConsumer.activation)
        (exactOpenSettlement exactResidualActivation).obligation) ∧
      Nonempty (FaithfulAuthorityReconstruction
        sourceGeneratedProofCarryingRecognitionWitnessEscape.refinedObserver) ∧
      Nonempty (FaithfulCofaceMorphism u8Gate.minimalCoface
        jointCore.revision.generate.toAdmissibleMinimalCoface) ∧
      entry.normalization.normalForm.generatedNext.root.source.lawSurface =
        jointRoot.source.base.lawSurface
  everyDepthSourceDeathsRetained : ∀ depth : Nat,
    Nonempty (SourceGeneratedPortfolioMaintenanceDeathAt depth
      (stablePortfolioSourceAt depth)) ∧
      Nonempty (SourceGeneratedPortfolioCaptureDeathAt depth
        (fullPortfolioSourceAt depth) fullCapture) ∧
      IsEmpty (CompletePortfolioAt depth (stablePortfolioSourceAt depth)) ∧
      IsEmpty (CapturedActionableFuturePortfolioAt depth) ∧
      IsEmpty (SourceGeneratedGroundedEconomicTerminalAt
        (tenureRepairExposureAt depth) (tenureEconomicImageAt depth) none) ∧
      periodicPaymentOccurrenceAt depth ≠
        periodicPaymentOccurrenceAt (depth + 1)
  depthZeroFixedRestriction :
    let periodic := sourceGeneratedPeriodicNormalizedViableDispositionAt 0
    let fixed := sourceGeneratedFixedOneStepViabilityAttractor
    periodic.normalization = fixed.normalization ∧
      periodic.viable = fixed.viable ∧
      periodic.viableDisposition = fixed.viableDisposition
  noCompletedHistory : ∀ _depth : Nat, True

theorem proofCarryingPeriodicNormalizedViableDispositionDirectConsumer :
    ProofCarryingPeriodicNormalizedViableDispositionCertificate where
  everyDepthViableFibre := every_period_enters_existing_viable_fibre
  everyDepthActualAuthorities :=
    next_visit_viability_retains_actual_authorities
  everyDepthSourceDeathsRetained :=
    periodic_basin_entry_does_not_delete_source_deaths
  depthZeroFixedRestriction := depth_zero_is_the_existing_fixed_attractor
  noCompletedHistory :=
    periodic_viable_mouth_has_no_rank_coverage_or_completed_history

end
end M14ProofCarryingPeriodicNormalizedViableDispositionRegression
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingPeriodicNormalizedViableDispositionRegression.every_period_enters_existing_viable_fibre
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingPeriodicNormalizedViableDispositionRegression.periodic_basin_entry_does_not_delete_source_deaths
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingPeriodicNormalizedViableDispositionRegression.proofCarryingPeriodicNormalizedViableDispositionDirectConsumer
