import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Root.Economy.Attractor.FixedOneStepViabilityAttractor

/-!
# M14 direct consumer for the fixed one-step viability attractor

The consumer checks an actual viable-fibre insertion, not a second list of
target properties.  It also keeps both source deaths and the existing U8
alternative visible, so ordinary viability is neither a source deletion nor
a revolutionary update.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingFixedOneStepViabilityAttractorRegression

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Renewal UBI Capacity Space CrossingCost
open ConstructiveRoot.RootInquiryCompletion
open M9ProofCarryingRenewalInquiryRoot
open M14UBIPeriodicRootHistory
open M14ActionableFuturePortfolio
open M14EconomicSingleFold
open M14GeneratedEconomicDisposition
open M14PortfolioMaintenanceDeath
open M14PortfolioCaptureDeath
open M14PeriodicDeathRepairNormalization
open M14FixedOneStepViabilityAttractor

theorem normalized_receipts_enter_existing_viable_fibre :
    let attractor := sourceGeneratedFixedOneStepViabilityAttractor
    HEq attractor.normalization.normalForm.targetPortfolio
        attractor.viable.portfolio ∧
      attractor.normalization.normalForm.generatedNext =
        attractor.viable.viable.ordinary.renewal.generatedNext ∧
      ordinaryEconomicLandingAt 0 = some
        (⟨M9ProofCarryingRenewalInquiryRoot.N,
          attractor.normalization.normalForm.generatedNext⟩ :
          AnyAuthoritativeRootCurrent) ∧
      postRepairViableExposure.root.erasedRootEvent =
        ⟨temporalVisitAt 1,
          attractor.normalization.normalForm.targetPortfolio.paymentOccurrence.rootOccurrence⟩ ∧
      postRepairViableImage = economicImage postRepairViableExposure ∧
      attractor.viableDisposition =
        M14GeneratedEconomicDisposition.viableDisposition ∧
      Nonempty (EconomicDispositionAt postRepairViableExposure
        postRepairViableImage (ordinaryEconomicLandingAt 0)) := by
  let attractor := sourceGeneratedFixedOneStepViabilityAttractor
  exact ⟨attractor.targetPortfolioExact,
    attractor.targetNextExact,
    attractor.targetLandingExact,
    attractor.targetOccurrenceExact,
    attractor.targetImageExact,
    attractor.viableDispositionExact,
    ⟨attractor.viableDisposition⟩⟩

theorem one_actual_step_preserves_source_deaths_and_u8_alternative :
    let attractor := sourceGeneratedFixedOneStepViabilityAttractor
    Nonempty (SourceGeneratedPortfolioMaintenanceDeathAt 0
      (stablePortfolioSourceAt 0)) ∧
      Nonempty (SourceGeneratedPortfolioCaptureDeathAt 0
        (fullPortfolioSourceAt 0) M14UBIExitCapacityFixture.fullCapture) ∧
      IsEmpty (CompletePortfolioAt 0 (stablePortfolioSourceAt 0)) ∧
      IsEmpty (CapturedActionableFuturePortfolioAt 0) ∧
      periodicPaymentOccurrenceAt 0 ≠ periodicPaymentOccurrenceAt 1 ∧
      IsEmpty (SourceGeneratedGroundedEconomicTerminalAt
        (tenureRepairExposureAt 0) (tenureEconomicImageAt 0) none) ∧
      Nonempty (SourceGeneratedCaptureDeathPolicyU8At
        attractor.normalization.captureDeath) ∧
      ordinaryEconomicLandingAt 0 ≠ revolutionaryEconomicLanding := by
  let attractor := sourceGeneratedFixedOneStepViabilityAttractor
  exact ⟨⟨attractor.normalization.service.sourceDeath⟩,
    ⟨attractor.normalization.captureDeath⟩,
    attractor.sourceMaintenanceStillEmpty,
    attractor.sourceCaptureStillEmpty,
    attractor.oneActualStep,
    attractor.nonterminal,
    ⟨captureDeathPolicyU8At attractor.normalization.captureDeath⟩,
    attractor.ordinaryU8Distinct⟩

theorem viable_entry_is_same_law_ordinary_not_u8 :
    let attractor := sourceGeneratedFixedOneStepViabilityAttractor
    attractor.normalization.normalForm.generatedNext.root.source.lawSurface =
        jointRoot.source.base.lawSurface ∧
      ordinaryEconomicLandingAt 0 = some
        (⟨M9ProofCarryingRenewalInquiryRoot.N,
          attractor.viable.viable.ordinary.renewal.generatedNext⟩ :
          AnyAuthoritativeRootCurrent) ∧
      ordinaryEconomicLandingAt 0 ≠ revolutionaryEconomicLanding := by
  let attractor := sourceGeneratedFixedOneStepViabilityAttractor
  exact ⟨attractor.lawSurfacePreserved,
    attractor.viableLandingExact,
    attractor.ordinaryU8Distinct⟩

structure ProofCarryingFixedOneStepViabilityAttractorCertificate : Prop where
  standing : Nonempty (SourceGeneratedFixedOneStepViabilityAttractorAt
    (sourceGeneratedPeriodicDeathRepairNormalizationAt 0)
    fixedPortfolioViableEconomicDisposition)
  exactViableFibre :
    let attractor := sourceGeneratedFixedOneStepViabilityAttractor
    HEq attractor.normalization.normalForm.targetPortfolio
        attractor.viable.portfolio ∧
      attractor.normalization.normalForm.generatedNext =
        attractor.viable.viable.ordinary.renewal.generatedNext ∧
      ordinaryEconomicLandingAt 0 = some
        (⟨M9ProofCarryingRenewalInquiryRoot.N,
          attractor.normalization.normalForm.generatedNext⟩ :
          AnyAuthoritativeRootCurrent) ∧
      postRepairViableExposure.root.erasedRootEvent =
        ⟨temporalVisitAt 1,
          attractor.normalization.normalForm.targetPortfolio.paymentOccurrence.rootOccurrence⟩ ∧
      postRepairViableImage = economicImage postRepairViableExposure ∧
      attractor.viableDisposition =
        M14GeneratedEconomicDisposition.viableDisposition ∧
      Nonempty (EconomicDispositionAt postRepairViableExposure
        postRepairViableImage (ordinaryEconomicLandingAt 0))
  sourceDeathsAndAlternativeRetained :
    let attractor := sourceGeneratedFixedOneStepViabilityAttractor
    Nonempty (SourceGeneratedPortfolioMaintenanceDeathAt 0
      (stablePortfolioSourceAt 0)) ∧
      Nonempty (SourceGeneratedPortfolioCaptureDeathAt 0
        (fullPortfolioSourceAt 0) M14UBIExitCapacityFixture.fullCapture) ∧
      IsEmpty (CompletePortfolioAt 0 (stablePortfolioSourceAt 0)) ∧
      IsEmpty (CapturedActionableFuturePortfolioAt 0) ∧
      periodicPaymentOccurrenceAt 0 ≠ periodicPaymentOccurrenceAt 1 ∧
      IsEmpty (SourceGeneratedGroundedEconomicTerminalAt
        (tenureRepairExposureAt 0) (tenureEconomicImageAt 0) none) ∧
      Nonempty (SourceGeneratedCaptureDeathPolicyU8At
        attractor.normalization.captureDeath) ∧
      ordinaryEconomicLandingAt 0 ≠ revolutionaryEconomicLanding
  sameLawOrdinaryBranch :
    let attractor := sourceGeneratedFixedOneStepViabilityAttractor
    attractor.normalization.normalForm.generatedNext.root.source.lawSurface =
        jointRoot.source.base.lawSurface ∧
      ordinaryEconomicLandingAt 0 = some
        (⟨M9ProofCarryingRenewalInquiryRoot.N,
          attractor.viable.viable.ordinary.renewal.generatedNext⟩ :
          AnyAuthoritativeRootCurrent) ∧
      ordinaryEconomicLandingAt 0 ≠ revolutionaryEconomicLanding
  mouthHasNoRankForecastOrU8 : True

theorem proofCarryingFixedOneStepViabilityAttractorDirectConsumer :
    ProofCarryingFixedOneStepViabilityAttractorCertificate where
  standing := ⟨sourceGeneratedFixedOneStepViabilityAttractor⟩
  exactViableFibre := normalized_receipts_enter_existing_viable_fibre
  sourceDeathsAndAlternativeRetained :=
    one_actual_step_preserves_source_deaths_and_u8_alternative
  sameLawOrdinaryBranch := viable_entry_is_same_law_ordinary_not_u8
  mouthHasNoRankForecastOrU8 :=
    fixed_one_step_attractor_mouth_has_no_rank_forecast_or_u8_fields

end
end M14ProofCarryingFixedOneStepViabilityAttractorRegression
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingFixedOneStepViabilityAttractorRegression.normalized_receipts_enter_existing_viable_fibre
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingFixedOneStepViabilityAttractorRegression.one_actual_step_preserves_source_deaths_and_u8_alternative
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingFixedOneStepViabilityAttractorRegression.proofCarryingFixedOneStepViabilityAttractorDirectConsumer
