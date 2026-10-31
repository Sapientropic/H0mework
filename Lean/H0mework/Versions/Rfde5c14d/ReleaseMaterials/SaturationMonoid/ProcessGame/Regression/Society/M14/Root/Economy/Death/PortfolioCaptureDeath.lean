import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Root.Economy.Death.PortfolioMaintenanceDeath
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Consumer.Identification.ZeroCapacityCausalNonidentifiabilityRegression
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Policy.UBIPolicySelfU8Regression

/-!
# M14 source-generated portfolio-capture death

The full source-generated tenure/health service portfolio may remain live
while full price capture removes every actionable purchasing-power future.
This module carries that exact cause through the existing open settlement,
residual bearer, activated consumer, source-owned responsibility incidence,
ordinary remove-capture renewal, and the fixed depth-zero self-U8 route.

The source and capture compiler are type indices.  The sole producer accepts
only a finite depth and returns the compiler-owned full source/full-capture
indices.  A stable source, `noCapture`, nominal transfer readout, or scalar
capacity cannot be supplied as capture authority.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14PortfolioCaptureDeath

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations Settlement Price Money UBI Renewal
open Capacity Space CrossingCost Revision
open Settlement.SourceOwnedSettlementCompiler
open UBI.Capacity UBI.Capacity.SourceOwnedExitGeometryCompilerAt
open ConstructiveRoot.RootInquiryCompletion
open ConstructiveRoot.ObstructionGeneratedMinimalCoface
open M3FiniteExchangeFixture M3ExchangeSettlementPriceRegression
open M8PurchasingPowerStandingRegression
open M9ProofCarryingRenewalInquiryRoot
open M9ProofCarryingRenewalInquiryRuntime
open M9ProofCarryingRenewalU8Revision
open M14UBIExitCapacityFixture
open M14UBIProofCarryingRootRestriction
open M14UBIPeriodicRootHistory
open M14UBIPeriodicActualServiceCapacity
open M14EssentialAccessRelationFixture
open M14EssentialAccessSectorRegression
open M14CaptureResponsibilityDispositionRegression
open M14ZeroCapacityCausalNonidentifiabilityRegression
open M14GeneratedEconomicDisposition
open M14ActionableFuturePortfolio
open M14PortfolioMaintenanceDeath
open M14TenureCaptureRouteRepairNoGoRegression
open M14ProofCarryingExitRepairRegression
open M14ProofCarryingExitRepairRenewalRegression
open M14UBIPolicyBreakingOccurrence
open M14UBIPolicySelfU8Regression

abbrev CaptureCompiler := SourceOwnedPriceCaptureCompilerAt
  exitRelationCompiler
  (OpenSettlementAt settlementCompiler openOccurrence)
  (exactOpenSettlement exactResidualActivation)

/-! ## Captured dependent portfolio -/

abbrev CapturedDomainActionableAt
    (depth : Nat) (domain : EssentialAccessRelationAuthority) :=
  ExactFeasibleExitEdgeAt (capturedGeometryCompilerAt depth)
    ExitFutureCode.leave (domainSlotAt depth domain)

abbrev CapturedActionableFuturePortfolioAt (depth : Nat) :=
  (domain : EssentialAccessRelationAuthority) →
    CapturedDomainActionableAt depth domain

instance capturedActionableFuturePortfolio_isEmpty (depth : Nat) :
    IsEmpty (CapturedActionableFuturePortfolioAt depth) :=
  ⟨fun portfolio => by
    let edge := portfolio tenureAuthority
    have noExit : IsEmpty capturedProgram.exitCone.ActionableExitAt :=
      capturedProgram.exitCone.isEmpty_actionableExit_iff_fullPriceCapture.mpr
        capturedProgram_fullPriceCapture
    exact noExit.false ⟨ExitFutureCode.leave, edge.codeSurvives⟩⟩

/-! ## Exact local-death carrier -/

/-- Capture death requires both the full service source and the exact full
capture compiler as indices. -/
structure SourceGeneratedPortfolioCaptureDeathAt
    (depth : Nat) (source : EssentialPortfolioSourceAt depth)
    (captureCompiler : CaptureCompiler) : Type 18 where
  private mk ::
  source_eq : source = fullPortfolioSourceAt depth
  captureCompiler_eq : captureCompiler = fullCapture
  fullServices : SourceGeneratedActionableFuturePortfolioAt depth
  fullServices_eq : fullServices =
    sourceGeneratedActionableFuturePortfolioAt depth
  captureSignature : PriceCaptureSignatureAt depth
  captureResponsibility : PeriodicCaptureResponsibilityAt depth
    (periodicSourceBackedPaymentAt depth)
  paymentRootExact : fullServices.paymentOccurrence.rootOccurrence =
    jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
      (temporalVisitAt depth)
  tenureServiceLive : SourceGeneratedEssentialDomainActionableAt
    depth tenureAuthority
  healthServiceLive : SourceGeneratedEssentialDomainActionableAt
    depth healthAuthority
  captured : fullCapture.Captures ExitFutureCode.leave
  capturedPortfolioEmpty : IsEmpty
    (CapturedActionableFuturePortfolioAt depth)
  exactSettlement :
    fullCapture.captureSettlement ExitFutureCode.leave leave_is_captured =
      exactOpenSettlement exactResidualActivation
  residualBearerRetained :
    OpenSettlementAt.residualBearer
        (fullCapture.captureSettlement ExitFutureCode.leave leave_is_captured) =
      OpenSettlementAt.residualBearer
        (exactOpenSettlement exactResidualActivation)
  generatedBeneficiary :
    OpenSettlementAt.protectedInterest
        (fullCapture.captureSettlement ExitFutureCode.leave leave_is_captured) =
      exchangeLaw.protectedInterestOfActor
        (exactCounterpartyActor exactResidualActivation)
  activatedResidualConsumer : Nonempty
    (OpenSettlementAt.ActivatedResidualConsumerAt
      (exactOpenSettlement exactResidualActivation))
  sourceOwnedResidual : Nonempty (SourceOwnsResponsibilityIncidence V
    (P.boundarySource
      capturedProgram.purchasingPowerStanding.activatedConsumer.activation)
    (exactOpenSettlement exactResidualActivation).obligation)
  residualConsumerNextExact :
    capturedProgram.purchasingPowerStanding.activatedConsumer.nextGeneratedState =
      capturedProgram.payment.nextGenerated
  capacityCollapse :
    (geometryCompilerAt depth).actionableExitCapacity = 1 ∧
      (capturedGeometryCompilerAt depth).actionableExitCapacity = 0
  ordinaryRepair : SourceGeneratedOrdinaryEconomicDispositionAt
    (tenureRepairExposureAt depth) (tenureEconomicImageAt depth)
      (ordinaryEconomicLandingAt depth)
  ordinaryRepairIsRemoveCapture :
    canonicalRepairAt (tenureCaptureOriginAt depth) = .removeCapture
  ordinaryNextExact : ordinaryRepair.renewal.generatedNext =
    jointRoot.generatedNextCurrentAt (temporalVisitAt depth)
  groundedTerminalEmpty : IsEmpty
    (SourceGeneratedGroundedEconomicTerminalAt
      (tenureRepairExposureAt depth) (tenureEconomicImageAt depth) none)
  actualRootSuccessor :
    (jointRoot.toAuthoritativeRoot.toRoot.evolutionAt
      (rootVisitAt depth).current).nextCurrent? =
        some (rootVisitAt depth).current

/-- Sole capture-death producer. -/
def portfolioCaptureDeathAt (depth : Nat) :
    SourceGeneratedPortfolioCaptureDeathAt depth
      (fullPortfolioSourceAt depth) fullCapture :=
  let full := sourceGeneratedActionableFuturePortfolioAt depth
  let responsibility := periodicCaptureResponsibilityAt depth
  let ordinary := ordinaryEconomicDispositionAt depth
  { source_eq := rfl
    captureCompiler_eq := rfl
    fullServices := full
    fullServices_eq := rfl
    captureSignature := priceCaptureSignatureAt depth
    captureResponsibility := responsibility
    paymentRootExact := full.rootOccurrenceExact
    tenureServiceLive := full.actionable tenureAuthority
    healthServiceLive := full.actionable healthAuthority
    captured := leave_is_captured
    capturedPortfolioEmpty :=
      capturedActionableFuturePortfolio_isEmpty depth
    exactSettlement := responsibility.captureDisposition.exactSettlement
    residualBearerRetained := responsibility.captureDisposition.bearerRetained
    generatedBeneficiary := responsibility.captureDisposition.beneficiaryGenerated
    activatedResidualConsumer :=
      responsibility.captureDisposition.activatedResidualConsumer
    sourceOwnedResidual := responsibility.captureDisposition.sourceOwnedResidual
    residualConsumerNextExact :=
      responsibility.captureDisposition.consumerNextIsPaymentNext
    capacityCollapse := responsibility.capacityCollapse
    ordinaryRepair := ordinary
    ordinaryRepairIsRemoveCapture := ordinary.renewal.repair_eq_removeCapture
    ordinaryNextExact := ordinary.generatedNextExact
    groundedTerminalEmpty := fixedGroundedEconomicTerminal_isEmpty depth
    actualRootSuccessor := fixedRoot_has_actual_successor depth }

theorem every_generated_period_has_capture_death (depth : Nat) :
    Nonempty (SourceGeneratedPortfolioCaptureDeathAt depth
      (fullPortfolioSourceAt depth) fullCapture) :=
  ⟨portfolioCaptureDeathAt depth⟩

/-! ## Exact-source and exact-capture negatives -/

instance stableSource_captureDeath_isEmpty (depth : Nat) :
    IsEmpty (SourceGeneratedPortfolioCaptureDeathAt depth
      (stablePortfolioSourceAt depth) fullCapture) :=
  ⟨fun death =>
    full_stable_sources_distinct depth death.source_eq.symm⟩

theorem noCapture_ne_fullCapture : noCapture ≠ fullCapture := by
  intro equality
  apply uncaptured_leave_has_no_capture_verdict
  rw [equality]
  exact leave_is_captured

instance noCapture_captureDeath_isEmpty (depth : Nat) :
    IsEmpty (SourceGeneratedPortfolioCaptureDeathAt depth
      (fullPortfolioSourceAt depth) noCapture) :=
  ⟨fun death => noCapture_ne_fullCapture death.captureCompiler_eq⟩

theorem stable_source_cannot_generate_capture_death (depth : Nat) :
    IsEmpty (SourceGeneratedPortfolioCaptureDeathAt depth
      (stablePortfolioSourceAt depth) fullCapture) :=
  stableSource_captureDeath_isEmpty depth

theorem uncaptured_compiler_cannot_generate_capture_death (depth : Nat) :
    IsEmpty (SourceGeneratedPortfolioCaptureDeathAt depth
      (fullPortfolioSourceAt depth) noCapture) :=
  noCapture_captureDeath_isEmpty depth

/-! ## Fixed existing policy-U8 refinement -/

/-- At the fixed breaking occurrence, capture death exposes both the actual
ordinary remove-capture renewal and the existing revolutionary self-U8 route.
The death witness is not a branch selector: the two authorities retain their
distinct producer mouths and strictly different landings. -/
structure SourceGeneratedCaptureDeathPolicyU8At
    (death : SourceGeneratedPortfolioCaptureDeathAt 0
      (fullPortfolioSourceAt 0) fullCapture) : Type 18 where
  private mk ::
  ordinary : SourceGeneratedOrdinaryEconomicDispositionAt
    (tenureRepairExposureAt 0) (tenureEconomicImageAt 0)
      (ordinaryEconomicLandingAt 0)
  ordinary_eq : ordinary = death.ordinaryRepair
  requiresU8 : SourceGeneratedRequiresU8EconomicDispositionAt
    (tenureRepairExposureAt 0) (tenureEconomicImageAt 0)
      revolutionaryEconomicLanding
  exactBreakingOccurrence :
    (⟨jointVisit.current, audit.rootOccurrence⟩ :
      Sigma M14UBIPolicyBreakingOccurrence.Root.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt) =
      ⟨(temporalVisitAt 0).current,
        (periodicSourceBackedPaymentAt 0).rootOccurrence.occurrence⟩
  gateToCore : Nonempty
    (FaithfulCofaceMorphism u8Gate.minimalCoface
      jointCore.revision.generate.toAdmissibleMinimalCoface)
  exactFirstWrite : jointCore.cofaceFactorization.2.firstWrite =
    M13SelfU8Regression.selfU8.firstWrite
  runtimeConsumesCore :
    SourceNativeInquiryRuntime.CofaceRealizationResumptionAt
      jointCore jointRuntime 0
  ordinaryLandingExact : ordinaryEconomicLandingAt 0 = some
    (⟨M9ProofCarryingRenewalInquiryRoot.N,
      ordinary.renewal.generatedNext⟩ : AnyAuthoritativeRootCurrent)
  revisedLandingExact :
    revolutionaryEconomicLanding =
      some requiresU8.legislation.policyLegislation.generatedNext
  landingsDistinct :
    ordinaryEconomicLandingAt 0 ≠ revolutionaryEconomicLanding
  groundedTerminalEmpty : IsEmpty
    (SourceGeneratedGroundedEconomicTerminalAt
      (tenureRepairExposureAt 0) (tenureEconomicImageAt 0) none)

def captureDeathPolicyU8At
    (death : SourceGeneratedPortfolioCaptureDeathAt 0
      (fullPortfolioSourceAt 0) fullCapture) :
    SourceGeneratedCaptureDeathPolicyU8At death :=
  let requiresU8 := requiresU8EconomicDisposition
  { ordinary := death.ordinaryRepair
    ordinary_eq := rfl
    requiresU8 := requiresU8
    exactBreakingOccurrence := requiresU8.exactBreakingOccurrence
    gateToCore := requiresU8.gateToCore
    exactFirstWrite := requiresU8.exactFirstWrite
    runtimeConsumesCore := requiresU8.runtimeConsumesCore
    ordinaryLandingExact := death.ordinaryRepair.landing_eq
    revisedLandingExact := requiresU8.landing_eq
    landingsDistinct := requiresU8.ordinaryLandingDistinct
    groundedTerminalEmpty := fixedGroundedEconomicTerminal_isEmpty 0 }

theorem fixed_capture_death_generates_ordinary_and_u8_exits :
    Nonempty (SourceGeneratedCaptureDeathPolicyU8At
      (portfolioCaptureDeathAt 0)) :=
  ⟨captureDeathPolicyU8At (portfolioCaptureDeathAt 0)⟩

end
end M14PortfolioCaptureDeath
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14PortfolioCaptureDeath.portfolioCaptureDeathAt
#print axioms SaturationMonoid.ProcessGame.Society.M14PortfolioCaptureDeath.uncaptured_compiler_cannot_generate_capture_death
#print axioms SaturationMonoid.ProcessGame.Society.M14PortfolioCaptureDeath.fixed_capture_death_generates_ordinary_and_u8_exits
