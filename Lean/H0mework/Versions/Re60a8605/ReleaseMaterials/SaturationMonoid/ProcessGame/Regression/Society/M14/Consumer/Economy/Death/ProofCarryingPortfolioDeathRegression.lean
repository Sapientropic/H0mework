import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Root.Economy.Death.PortfolioCaptureDeath
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Root.Economy.Maintenance.PeriodicEssentialServiceRestoration

/-!
# M14 proof-carrying portfolio-death consumer

Maintenance death and capture death are two source-strict local failures on
the same generated temporal root.  No death-mode enumeration compares them:
the stable/full source indices, health-service fibres, and no-capture/full-
capture compilers themselves carry the distinction.

The maintenance branch has payment, route, tenure action, and scalar capacity
`1` but no health service.  The capture branch has the full tenure/health
service portfolio before capture, yet full capture yields capacity `0` and an
accounted residual destination.  Both branches retain the actual root
self-loop and reject the existing grounded-terminal/`none` landing fibre.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingPortfolioDeathRegression

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations Settlement Price Money UBI Renewal
open Capacity Space CrossingCost
open Settlement.SourceOwnedSettlementCompiler
open ConstructiveRoot.RootInquiryCompletion
open M3FiniteExchangeFixture M3ExchangeSettlementPriceRegression
open M9ProofCarryingRenewalInquiryRoot
open M14UBIExitCapacityFixture
open M14UBIProofCarryingRootRestriction
open M14UBIPeriodicRootHistory
open M14UBIPeriodicActualServiceCapacity
open M14EssentialAccessRelationFixture
open M14EssentialAccessSectorRegression
open M14CaptureResponsibilityDispositionRegression
open M14GeneratedEconomicDisposition
open M14ActionableFuturePortfolio
open M14PortfolioMaintenanceDeath
open M14PortfolioCaptureDeath
open M14SourceEssentialServiceRestoration
open M14PeriodicEssentialServiceRestoration
open M14ProofCarryingExitRepairRegression
open M14ProofCarryingExitRepairRenewalRegression
open M14TenureCaptureRouteRepairNoGoRegression
open M14UBISelfU8SameRootRegression

/-! ## Pointwise source-strict readings -/

theorem positive_capacity_does_not_prevent_maintenance_death
    (depth : Nat) :
    Nonempty (SourceGeneratedPortfolioMaintenanceDeathAt depth
      (stablePortfolioSourceAt depth)) ∧
      Nonempty (PeriodicSourceBackedPaymentAt depth) ∧
      Nonempty (SourceGeneratedStableEssentialDomainActionableAt
        depth tenureAuthority) ∧
      IsEmpty (SourceGeneratedStableDomainServiceIncidenceAt depth
        (exactEssentialAccessSeed .health)) ∧
      IsEmpty (CompletePortfolioAt depth (stablePortfolioSourceAt depth)) ∧
      (stableGeometryCompilerAt depth).actionableExitCapacity = 1 :=
  let death := portfolioMaintenanceDeathAt depth
  ⟨⟨death⟩, ⟨death.stable.paymentOccurrence⟩,
    ⟨death.tenureActionable⟩, death.healthServiceEmpty,
    death.completePortfolioEmpty, death.exactCapacity⟩

theorem full_services_do_not_prevent_capture_death
    (depth : Nat) :
    Nonempty (SourceGeneratedPortfolioCaptureDeathAt depth
      (fullPortfolioSourceAt depth) fullCapture) ∧
      Nonempty (SourceGeneratedEssentialDomainActionableAt
        depth tenureAuthority) ∧
      Nonempty (SourceGeneratedEssentialDomainActionableAt
        depth healthAuthority) ∧
      IsEmpty (CapturedActionableFuturePortfolioAt depth) ∧
      (geometryCompilerAt depth).actionableExitCapacity = 1 ∧
      (capturedGeometryCompilerAt depth).actionableExitCapacity = 0 ∧
      Nonempty (OpenSettlementAt.ActivatedResidualConsumerAt
        (exactOpenSettlement exactResidualActivation)) ∧
      Nonempty (SourceOwnsResponsibilityIncidence V
        (P.boundarySource
          capturedProgram.purchasingPowerStanding.activatedConsumer.activation)
        (exactOpenSettlement exactResidualActivation).obligation) :=
  let death := portfolioCaptureDeathAt depth
  ⟨⟨death⟩, ⟨death.tenureServiceLive⟩,
    ⟨death.healthServiceLive⟩, death.capturedPortfolioEmpty,
    death.capacityCollapse.1, death.capacityCollapse.2,
    death.activatedResidualConsumer, death.sourceOwnedResidual⟩

/-- Strong same-root cause theorem.  The distinction is witnessed by exact
source prefixes/service fibres and capture compilers, not a new death tag. -/
theorem maintenance_capture_causes_are_source_strict
    (depth : Nat) :
    let maintenance := portfolioMaintenanceDeathAt depth
    let capture := portfolioCaptureDeathAt depth
    maintenance.stable.paymentOccurrence =
        capture.fullServices.paymentOccurrence ∧
      maintenance.stable.paymentOccurrence.rootOccurrence =
        capture.fullServices.paymentOccurrence.rootOccurrence ∧
      stablePrefixAt depth ≠ anomiePrefixAt depth ∧
      fullPortfolioSourceAt depth ≠ stablePortfolioSourceAt depth ∧
      ¬ noCapture.Captures ExitFutureCode.leave ∧
      fullCapture.Captures ExitFutureCode.leave ∧
      IsEmpty (SourceGeneratedStableDomainServiceIncidenceAt depth
        (exactEssentialAccessSeed .health)) ∧
      Nonempty (SourceGeneratedEssentialDomainActionableAt
        depth healthAuthority) ∧
      (stableGeometryCompilerAt depth).actionableExitCapacity = 1 ∧
      (capturedGeometryCompilerAt depth).actionableExitCapacity = 0 ∧
      Nonempty (OpenSettlementAt.ActivatedResidualConsumerAt
        (exactOpenSettlement exactResidualActivation)) ∧
      Nonempty (SourceOwnsResponsibilityIncidence V
        (P.boundarySource
          capturedProgram.purchasingPowerStanding.activatedConsumer.activation)
        (exactOpenSettlement exactResidualActivation).obligation) := by
  let maintenance := portfolioMaintenanceDeathAt depth
  let capture := portfolioCaptureDeathAt depth
  exact ⟨rfl, rfl, stable_anomie_prefixes_distinct depth,
    full_stable_sources_distinct depth, maintenance.uncaptured,
    capture.captured, maintenance.healthServiceEmpty,
    ⟨capture.healthServiceLive⟩, maintenance.exactCapacity,
    capture.capacityCollapse.2, capture.activatedResidualConsumer,
    capture.sourceOwnedResidual⟩

/-! ## Local death is not whole-root death -/

theorem every_local_death_is_nonterminal (depth : Nat) :
    IsEmpty (SourceGeneratedGroundedEconomicTerminalAt
      (tenureRepairExposureAt depth) (tenureEconomicImageAt depth) none) ∧
      IsEmpty (EconomicDispositionAt
        (tenureRepairExposureAt depth) (tenureEconomicImageAt depth) none) ∧
      (jointRoot.toAuthoritativeRoot.toRoot.evolutionAt
        (rootVisitAt depth).current).nextCurrent? =
          some (rootVisitAt depth).current :=
  let maintenance := portfolioMaintenanceDeathAt depth
  let capture := portfolioCaptureDeathAt depth
  ⟨maintenance.groundedTerminalEmpty,
    fixedRoot_noneLandingDisposition_isEmpty _ _,
    capture.actualRootSuccessor⟩

/-! ## Generated exits -/

theorem maintenance_death_generates_next_visit_restoration_responsibility
    (depth : Nat) :
    let death := portfolioMaintenanceDeathAt depth
    Nonempty (SourceGeneratedMaintenanceRestorationTransportAt death) ∧
      IsEmpty (CompletePortfolioAt depth (stablePortfolioSourceAt depth)) ∧
      Nonempty (CompletePortfolioAt (depth + 1)
        (fullPortfolioSourceAt (depth + 1))) ∧
      temporalVisitAt depth ≠ temporalVisitAt (depth + 1) ∧
      (stableGeometryCompilerAt depth).actionableExitCapacity = 1 ∧
      (geometryCompilerAt (depth + 1)).actionableExitCapacity = 1 := by
  let death := portfolioMaintenanceDeathAt depth
  let transport := maintenanceRestorationTransportAt death
  exact ⟨⟨transport⟩, transport.sourcePortfolioEmpty,
    transport.targetPortfolioLive, transport.adjacentVisitsDistinct,
    transport.sourceCapacityStillPositive, transport.targetCapacityPositive⟩

/-- The transporter responsibility is now discharged by an independently
installed action-bearing service coordinate.  Cause, root occurrence, row,
whole ledger, next, and restored health service commute. -/
theorem maintenance_death_generates_actual_service_restoration
    (depth : Nat) :
    let death := portfolioMaintenanceDeathAt depth
    let restoration := sourceGeneratedEssentialServiceRestorationAt depth
    death.stable.paymentOccurrence.rootOccurrence =
        restoration.rootOccurrence ∧
      death.healthServiceEmpty =
        stableHealthDomainServiceIncidence_isEmpty depth ∧
      restoration.sourceHealthUnitMissing =
        healthServiceUnit_not_mem_maintenanceSource ∧
      maintenanceSourceUnits = (stablePrefixAt depth).units ∧
      essentialDomainServiceUnitAt (exactEssentialAccessSeed .health) =
        SourceAppliedEssentialServiceRestorationAt.unitAt
          restoration.installed.payload.disposition ∧
      restoration.installed.payload.sourceEntry =
        RootInquiryU8CompletionRegression.entry ∧
      HEq restoration.installed.payload.selectedRow
        (installedUBIAt depth).payload.selectedRow ∧
      restoration.applied.selectedWrite.sourceRow.CommutesWithWorld ∧
      restoration.applied.wholeLedgerWriteBack =
        (jointRoot.toAuthoritativeRoot.toLedgerRoot
          |>.generatedAtTemporalVisit
            (temporalVisitAt depth)).wholeLedgerWriteBack ∧
      restoration.installed.RootAnswerAndNextFactorizes ∧
      restoration.applied.generatedNext =
        jointRoot.generatedNextCurrentAt (temporalVisitAt depth) ∧
      restoration.applied.generatedNext.visit =
        temporalVisitAt (depth + 1) ∧
      Nonempty (SourceGeneratedActionableFuturePortfolioAt (depth + 1)) ∧
      (anomiePhaseAt (depth + 1)).served.get
          restoration.targetHealth.serviceIncidence.slot =
        SourceAppliedEssentialServiceRestorationAt.unitAt
          restoration.installed.payload.disposition ∧
      (geometryCompilerAt (depth + 1)).actionableExitCapacity = 1 := by
  let death := portfolioMaintenanceDeathAt depth
  let restoration := sourceGeneratedEssentialServiceRestorationAt depth
  exact ⟨death.paymentRootExact.trans restoration.rootOccurrenceExact.symm,
    Subsingleton.elim _ _, Subsingleton.elim _ _,
    restoration.sourceUnitsExact, rfl,
    restoration.sourceEntryExact,
    restoration.selectedRowSharedWithUBI,
    restoration.selectedWriteCommutes,
    restoration.wholeLedgerExact,
    restoration.rootFactorization,
    restoration.generatedNextExact,
    restoration.nextVisitExact,
    ⟨restoration.targetPortfolio⟩,
    restoration.targetHealthServesActionUnit,
    restoration.targetCapacityExact⟩

/-- Regression guard against post-hoc attachment: the actual restoration
carrier itself owns the exact maintenance-death source it consumes. -/
theorem actual_restoration_contains_its_maintenance_death
    (depth : Nat) :
    let restoration := sourceGeneratedEssentialServiceRestorationAt depth
    Nonempty (SourceGeneratedPortfolioMaintenanceDeathAt depth
      (stablePortfolioSourceAt depth)) ∧
      restoration.sourceDeath.stable.paymentOccurrence.rootOccurrence =
        restoration.rootOccurrence ∧
      IsEmpty (SourceGeneratedStableDomainServiceIncidenceAt depth
        (exactEssentialAccessSeed .health)) ∧
      IsEmpty (CompletePortfolioAt depth (stablePortfolioSourceAt depth)) ∧
      (stableGeometryCompilerAt depth).actionableExitCapacity = 1 := by
  let restoration := sourceGeneratedEssentialServiceRestorationAt depth
  exact ⟨⟨restoration.sourceDeath⟩,
    restoration.sourceDeathRootExact,
    restoration.sourceDeathHealthEmpty,
    restoration.sourceDeathPortfolioEmpty,
    restoration.sourceDeathCapacityExact⟩

theorem service_and_capture_repairs_share_next_but_not_authority
    (depth : Nat) :
    let service := sourceGeneratedEssentialServiceRestorationAt depth
    let captureRepair := actualOrdinaryRenewalAt depth
    service.applied.generatedNext = captureRepair.generatedNext ∧
      jointEssentialServiceRestorationProjection ≠ jointUBIProjection ∧
      service.installed.payload.disposition =
        sourceGeneratedHealthServiceRestoration ∧
      captureRepair.source.installed.payload.disposition =
        sourceGeneratedUBIDisposition ∧
      canonicalRepairAt (tenureCaptureOriginAt depth) = .removeCapture := by
  let service := sourceGeneratedEssentialServiceRestorationAt depth
  let captureRepair := actualOrdinaryRenewalAt depth
  exact ⟨service.generatedNextExact.trans
      captureRepair.generatedNext_eq_rootCompiler.symm,
    service.serviceProjectionDistinctFromUBI,
    service.actionExact,
    captureRepair.source.exactDisposition,
    captureRepair.repair_eq_removeCapture⟩

theorem fixed_service_ordinary_next_is_not_u8_revised_next :
    let service := sourceGeneratedEssentialServiceRestorationAt 0
    service.applied.generatedNext =
        jointRoot.generatedNextCurrentAt (temporalVisitAt 0) ∧
      (⟨M9ProofCarryingRenewalInquiryRoot.N,
        jointRoot.generatedNextCurrentAt (temporalVisitAt 0)⟩ :
        AnyAuthoritativeRootCurrent) ≠
        M13SelfU8Regression.selfU8.revisedNext := by
  let service := sourceGeneratedEssentialServiceRestorationAt 0
  exact ⟨service.generatedNextExact,
    ubi_old_next_ne_selfU8_revisedNext⟩

theorem fixed_capture_death_has_distinct_ordinary_and_u8_exits :
    let death := portfolioCaptureDeathAt 0
    Nonempty (SourceGeneratedCaptureDeathPolicyU8At death) ∧
      Nonempty (SourceGeneratedOrdinaryEconomicDispositionAt
        (tenureRepairExposureAt 0) (tenureEconomicImageAt 0)
          (ordinaryEconomicLandingAt 0)) ∧
      Nonempty (SourceGeneratedRequiresU8EconomicDispositionAt
        (tenureRepairExposureAt 0) (tenureEconomicImageAt 0)
          revolutionaryEconomicLanding) ∧
      ordinaryEconomicLandingAt 0 ≠ revolutionaryEconomicLanding := by
  let death := portfolioCaptureDeathAt 0
  let exits := captureDeathPolicyU8At death
  exact ⟨⟨exits⟩, ⟨exits.ordinary⟩,
    ⟨exits.requiresU8⟩, exits.landingsDistinct⟩

/-! ## Exact-index negative controls -/

theorem death_sources_and_capture_authority_cannot_be_swapped
    (depth : Nat) :
    IsEmpty (SourceGeneratedPortfolioMaintenanceDeathAt depth
      (fullPortfolioSourceAt depth)) ∧
      IsEmpty (SourceGeneratedPortfolioCaptureDeathAt depth
        (stablePortfolioSourceAt depth) fullCapture) ∧
      IsEmpty (SourceGeneratedPortfolioCaptureDeathAt depth
        (fullPortfolioSourceAt depth) noCapture) :=
  ⟨full_source_cannot_generate_maintenance_death depth,
    stable_source_cannot_generate_capture_death depth,
    uncaptured_compiler_cannot_generate_capture_death depth⟩

/-! ## Canonical certificate -/

structure ProofCarryingPortfolioDeathCertificate : Prop where
  everyMaintenanceDeath : ∀ depth : Nat,
    Nonempty (SourceGeneratedPortfolioMaintenanceDeathAt depth
      (stablePortfolioSourceAt depth))
  everyCaptureDeath : ∀ depth : Nat,
    Nonempty (SourceGeneratedPortfolioCaptureDeathAt depth
      (fullPortfolioSourceAt depth) fullCapture)
  everyPositiveCapacityMaintenanceDeath : ∀ depth : Nat,
    Nonempty (SourceGeneratedPortfolioMaintenanceDeathAt depth
        (stablePortfolioSourceAt depth)) ∧
      Nonempty (PeriodicSourceBackedPaymentAt depth) ∧
      Nonempty (SourceGeneratedStableEssentialDomainActionableAt
        depth tenureAuthority) ∧
      IsEmpty (SourceGeneratedStableDomainServiceIncidenceAt depth
        (exactEssentialAccessSeed .health)) ∧
      IsEmpty (CompletePortfolioAt depth (stablePortfolioSourceAt depth)) ∧
      (stableGeometryCompilerAt depth).actionableExitCapacity = 1
  everyFullServiceCaptureDeath : ∀ depth : Nat,
    Nonempty (SourceGeneratedPortfolioCaptureDeathAt depth
        (fullPortfolioSourceAt depth) fullCapture) ∧
      Nonempty (SourceGeneratedEssentialDomainActionableAt
        depth tenureAuthority) ∧
      Nonempty (SourceGeneratedEssentialDomainActionableAt
        depth healthAuthority) ∧
      IsEmpty (CapturedActionableFuturePortfolioAt depth) ∧
      (geometryCompilerAt depth).actionableExitCapacity = 1 ∧
      (capturedGeometryCompilerAt depth).actionableExitCapacity = 0 ∧
      Nonempty (OpenSettlementAt.ActivatedResidualConsumerAt
        (exactOpenSettlement exactResidualActivation)) ∧
      Nonempty (SourceOwnsResponsibilityIncidence V
        (P.boundarySource
          capturedProgram.purchasingPowerStanding.activatedConsumer.activation)
        (exactOpenSettlement exactResidualActivation).obligation)
  everyCauseStrict : ∀ depth : Nat,
    let maintenance := portfolioMaintenanceDeathAt depth
    let capture := portfolioCaptureDeathAt depth
    maintenance.stable.paymentOccurrence =
        capture.fullServices.paymentOccurrence ∧
      maintenance.stable.paymentOccurrence.rootOccurrence =
        capture.fullServices.paymentOccurrence.rootOccurrence ∧
      stablePrefixAt depth ≠ anomiePrefixAt depth ∧
      fullPortfolioSourceAt depth ≠ stablePortfolioSourceAt depth ∧
      ¬ noCapture.Captures ExitFutureCode.leave ∧
      fullCapture.Captures ExitFutureCode.leave ∧
      IsEmpty (SourceGeneratedStableDomainServiceIncidenceAt depth
        (exactEssentialAccessSeed .health)) ∧
      Nonempty (SourceGeneratedEssentialDomainActionableAt
        depth healthAuthority) ∧
      (stableGeometryCompilerAt depth).actionableExitCapacity = 1 ∧
      (capturedGeometryCompilerAt depth).actionableExitCapacity = 0 ∧
      Nonempty (OpenSettlementAt.ActivatedResidualConsumerAt
        (exactOpenSettlement exactResidualActivation)) ∧
      Nonempty (SourceOwnsResponsibilityIncidence V
        (P.boundarySource
          capturedProgram.purchasingPowerStanding.activatedConsumer.activation)
        (exactOpenSettlement exactResidualActivation).obligation)
  everyDeathNonterminal : ∀ depth : Nat,
    IsEmpty (SourceGeneratedGroundedEconomicTerminalAt
      (tenureRepairExposureAt depth) (tenureEconomicImageAt depth) none) ∧
      IsEmpty (EconomicDispositionAt
        (tenureRepairExposureAt depth) (tenureEconomicImageAt depth) none) ∧
      (jointRoot.toAuthoritativeRoot.toRoot.evolutionAt
        (rootVisitAt depth).current).nextCurrent? =
          some (rootVisitAt depth).current
  everyMaintenanceRestorationResponsibility : ∀ depth : Nat,
    Nonempty (SourceGeneratedMaintenanceRestorationTransportAt
      (portfolioMaintenanceDeathAt depth))
  everyActualMaintenanceRestoration : ∀ depth : Nat,
    Nonempty (SourceGeneratedProofCarryingEssentialServiceRestorationAt depth)
  everyMaintenanceDeathActualCommuting : ∀ depth : Nat,
    let death := portfolioMaintenanceDeathAt depth
    let restoration := sourceGeneratedEssentialServiceRestorationAt depth
    death.stable.paymentOccurrence.rootOccurrence =
        restoration.rootOccurrence ∧
      death.healthServiceEmpty =
        stableHealthDomainServiceIncidence_isEmpty depth ∧
      restoration.sourceHealthUnitMissing =
        healthServiceUnit_not_mem_maintenanceSource ∧
      maintenanceSourceUnits = (stablePrefixAt depth).units ∧
      essentialDomainServiceUnitAt (exactEssentialAccessSeed .health) =
        SourceAppliedEssentialServiceRestorationAt.unitAt
          restoration.installed.payload.disposition ∧
      restoration.installed.payload.sourceEntry =
        RootInquiryU8CompletionRegression.entry ∧
      HEq restoration.installed.payload.selectedRow
        (installedUBIAt depth).payload.selectedRow ∧
      restoration.applied.selectedWrite.sourceRow.CommutesWithWorld ∧
      restoration.applied.wholeLedgerWriteBack =
        (jointRoot.toAuthoritativeRoot.toLedgerRoot
          |>.generatedAtTemporalVisit
            (temporalVisitAt depth)).wholeLedgerWriteBack ∧
      restoration.installed.RootAnswerAndNextFactorizes ∧
      restoration.applied.generatedNext =
        jointRoot.generatedNextCurrentAt (temporalVisitAt depth) ∧
      restoration.applied.generatedNext.visit =
        temporalVisitAt (depth + 1) ∧
      Nonempty (SourceGeneratedActionableFuturePortfolioAt (depth + 1)) ∧
      (anomiePhaseAt (depth + 1)).served.get
          restoration.targetHealth.serviceIncidence.slot =
        SourceAppliedEssentialServiceRestorationAt.unitAt
          restoration.installed.payload.disposition ∧
      (geometryCompilerAt (depth + 1)).actionableExitCapacity = 1
  actualRestorationOwnsMaintenanceDeath : ∀ depth : Nat,
    let restoration := sourceGeneratedEssentialServiceRestorationAt depth
    Nonempty (SourceGeneratedPortfolioMaintenanceDeathAt depth
      (stablePortfolioSourceAt depth)) ∧
      restoration.sourceDeath.stable.paymentOccurrence.rootOccurrence =
        restoration.rootOccurrence ∧
      IsEmpty (SourceGeneratedStableDomainServiceIncidenceAt depth
        (exactEssentialAccessSeed .health)) ∧
      IsEmpty (CompletePortfolioAt depth (stablePortfolioSourceAt depth)) ∧
      (stableGeometryCompilerAt depth).actionableExitCapacity = 1
  serviceAndCaptureOrdinaryDistinctAuthority : ∀ depth : Nat,
    let service := sourceGeneratedEssentialServiceRestorationAt depth
    let captureRepair := actualOrdinaryRenewalAt depth
    service.applied.generatedNext = captureRepair.generatedNext ∧
      jointEssentialServiceRestorationProjection ≠ jointUBIProjection ∧
      service.installed.payload.disposition =
        sourceGeneratedHealthServiceRestoration ∧
      captureRepair.source.installed.payload.disposition =
        sourceGeneratedUBIDisposition ∧
      canonicalRepairAt (tenureCaptureOriginAt depth) = .removeCapture
  fixedServiceNextDistinctFromU8 :
    let service := sourceGeneratedEssentialServiceRestorationAt 0
    service.applied.generatedNext =
        jointRoot.generatedNextCurrentAt (temporalVisitAt 0) ∧
      (⟨M9ProofCarryingRenewalInquiryRoot.N,
        jointRoot.generatedNextCurrentAt (temporalVisitAt 0)⟩ :
        AnyAuthoritativeRootCurrent) ≠
        M13SelfU8Regression.selfU8.revisedNext
  wrongDomainActionEmpty : IsEmpty
    (SourceAppliedEssentialServiceRestorationAt
      M10OccurrenceCapacityProcessFixture.focalSeed
      (exactEssentialAccessSeed .tenure) healthServiceUnit)
  wrongUnitActionEmpty : IsEmpty
    (SourceAppliedEssentialServiceRestorationAt
      M10OccurrenceCapacityProcessFixture.focalSeed
      healthDomainSeed M10OccurrenceCapacityProcessFixture.firstUnit)
  fixedCaptureOrdinaryAndU8 : Nonempty
    (SourceGeneratedCaptureDeathPolicyU8At (portfolioCaptureDeathAt 0))
  exactIndexNegatives : ∀ depth : Nat,
    IsEmpty (SourceGeneratedPortfolioMaintenanceDeathAt depth
      (fullPortfolioSourceAt depth)) ∧
      IsEmpty (SourceGeneratedPortfolioCaptureDeathAt depth
        (stablePortfolioSourceAt depth) fullCapture) ∧
      IsEmpty (SourceGeneratedPortfolioCaptureDeathAt depth
        (fullPortfolioSourceAt depth) noCapture)

theorem proofCarryingPortfolioDeathDirectConsumer :
    ProofCarryingPortfolioDeathCertificate where
  everyMaintenanceDeath := every_generated_period_has_maintenance_death
  everyCaptureDeath := every_generated_period_has_capture_death
  everyPositiveCapacityMaintenanceDeath :=
    positive_capacity_does_not_prevent_maintenance_death
  everyFullServiceCaptureDeath := full_services_do_not_prevent_capture_death
  everyCauseStrict := maintenance_capture_causes_are_source_strict
  everyDeathNonterminal := every_local_death_is_nonterminal
  everyMaintenanceRestorationResponsibility :=
    every_maintenance_death_generates_restoration_transport
  everyActualMaintenanceRestoration :=
    every_generated_period_has_actual_service_restoration
  everyMaintenanceDeathActualCommuting :=
    maintenance_death_generates_actual_service_restoration
  actualRestorationOwnsMaintenanceDeath :=
    actual_restoration_contains_its_maintenance_death
  serviceAndCaptureOrdinaryDistinctAuthority :=
    service_and_capture_repairs_share_next_but_not_authority
  fixedServiceNextDistinctFromU8 :=
    fixed_service_ordinary_next_is_not_u8_revised_next
  wrongDomainActionEmpty := tenureDomainRestoration_isEmpty
  wrongUnitActionEmpty := firstUnitRestoration_isEmpty
  fixedCaptureOrdinaryAndU8 :=
    fixed_capture_death_generates_ordinary_and_u8_exits
  exactIndexNegatives := death_sources_and_capture_authority_cannot_be_swapped

end
end M14ProofCarryingPortfolioDeathRegression
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingPortfolioDeathRegression.maintenance_capture_causes_are_source_strict
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingPortfolioDeathRegression.every_local_death_is_nonterminal
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingPortfolioDeathRegression.maintenance_death_generates_actual_service_restoration
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingPortfolioDeathRegression.actual_restoration_contains_its_maintenance_death
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingPortfolioDeathRegression.service_and_capture_repairs_share_next_but_not_authority
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingPortfolioDeathRegression.proofCarryingPortfolioDeathDirectConsumer
