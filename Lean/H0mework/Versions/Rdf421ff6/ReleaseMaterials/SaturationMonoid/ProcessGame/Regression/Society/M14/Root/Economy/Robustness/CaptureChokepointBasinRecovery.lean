import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Root.Economy.Attractor.MinimalEconomicViabilityHittingTime
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Consumer.Capture.StructuralRentCaptureRegression
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Consumer.Economy.Portfolio.ProofCarryingActionableFuturePortfolioRegression

/-!
# M14 structural-capture chokepoint and basin recovery

Full capture does more than make the dependent portfolio empty: it removes
the feasible edge of every generated essential-access domain even though
each domain's relation, payment, route, service, and crossing remain live.
The same source-generated structural-rent capture retains its settlement
responsibility and carries the existing action-bearing remove-capture edge
back into the viable basin.

No sector list, chokepoint graph, perturbation registry, viable-to-capture
arrow, root, ledger, rank, optimizer, or completed future is introduced.
The public producer accepts only `depth`.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14CaptureChokepointBasinRecovery

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations Exchange Settlement Price Money UBI Policy
open Renewal Capacity Space CrossingCost
open Settlement.SourceOwnedSettlementCompiler
open UBI.Capture
open M3FiniteExchangeFixture M3ExchangeSettlementPriceRegression
open M9ProofCarryingRenewalInquiryRoot
open M14UBIExitCapacityFixture
open M14UBIProofCarryingRootRestriction
open M14UBIPeriodicRootHistory
open M14UBIPeriodicActualServiceCapacity
open M14CaptureResponsibilityDispositionRegression
open M14ZeroCapacityCausalNonidentifiabilityRegression
open M14EssentialAccessRelationFixture
open M14EssentialAccessPaymentPurposeLaw
open M14EssentialAccessSectorRegression
open M14ActionableFuturePortfolio
open M14GeneratedEconomicDisposition
open M14PortfolioMaintenanceDeath
open M14PortfolioCaptureDeath
open M14TenureCaptureRouteRepairNoGoRegression
open M14ProofCarryingExitRepairRegression
open M14PeriodicDeathRepairNormalization
open M14PeriodicViabilityRenewalReceipt
open M14EconomicViability
open M14AdjacentEconomicViabilityBoundary
open M14ActualEconomicViabilityPath
open M14MinimalEconomicViabilityHittingTime
open M14StructuralRentCaptureRegression
open M14ProofCarryingActionableFuturePortfolioRegression

abbrev CaptureDeathAt (depth : Nat) :=
  SourceGeneratedPortfolioCaptureDeathAt depth
    (fullPortfolioSourceAt depth) fullCapture

abbrev StructuralRentAt (depth : Nat) :=
  PeriodicStructuralRentCaptureAt depth
    (periodicSourceBackedPaymentAt depth)

abbrev RecoveryTargetAt (depth : Nat) :=
  EconomicViabilityAt (depth + 1)
    (fullPortfolioSourceAt (depth + 1)) noCapture

/-! ## Domainwise cut, stronger than product emptiness -/

/-- Full capture blocks every domain-specific feasible edge.  The domain is
the existing generated `EssentialAccessRelationAuthority`, not a new sector
registry. -/
theorem fullCapture_blocks_every_essential_domain
    (depth : Nat) (domain : EssentialAccessRelationAuthority) :
    IsEmpty (M14PortfolioCaptureDeath.CapturedDomainActionableAt
      depth domain) :=
  ⟨fun edge => by
    have noExit : IsEmpty capturedProgram.exitCone.ActionableExitAt :=
      capturedProgram.exitCone.isEmpty_actionableExit_iff_fullPriceCapture.mpr
        capturedProgram_fullPriceCapture
    exact noExit.false ⟨ExitFutureCode.leave, edge.codeSurvives⟩⟩

theorem every_uncaptured_essential_domain_is_live
    (depth : Nat) (domain : EssentialAccessRelationAuthority) :
    Nonempty (SourceGeneratedEssentialDomainActionableAt depth domain) :=
  ⟨sourceGeneratedEssentialDomainActionableAt depth domain⟩

/-! ## Source-generated chokepoint cell -/

/-- One source-generated structural capture whose cut lies in the already
generated capture-repair basin.  `rent`, `death`, `boundary`, and `target`
are dependent indices; the public producer computes all four. -/
structure SourceGeneratedCaptureChokepointBasinRecoveryAt
    (depth : Nat)
    (rent : StructuralRentAt depth)
    (death : CaptureDeathAt depth)
    (boundary : PeriodicViabilityBoundaryAt depth)
    (target : RecoveryTargetAt depth) : Type 18 where
  private mk ::
  rentExact : rent = periodicStructuralRentCaptureAt depth
  deathExact : death = portfolioCaptureDeathAt depth
  boundaryExact : boundary =
    sourceGeneratedAdjacentEconomicViabilityBoundaryAt depth
  targetExact : target = sourceGeneratedPeriodicEconomicViabilityAt depth
  rootExact : death.fullServices.paymentOccurrence.rootOccurrence =
    jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
      (temporalVisitAt depth)
  rentRootExact :
    (periodicSourceBackedPaymentAt depth).rootOccurrence =
      jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
        (temporalVisitAt depth)
  rentDeathRootShared :
    (periodicSourceBackedPaymentAt depth).rootOccurrence =
      death.fullServices.paymentOccurrence.rootOccurrence
  structuralPurpose : SourceGeneratedStructuralRentCaptureAt depth
  structuralPurposeExact : structuralPurpose = rent.structuralRent
  purposeRelationExact :
    essentialAccessPaymentPurposeCompiler.purposeRelation
      exactResidualActivation = tenureRelation
  tenurePhaseGenerated :
    essentialAccessPaymentPurposeCompiler.purposePhase
      exactResidualActivation = EssentialAccessSector.tenure
  tenureRoleGenerated :
    essentialAccessRelationCompiler.RelationRoleAt tenureActor tenureRelation
      .target .tenureProvider
  liveBeforeCapture : (domain : EssentialAccessRelationAuthority) →
    SourceGeneratedEssentialDomainActionableAt depth domain
  allDomainsCut : (domain : EssentialAccessRelationAuthority) →
    IsEmpty (M14PortfolioCaptureDeath.CapturedDomainActionableAt
      depth domain)
  tenureHealthCrossingsDistinct :
    domainCrossingAt depth tenureAuthority ≠
      domainCrossingAt depth healthAuthority
  paymentPreserved : capturedProgram.payment = exitCapacityProgram.payment
  purchasingPowerStandingPreserved :
    capturedProgram.purchasingPowerStanding =
      exitCapacityProgram.purchasingPowerStanding
  everyRoutePreserved : ∀ code crossing,
    (capturedGeometryCompilerAt depth).RoutesAt code crossing =
      (geometryCompilerAt depth).RoutesAt code crossing
  actualServiceRetained : Nonempty (ExactServedCrossingDebitedRunAt
    (anomiePhaseAt depth) M10OccurrenceCapacityDebitedRunFixture.debited
      (serviceCompilerAt depth))
  commonCodeCaptured : fullCapture.Captures ExitFutureCode.leave
  exactSettlement :
    fullCapture.captureSettlement ExitFutureCode.leave leave_is_captured =
      exactOpenSettlement exactResidualActivation
  residualBearerRetained :
    OpenSettlementAt.residualBearer
        (fullCapture.captureSettlement ExitFutureCode.leave
          leave_is_captured) =
      OpenSettlementAt.residualBearer
        (exactOpenSettlement exactResidualActivation)
  generatedBeneficiary :
    OpenSettlementAt.protectedInterest
        (fullCapture.captureSettlement ExitFutureCode.leave
          leave_is_captured) =
      exchangeLaw.protectedInterestOfActor tenureActor
  activatedResidualConsumer : Nonempty
    (OpenSettlementAt.ActivatedResidualConsumerAt
      (exactOpenSettlement exactResidualActivation))
  sourceOwnedResidual : Nonempty (SourceOwnsResponsibilityIncidence V
    (P.boundarySource
      capturedProgram.purchasingPowerStanding.activatedConsumer.activation)
    (exactOpenSettlement exactResidualActivation).obligation)
  repairExact : boundary.entry.normalization.captureDeath.ordinaryRepair =
    death.ordinaryRepair
  repairIsRemoveCapture :
    canonicalRepairAt (tenureCaptureOriginAt depth) =
      Policy.ExactExitRepair.removeCapture
  repairRowSharedWithUBI : HEq
    death.ordinaryRepair.renewal.source.installed.payload.selectedRow
      (installedUBIAt depth).payload.selectedRow
  repairSelectedWriteCommutes :
    death.ordinaryRepair.renewal.ordinarySelectedWrite.sourceRow
      |>.CommutesWithWorld
  repairWholeLedgerExact :
    death.ordinaryRepair.renewal.wholeLedgerWriteBack =
      (jointRoot.toAuthoritativeRoot.toLedgerRoot
        |>.generatedAtTemporalVisit
          (temporalVisitAt depth)).wholeLedgerWriteBack
  repairNextExact : death.ordinaryRepair.renewal.generatedNext =
    jointRoot.generatedNextCurrentAt (temporalVisitAt depth)
  recoveryEdge : Nonempty
    (captureConfigurationAt depth ⟶ repairedConfigurationAt depth)
  targetDispositionExact : HEq target.toDisposition
    boundary.entry.viableDisposition
  targetRootExact : target.portfolio.paymentOccurrence.rootOccurrence =
    jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
      (temporalVisitAt (depth + 1))
  lawSurfacePreserved :
    boundary.entry.normalization.normalForm.generatedNext.root.source.lawSurface =
      jointRoot.source.base.lawSurface

namespace SourceGeneratedCaptureChokepointBasinRecoveryAt

theorem rent
    {depth : Nat} {rent : StructuralRentAt depth}
    {death : CaptureDeathAt depth}
    {boundary : PeriodicViabilityBoundaryAt depth}
    {target : RecoveryTargetAt depth}
    (_cell : SourceGeneratedCaptureChokepointBasinRecoveryAt
      depth rent death boundary target) : StructuralRentAt depth := rent

def death
    {depth : Nat} {rent : StructuralRentAt depth}
    {death : CaptureDeathAt depth}
    {boundary : PeriodicViabilityBoundaryAt depth}
    {target : RecoveryTargetAt depth}
    (_cell : SourceGeneratedCaptureChokepointBasinRecoveryAt
      depth rent death boundary target) := death

def boundary
    {depth : Nat} {rent : StructuralRentAt depth}
    {death : CaptureDeathAt depth}
    {boundary : PeriodicViabilityBoundaryAt depth}
    {target : RecoveryTargetAt depth}
    (_cell : SourceGeneratedCaptureChokepointBasinRecoveryAt
      depth rent death boundary target) := boundary

def target
    {depth : Nat} {rent : StructuralRentAt depth}
    {death : CaptureDeathAt depth}
    {boundary : PeriodicViabilityBoundaryAt depth}
    {target : RecoveryTargetAt depth}
    (_cell : SourceGeneratedCaptureChokepointBasinRecoveryAt
      depth rent death boundary target) := target

end SourceGeneratedCaptureChokepointBasinRecoveryAt

/-- Sole depth-only producer. -/
def sourceGeneratedCaptureChokepointBasinRecoveryAt (depth : Nat) :
    SourceGeneratedCaptureChokepointBasinRecoveryAt depth
      (periodicStructuralRentCaptureAt depth)
      (portfolioCaptureDeathAt depth)
      (sourceGeneratedAdjacentEconomicViabilityBoundaryAt depth)
      (sourceGeneratedPeriodicEconomicViabilityAt depth) := by
  let rent := periodicStructuralRentCaptureAt depth
  let death := portfolioCaptureDeathAt depth
  let boundary := sourceGeneratedAdjacentEconomicViabilityBoundaryAt depth
  let target := sourceGeneratedPeriodicEconomicViabilityAt depth
  let preserved := repairs_preserve_every_non_target_axis depth
  exact
    { rentExact := rfl
      deathExact := rfl
      boundaryExact := rfl
      targetExact := rfl
      rootExact := death.paymentRootExact
      rentRootExact := rent.exactTemporalOccurrence
      rentDeathRootShared :=
        rent.exactTemporalOccurrence.trans death.paymentRootExact.symm
      structuralPurpose := rent.structuralRent
      structuralPurposeExact := rfl
      purposeRelationExact := rent.structuralRent.purposeRelationExact
      tenurePhaseGenerated := rent.structuralRent.tenurePhaseGenerated
      tenureRoleGenerated := rent.structuralRent.tenureRoleGenerated
      liveBeforeCapture := death.fullServices.actionable
      allDomainsCut := fullCapture_blocks_every_essential_domain depth
      tenureHealthCrossingsDistinct :=
        tenure_health_crossings_are_distinct depth
      paymentPreserved := preserved.1
      purchasingPowerStandingPreserved := preserved.2.1
      everyRoutePreserved := preserved.2.2.2.2.2.1
      actualServiceRetained := rent.actualServiceRetained
      commonCodeCaptured := death.captured
      exactSettlement := death.exactSettlement
      residualBearerRetained := death.residualBearerRetained
      generatedBeneficiary := by
        rw [(installedTenureFailureAt depth).tenureActorIsCounterparty]
        exact death.generatedBeneficiary
      activatedResidualConsumer := death.activatedResidualConsumer
      sourceOwnedResidual := death.sourceOwnedResidual
      repairExact := rfl
      repairIsRemoveCapture := death.ordinaryRepairIsRemoveCapture
      repairRowSharedWithUBI := HEq.rfl
      repairSelectedWriteCommutes := death.ordinaryRepair.selectedWriteCommutes
      repairWholeLedgerExact := death.ordinaryRepair.wholeLedgerExact
      repairNextExact := death.ordinaryNextExact
      recoveryEdge := ⟨captureActionEdgeAt depth⟩
      targetDispositionExact := HEq.rfl
      targetRootExact := target.portfolio.rootOccurrenceExact
      lawSurfacePreserved := boundary.lawSurfacePreserved }

theorem every_generated_structural_capture_is_a_domainwise_chokepoint
    (depth : Nat) :
    Nonempty (SourceGeneratedCaptureChokepointBasinRecoveryAt depth
      (periodicStructuralRentCaptureAt depth)
      (portfolioCaptureDeathAt depth)
      (sourceGeneratedAdjacentEconomicViabilityBoundaryAt depth)
      (sourceGeneratedPeriodicEconomicViabilityAt depth)) :=
  ⟨sourceGeneratedCaptureChokepointBasinRecoveryAt depth⟩

/-! ## Basin consumer -/

theorem structural_capture_chokepoint_is_in_viability_basin
    (depth horizon : Nat) :
    (∀ domain : EssentialAccessRelationAuthority,
      Nonempty (SourceGeneratedEssentialDomainActionableAt depth domain) ∧
        IsEmpty (M14PortfolioCaptureDeath.CapturedDomainActionableAt
          depth domain)) ∧
      domainCrossingAt depth tenureAuthority ≠
        domainCrossingAt depth healthAuthority ∧
      Nonempty (SourceGeneratedStructuralRentCaptureAt depth) ∧
      Nonempty (captureConfigurationAt depth ⟶
        repairedConfigurationAt depth) ∧
      captureViabilityHittingTimeAt depth = 1 ∧
      (captureFiniteAttractorPathAt depth horizon).length = horizon + 1 ∧
      Nonempty ((repairedConfigurationAt (depth + horizon)).Viable) := by
  let cell := sourceGeneratedCaptureChokepointBasinRecoveryAt depth
  exact
    ⟨fun domain =>
        ⟨⟨cell.liveBeforeCapture domain⟩, cell.allDomainsCut domain⟩,
      cell.tenureHealthCrossingsDistinct,
      ⟨cell.structuralPurpose⟩,
      cell.recoveryEdge,
      captureViabilityHittingTime_eq_one depth,
      captureFiniteAttractorPath_length depth horizon,
      ⟨finiteContinuationTargetViabilityAt depth horizon⟩⟩

/-! ## Strong negative controls -/

/-- The current action graph contains no invented `noCapture → fullCapture`
shock.  Every existing edge advances one temporal depth, while the proposed
capture target stays at the source visit. -/
theorem current_quiver_has_no_viable_to_capture_shock (depth : Nat) :
    IsEmpty (repairedConfigurationAt depth ⟶
      captureConfigurationAt (depth + 1)) :=
  ⟨by
    rintro ⟨edgeDepth, boundary, action, edge⟩
    rcases action with repair | renewal
    · rcases repair with service | capture
      · have sourceDepth := congrArg Sigma.fst edge.sourceExact
        have targetDepth := congrArg Sigma.fst edge.targetExact
        change depth + 1 = edgeDepth at sourceDepth
        change depth + 1 = edgeDepth + 1 at targetDepth
        omega
      · have sourceDepth := congrArg Sigma.fst edge.sourceExact
        have targetDepth := congrArg Sigma.fst edge.targetExact
        change depth + 1 = edgeDepth at sourceDepth
        change depth + 1 = edgeDepth + 1 at targetDepth
        omega
    · have sourceDepth := congrArg Sigma.fst edge.sourceExact
      have targetDepth := congrArg Sigma.fst edge.targetExact
      change depth + 1 = edgeDepth + 1 at sourceDepth
      change depth + 1 = (edgeDepth + 1) + 1 at targetDepth
      omega⟩

theorem noCapture_cannot_generate_capture_chokepoint (depth : Nat) :
    IsEmpty (SourceGeneratedPortfolioCaptureDeathAt depth
      (fullPortfolioSourceAt depth) noCapture) :=
  uncaptured_compiler_cannot_generate_capture_death depth

theorem route_missing_is_not_capture_chokepoint_authority
    (depth : Nat) (domain : EssentialAccessRelationAuthority) :
    IsEmpty ((routeIncidenceMissingGeometryAt depth).RoutesAt
      ExitFutureCode.leave (domainCrossingAt depth domain)) ∧
      ¬ noCapture.Captures ExitFutureCode.leave :=
  ⟨route_incidence_missing_at depth ExitFutureCode.leave
      (domainCrossingAt depth domain),
    uncaptured_leave_has_no_capture_verdict⟩

theorem maintenance_failure_is_not_capture_chokepoint
    (depth : Nat) :
    (stableGeometryCompilerAt depth).actionableExitCapacity = 1 ∧
      IsEmpty (SourceGeneratedStableDomainServiceIncidenceAt depth
        (exactEssentialAccessSeed .health)) ∧
      ¬ noCapture.Captures ExitFutureCode.leave :=
  let death := portfolioMaintenanceDeathAt depth
  ⟨death.exactCapacity, death.healthServiceEmpty,
    uncaptured_leave_has_no_capture_verdict⟩

theorem fully_fulfilled_same_payment_has_no_chokepoint_rent
    (depth : Nat)
    (fully : FullyFulfilledExchangeAt settlementCompiler openOccurrence) :
    IsEmpty (RootInstalledTenurePurposeCaptureAt depth) :=
  fullyFulfilledSamePaymentOccurrence_noStructuralRent depth fully

theorem capture_chokepoint_mouth_has_no_graph_or_future_fields
    (depth : Nat) : True := by
  let cell := sourceGeneratedCaptureChokepointBasinRecoveryAt depth
  fail_if_success exact cell.graph
  fail_if_success exact cell.sectorRegistry
  fail_if_success exact cell.perturbationEdge
  fail_if_success exact cell.viableToCapture
  fail_if_success exact cell.rank
  fail_if_success exact cell.coverage
  fail_if_success exact cell.optimizer
  fail_if_success exact cell.completedHistory
  fail_if_success exact cell.futureTable
  trivial

end
end M14CaptureChokepointBasinRecovery
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14CaptureChokepointBasinRecovery.fullCapture_blocks_every_essential_domain
#print axioms SaturationMonoid.ProcessGame.Society.M14CaptureChokepointBasinRecovery.sourceGeneratedCaptureChokepointBasinRecoveryAt
#print axioms SaturationMonoid.ProcessGame.Society.M14CaptureChokepointBasinRecovery.structural_capture_chokepoint_is_in_viability_basin
#print axioms SaturationMonoid.ProcessGame.Society.M14CaptureChokepointBasinRecovery.current_quiver_has_no_viable_to_capture_shock
