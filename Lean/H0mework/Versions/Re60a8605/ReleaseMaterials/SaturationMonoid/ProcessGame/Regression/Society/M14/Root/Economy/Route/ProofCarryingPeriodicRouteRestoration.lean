import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Root.Economy.Route.PeriodicRouteOutageRestoration
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Consumer.Policy.TenureCaptureRouteRepairNoGoRegression
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Consumer.Policy.ProofCarryingExitRepairRegression
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Root.Economy.Portfolio.ActionableFuturePortfolio

/-!
# M14 proof-carrying periodic route restoration

The independently installed route coordinate, its actualized route-bottleneck
origin, and the existing proof-carrying repair compiler now meet in one
visit-indexed carrier.  The same root occurrence, component outcome, selected
row, whole-ledger write-back, generated next, and law surface lead to the
existing next-visit actionable-future portfolio.

The carrier is indexed only by temporal depth and repair.  Its sole public
producer accepts `depth` and generates the canonical `restoreRoute` repair.
Domain actionability, route receipts, and feasible edges remain pointwise
readouts of the existing dependent portfolio; no domain registry or coverage
table is stored.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingPeriodicRouteRestoration

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations Settlement Money Renewal Revision UBI
open Policy Capacity Space CrossingCost
open UBI.Capacity UBI.Capacity.SourceOwnedExitGeometryCompilerAt
open M3FiniteExchangeFixture M3ExchangeSettlementPriceRegression
open M9ProofCarryingRenewalInquiryRoot
open M14UBIExitCapacityFixture
open M14UBIProofCarryingRootRestriction
open M14UBIPeriodicRootHistory
open M14UBIPeriodicActualServiceCapacity
open M14SourceRouteOutageRestoration
open M14PeriodicRouteOutageRestoration
open M14TenureCaptureRouteRepairNoGoRegression
open M14ProofCarryingExitRepairRegression
open M14ProofCarryingExitRepairRenewalRegression
open M14EssentialAccessRelationFixture
open M14EssentialAccessSectorRegression
open M14ActionableFuturePortfolio

/-- One actual route restoration carrying its exact source-aware repair and
the existing next-visit full portfolio. -/
structure SourceGeneratedProofCarryingPeriodicRouteRestorationAt
    (depth : Nat) (repair : ExactExitRepair) : Type 18 where
  private mk ::
  actual : SourceGeneratedPeriodicRouteOutageRestorationAt depth
  actualExact : actual =
    sourceGeneratedPeriodicRouteOutageRestorationAt depth
  originConsumerExact : actual.installed.payload.consumer =
    sourceRouteOutageRestriction
  originActionExact : actual.installed.payload.disposition =
    sourceGeneratedRouteRestoration
  originActualWitness :
    Nonempty (SourceGeneratedPeriodicRouteOutageRestorationAt depth)
  originProvenance : ActualRouteOriginProvenanceAt depth
  repairProof : SourceGeneratedProofCarryingExitRepairAt
    (routeBottleneckOriginAt depth) repair
  failureCapacityExact : failureCapacityReadoutAt depth
    (routeBottleneckOriginAt depth) = 0
  repairExact : repair = canonicalRepairAt
    (routeBottleneckOriginAt depth)
  canonicalRepairIsRestoreRoute : canonicalRepairAt
    (routeBottleneckOriginAt depth) = ExactExitRepair.restoreRoute
  outcomeExact : repairOutcomeCapacityAt depth
    (routeBottleneckOriginAt depth) repair = 1
  uniqueEffective : (candidate : ExactExitRepair) →
    EffectiveRepairAt depth (routeBottleneckOriginAt depth) candidate ↔
      candidate = repair
  componentOutcomeExact :
    routeOutageRestorationRecognition.law.toProjectionLaw.outcomeAt PUnit.unit
        (jointRoot.emitted (temporalVisitAt depth).current) =
      (.inl ⟨actual.installed.active, actual.installed.payload⟩ :
        SourceNativeProjectionFiberAt
          routeOutageRestorationRecognition.law.toProjectionLaw PUnit.unit
          (jointRoot.emitted (temporalVisitAt depth).current))
  rootOccurrenceExact : actual.rootOccurrence =
    jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
      (temporalVisitAt depth)
  sourceEntryExact : actual.installed.payload.sourceEntry =
    RootInquiryU8CompletionRegression.entry
  selectedRowSharedWithUBI : HEq actual.installed.payload.selectedRow
    (installedUBIAt depth).payload.selectedRow
  successorSharedWithUBI : HEq actual.installed.payload.successor
    (installedUBIAt depth).payload.successor
  selectedWriteExact : actual.applied.selectedWrite =
    actual.installed.temporalSelectedRow
  selectedWriteCommutes :
    actual.applied.selectedWrite.sourceRow.CommutesWithWorld
  wholeLedgerExact : actual.applied.wholeLedgerWriteBack =
    (jointRoot.toAuthoritativeRoot.toLedgerRoot
      |>.generatedAtTemporalVisit
        (temporalVisitAt depth)).wholeLedgerWriteBack
  rootFactorization : actual.installed.RootAnswerAndNextFactorizes
  generatedNextExact : actual.applied.generatedNext =
    jointRoot.generatedNextCurrentAt (temporalVisitAt depth)
  lawSurfacePreserved : actual.applied.generatedNext.root.source.lawSurface =
    jointRoot.source.base.lawSurface
  nextVisitExact : actual.applied.generatedNext.visit =
    temporalVisitAt (depth + 1)
  targetPortfolio : SourceGeneratedActionableFuturePortfolioAt (depth + 1)
  targetPortfolioExact : targetPortfolio =
    sourceGeneratedActionableFuturePortfolioAt (depth + 1)
  targetRootExact : targetPortfolio.paymentOccurrence.rootOccurrence =
    jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
      (temporalVisitAt (depth + 1))
  targetCapacityExact :
    (geometryCompilerAt (depth + 1)).actionableExitCapacity = 1

namespace SourceGeneratedProofCarryingPeriodicRouteRestorationAt

variable {depth : Nat} {repair : ExactExitRepair}

/-- Pointwise existing domain actionability; the domain is a generated
authority, not an entry in a stored coverage table. -/
def targetDomainActionable
    (restoration : SourceGeneratedProofCarryingPeriodicRouteRestorationAt
      depth repair)
    (domain : EssentialAccessRelationAuthority) :
    SourceGeneratedEssentialDomainActionableAt (depth + 1) domain :=
  restoration.targetPortfolio.actionable domain

abbrev TargetDomainFeasibleAt
    (restoration : SourceGeneratedProofCarryingPeriodicRouteRestorationAt
      depth repair)
    (domain : EssentialAccessRelationAuthority) :=
  ExactFeasibleExitEdgeAt (geometryCompilerAt (depth + 1))
    ExitFutureCode.leave
      (restoration.targetDomainActionable domain).serviceIncidence.slot

abbrev TargetDomainRouteReceiptAt
    (restoration : SourceGeneratedProofCarryingPeriodicRouteRestorationAt
      depth repair)
    (domain : EssentialAccessRelationAuthority) :=
  (geometryCompilerAt (depth + 1)).RoutesAt ExitFutureCode.leave
    (ExactServedCrossingDebitedRunAt.servicedCrossingAt
      (phase := anomiePhaseAt (depth + 1))
      (crossingCompiler := crossingCompilerAt (depth + 1))
      (restoration.targetDomainActionable domain).serviceIncidence.slot)

/-- Existing feasible edge of one requested domain. -/
def targetDomainFeasible
    (restoration : SourceGeneratedProofCarryingPeriodicRouteRestorationAt
      depth repair)
    (domain : EssentialAccessRelationAuthority) :
    TargetDomainFeasibleAt restoration domain :=
  (restoration.targetDomainActionable domain).feasible

/-- Existing generated route receipt carried by that feasible edge. -/
def targetDomainRouteReceipt
    (restoration : SourceGeneratedProofCarryingPeriodicRouteRestorationAt
      depth repair)
    (domain : EssentialAccessRelationAuthority) :
    TargetDomainRouteReceiptAt restoration domain :=
  (restoration.targetDomainFeasible domain).routeReceipt

end SourceGeneratedProofCarryingPeriodicRouteRestorationAt

/-- Sole producer: the repair index is generated from the exact route origin,
not accepted from the caller. -/
def sourceGeneratedProofCarryingPeriodicRouteRestorationAt (depth : Nat) :
    SourceGeneratedProofCarryingPeriodicRouteRestorationAt depth
      (canonicalRepairAt (routeBottleneckOriginAt depth)) := by
  let actual := sourceGeneratedPeriodicRouteOutageRestorationAt depth
  let repairProof := SourceGeneratedProofCarryingExitRepairAt.generate
    (routeBottleneckOriginAt depth)
  let target := sourceGeneratedActionableFuturePortfolioAt (depth + 1)
  exact
    { actual := actual
      actualExact := rfl
      originConsumerExact := actual.consumerExact
      originActionExact := actual.actionExact
      originActualWitness :=
        (routeBottleneckFailureAt depth).actualRouteRestoration
      originProvenance := routeBottleneckFailure_actual_provenance depth
      repairProof := repairProof
      failureCapacityExact := route_bottleneck_failure_readout_eq_zero depth
      repairExact := repairProof.repair_eq
      canonicalRepairIsRestoreRoute := rfl
      outcomeExact := repairProof.outcome_eq_one
      uniqueEffective := by
        intro candidate
        rw [repairProof.repair_eq]
        exact effective_repair_iff_eq_canonical
          (routeBottleneckOriginAt depth) candidate
      componentOutcomeExact := actual.componentOutcomeExact
      rootOccurrenceExact := actual.rootOccurrenceExact
      sourceEntryExact := actual.sourceEntryExact
      selectedRowSharedWithUBI := actual.selectedRowSharedWithUBI
      successorSharedWithUBI := actual.successorSharedWithUBI
      selectedWriteExact := actual.selectedWriteExact
      selectedWriteCommutes := actual.selectedWriteCommutes
      wholeLedgerExact := actual.wholeLedgerExact
      rootFactorization := actual.rootFactorization
      generatedNextExact := actual.generatedNextExact
      lawSurfacePreserved := actual.lawSurfacePreserved
      nextVisitExact := actual.nextVisitExact
      targetPortfolio := target
      targetPortfolioExact := rfl
      targetRootExact := target.rootOccurrenceExact
      targetCapacityExact := actual.targetCapacityExact }

theorem every_generated_period_has_proofCarrying_route_restoration
    (depth : Nat) :
    Nonempty (SourceGeneratedProofCarryingPeriodicRouteRestorationAt depth
      (canonicalRepairAt (routeBottleneckOriginAt depth))) :=
  ⟨sourceGeneratedProofCarryingPeriodicRouteRestorationAt depth⟩

/-! ## Strong exact-source negatives -/

instance periodicRouteRemoveCapture_isEmpty (depth : Nat) : IsEmpty
    (SourceGeneratedProofCarryingPeriodicRouteRestorationAt
      depth .removeCapture) :=
  ⟨fun restoration => by
    have impossible := restoration.repairExact.trans
      restoration.canonicalRepairIsRestoreRoute
    cases impossible⟩

theorem noActualRouteOutage_noProofCarryingRestoration
    {depth : Nat} {repair : ExactExitRepair}
    (noActual : IsEmpty
      (SourceGeneratedPeriodicRouteOutageRestorationAt depth)) :
    IsEmpty (SourceGeneratedProofCarryingPeriodicRouteRestorationAt
      depth repair) :=
  ⟨fun restoration => noActual.false restoration.actual⟩

theorem generatedFullRouteSource_cannotGenerate_highLevelRouteRestoration :
    IsEmpty (SourceAppliedRouteRestorationAt
      M10OccurrenceCapacityProcessFixture.focalSeed
      SourceGeneratedUBIRouteReceiptAt SourceGeneratedUBIRouteReceiptAt
      .routeBottleneck .restoreRoute) :=
  generatedFullRouteSource_cannotGenerateRouteRestoration

/-- The old theorem remains true in its exact scope: the tenure coordinate
cannot execute `restoreRoute`.  The independently installed route coordinate
above is a different authority carrier. -/
theorem legacyTenureCoordinate_restoreRoute_isEmpty (depth : Nat) :
    IsEmpty (SourceInstalledProofCarryingExitRepairRenewalAt
      depth .restoreRoute) :=
  M14ProofCarryingExitRepairRenewalRegression.SourceInstalledProofCarryingExitRepairRenewalAt.restoreRoute_is_not_actual_in_tenure_coordinate
    depth

theorem route_restoration_pointwise_domain_readouts
    (depth : Nat) (domain : EssentialAccessRelationAuthority) :
    let restoration :=
      sourceGeneratedProofCarryingPeriodicRouteRestorationAt depth
    Nonempty (SourceGeneratedEssentialDomainActionableAt
        (depth + 1) domain) ∧
      Nonempty
        (SourceGeneratedProofCarryingPeriodicRouteRestorationAt.TargetDomainFeasibleAt
          restoration domain) ∧
      Nonempty
        (SourceGeneratedProofCarryingPeriodicRouteRestorationAt.TargetDomainRouteReceiptAt
          restoration domain) :=
  let restoration :=
    sourceGeneratedProofCarryingPeriodicRouteRestorationAt depth
  ⟨⟨restoration.targetDomainActionable domain⟩,
    ⟨restoration.targetDomainFeasible domain⟩,
    ⟨restoration.targetDomainRouteReceipt domain⟩⟩

theorem proofCarrying_route_restoration_mouth_has_no_submitted_authority
    (depth : Nat) : True := by
  let restoration :=
    sourceGeneratedProofCarryingPeriodicRouteRestorationAt depth
  fail_if_success exact restoration.origin
  fail_if_success exact restoration.submittedRepair
  fail_if_success exact restoration.result
  fail_if_success exact restoration.targetCandidate
  fail_if_success exact restoration.nextCandidate
  fail_if_success exact restoration.domainRegistry
  fail_if_success exact restoration.coverage
  fail_if_success exact restoration.trace
  fail_if_success exact restoration.measure
  fail_if_success exact restoration.probability
  fail_if_success exact restoration.u8Core
  fail_if_success exact restoration.completedFuture
  trivial

end
end M14ProofCarryingPeriodicRouteRestoration
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingPeriodicRouteRestoration.sourceGeneratedProofCarryingPeriodicRouteRestorationAt
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingPeriodicRouteRestoration.periodicRouteRemoveCapture_isEmpty
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingPeriodicRouteRestoration.legacyTenureCoordinate_restoreRoute_isEmpty
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingPeriodicRouteRestoration.route_restoration_pointwise_domain_readouts
