import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Root.Economy.Route.ProofCarryingPeriodicRouteRestoration
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Consumer.Economy.Route.ProofCarryingActualRouteOriginRegression

/-!
# M14 direct consumer for proof-carrying periodic route restoration

This consumer joins the actual route coordinate, its private exact origin,
the existing repair compiler, and the next-visit actionable portfolio.  It
checks the full root/row/ledger/next provenance and proves pointwise restored
route feasibility for every existing essential authority.

The certificate is dependent on the already consumed actual-origin
certificate.  It stores no second origin authority, domain registry, coverage
table, target schedule, trace, measure, U8 branch, or completed future.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingPeriodicRouteRestorationRegression

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Renewal UBI Policy Capacity Space CrossingCost
open M9ProofCarryingRenewalInquiryRoot
open M14UBIPeriodicRootHistory
open M14UBIPeriodicActualServiceCapacity
open M14UBIProofCarryingRootRestriction
open M14SourceRouteOutageRestoration
open M14PeriodicRouteOutageRestoration
open M14TenureCaptureRouteRepairNoGoRegression
open M14ProofCarryingExitRepairRegression
open M14ProofCarryingExitRepairRenewalRegression
open M14EssentialAccessRelationFixture
open M14EssentialAccessSectorRegression
open M14ActionableFuturePortfolio
open M14ProofCarryingActualRouteOriginRegression
open M14ProofCarryingPeriodicRouteRestoration

theorem proofCarryingRouteSourceAndRepairExact (depth : Nat) :
    let restoration :=
      sourceGeneratedProofCarryingPeriodicRouteRestorationAt depth
    Nonempty (SourceGeneratedProofCarryingPeriodicRouteRestorationAt depth
        (canonicalRepairAt (routeBottleneckOriginAt depth))) ∧
      Nonempty (SourceGeneratedPeriodicRouteOutageRestorationAt depth) ∧
      restoration.actual =
        sourceGeneratedPeriodicRouteOutageRestorationAt depth ∧
      ActualRouteOriginProvenanceAt depth ∧
      restoration.actual.installed.payload.consumer =
        sourceRouteOutageRestriction ∧
      restoration.actual.installed.payload.disposition =
        sourceGeneratedRouteRestoration ∧
      Nonempty (SourceGeneratedProofCarryingExitRepairAt
        (routeBottleneckOriginAt depth)
          (canonicalRepairAt (routeBottleneckOriginAt depth))) ∧
      failureCapacityReadoutAt depth (routeBottleneckOriginAt depth) = 0 ∧
      canonicalRepairAt (routeBottleneckOriginAt depth) = .restoreRoute ∧
      repairOutcomeCapacityAt depth (routeBottleneckOriginAt depth)
        (canonicalRepairAt (routeBottleneckOriginAt depth)) = 1 ∧
      (∀ candidate : ExactExitRepair,
        EffectiveRepairAt depth (routeBottleneckOriginAt depth) candidate ↔
          candidate = canonicalRepairAt (routeBottleneckOriginAt depth)) := by
  let restoration :=
    sourceGeneratedProofCarryingPeriodicRouteRestorationAt depth
  exact ⟨⟨restoration⟩,
    restoration.originActualWitness,
    restoration.actualExact,
    restoration.originProvenance,
    restoration.originConsumerExact,
    restoration.originActionExact,
    ⟨restoration.repairProof⟩,
    restoration.failureCapacityExact,
    restoration.canonicalRepairIsRestoreRoute,
    restoration.outcomeExact,
    restoration.uniqueEffective⟩

theorem proofCarryingRouteRootLedgerAndNextExact (depth : Nat) :
    let restoration :=
      sourceGeneratedProofCarryingPeriodicRouteRestorationAt depth
    routeOutageRestorationRecognition.law.toProjectionLaw.outcomeAt PUnit.unit
        (jointRoot.emitted (temporalVisitAt depth).current) =
      (.inl ⟨restoration.actual.installed.active,
        restoration.actual.installed.payload⟩ :
        SourceNativeProjectionFiberAt
          routeOutageRestorationRecognition.law.toProjectionLaw PUnit.unit
          (jointRoot.emitted (temporalVisitAt depth).current)) ∧
      restoration.actual.rootOccurrence =
        jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
          (temporalVisitAt depth) ∧
      restoration.actual.installed.payload.sourceEntry =
        RootInquiryU8CompletionRegression.entry ∧
      HEq restoration.actual.installed.payload.selectedRow
        (installedUBIAt depth).payload.selectedRow ∧
      HEq restoration.actual.installed.payload.successor
        (installedUBIAt depth).payload.successor ∧
      restoration.actual.applied.selectedWrite =
        restoration.actual.installed.temporalSelectedRow ∧
      restoration.actual.applied.selectedWrite.sourceRow.CommutesWithWorld ∧
      restoration.actual.applied.wholeLedgerWriteBack =
        (jointRoot.toAuthoritativeRoot.toLedgerRoot
          |>.generatedAtTemporalVisit
            (temporalVisitAt depth)).wholeLedgerWriteBack ∧
      restoration.actual.installed.RootAnswerAndNextFactorizes ∧
      restoration.actual.applied.generatedNext =
        jointRoot.generatedNextCurrentAt (temporalVisitAt depth) ∧
      restoration.actual.applied.generatedNext.visit =
        temporalVisitAt (depth + 1) ∧
      restoration.actual.applied.generatedNext.root.source.lawSurface =
        jointRoot.source.base.lawSurface := by
  let restoration :=
    sourceGeneratedProofCarryingPeriodicRouteRestorationAt depth
  exact ⟨restoration.componentOutcomeExact,
    restoration.rootOccurrenceExact,
    restoration.sourceEntryExact,
    restoration.selectedRowSharedWithUBI,
    restoration.successorSharedWithUBI,
    restoration.selectedWriteExact,
    restoration.selectedWriteCommutes,
    restoration.wholeLedgerExact,
    restoration.rootFactorization,
    restoration.generatedNextExact,
    restoration.nextVisitExact,
    restoration.lawSurfacePreserved⟩

theorem proofCarryingRouteTargetPortfolioExact (depth : Nat) :
    let restoration :=
      sourceGeneratedProofCarryingPeriodicRouteRestorationAt depth
    restoration.targetPortfolio =
        sourceGeneratedActionableFuturePortfolioAt (depth + 1) ∧
      restoration.targetPortfolio.paymentOccurrence.rootOccurrence =
        jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
          (temporalVisitAt (depth + 1)) ∧
      (geometryCompilerAt (depth + 1)).actionableExitCapacity = 1 ∧
      (∀ domain : EssentialAccessRelationAuthority,
        Nonempty (SourceGeneratedEssentialDomainActionableAt
          (depth + 1) domain) ∧
        Nonempty
          (SourceGeneratedProofCarryingPeriodicRouteRestorationAt.TargetDomainFeasibleAt
            restoration domain) ∧
        Nonempty
          (SourceGeneratedProofCarryingPeriodicRouteRestorationAt.TargetDomainRouteReceiptAt
            restoration domain)) := by
  let restoration :=
    sourceGeneratedProofCarryingPeriodicRouteRestorationAt depth
  exact ⟨restoration.targetPortfolioExact,
    restoration.targetRootExact,
    restoration.targetCapacityExact,
    fun domain => route_restoration_pointwise_domain_readouts depth domain⟩

theorem proofCarryingRouteStrictControls (depth : Nat) :
    IsEmpty (SourceGeneratedProofCarryingPeriodicRouteRestorationAt
        depth .removeCapture) ∧
      (IsEmpty (SourceGeneratedPeriodicRouteOutageRestorationAt depth) →
        IsEmpty (SourceGeneratedProofCarryingPeriodicRouteRestorationAt
          depth (canonicalRepairAt (routeBottleneckOriginAt depth)))) ∧
      IsEmpty (SourceAppliedRouteRestorationAt
        M10OccurrenceCapacityProcessFixture.focalSeed
        SourceGeneratedUBIRouteReceiptAt SourceGeneratedUBIRouteReceiptAt
        .routeBottleneck .restoreRoute) ∧
      IsEmpty (SourceInstalledProofCarryingExitRepairRenewalAt
        depth .restoreRoute) ∧
      jointRouteOutageRestorationProjection ≠ jointUBIProjection :=
  ⟨inferInstance,
    fun noActual => noActualRouteOutage_noProofCarryingRestoration noActual,
    generatedFullRouteSource_cannotGenerate_highLevelRouteRestoration,
    legacyTenureCoordinate_restoreRoute_isEmpty depth,
    routeOutage_projection_ne_ubi_projection⟩

theorem proofCarryingRouteCarrierConstructorIsPrivate : True := by
  fail_if_success
    exact SourceGeneratedProofCarryingPeriodicRouteRestorationAt.mk
  trivial

structure ProofCarryingPeriodicRouteRestorationCertificateAt
    {source : TenureCaptureRouteRepairNoGoCertificate}
    (origin : ProofCarryingActualRouteOriginCertificateAt source) : Prop where
  sourceProvenance : ∀ depth : Nat,
    ActualRouteOriginProvenanceAt depth
  everyDepthSourceAndRepair : ∀ depth : Nat,
    let restoration :=
      sourceGeneratedProofCarryingPeriodicRouteRestorationAt depth
    Nonempty (SourceGeneratedProofCarryingPeriodicRouteRestorationAt depth
        (canonicalRepairAt (routeBottleneckOriginAt depth))) ∧
      Nonempty (SourceGeneratedPeriodicRouteOutageRestorationAt depth) ∧
      restoration.actual =
        sourceGeneratedPeriodicRouteOutageRestorationAt depth ∧
      ActualRouteOriginProvenanceAt depth ∧
      restoration.actual.installed.payload.consumer =
        sourceRouteOutageRestriction ∧
      restoration.actual.installed.payload.disposition =
        sourceGeneratedRouteRestoration ∧
      Nonempty (SourceGeneratedProofCarryingExitRepairAt
        (routeBottleneckOriginAt depth)
          (canonicalRepairAt (routeBottleneckOriginAt depth))) ∧
      failureCapacityReadoutAt depth (routeBottleneckOriginAt depth) = 0 ∧
      canonicalRepairAt (routeBottleneckOriginAt depth) = .restoreRoute ∧
      repairOutcomeCapacityAt depth (routeBottleneckOriginAt depth)
        (canonicalRepairAt (routeBottleneckOriginAt depth)) = 1 ∧
      (∀ candidate : ExactExitRepair,
        EffectiveRepairAt depth (routeBottleneckOriginAt depth) candidate ↔
          candidate = canonicalRepairAt (routeBottleneckOriginAt depth))
  everyDepthRootLedgerNext : ∀ depth : Nat,
    let restoration :=
      sourceGeneratedProofCarryingPeriodicRouteRestorationAt depth
    routeOutageRestorationRecognition.law.toProjectionLaw.outcomeAt PUnit.unit
        (jointRoot.emitted (temporalVisitAt depth).current) =
      (.inl ⟨restoration.actual.installed.active,
        restoration.actual.installed.payload⟩ :
        SourceNativeProjectionFiberAt
          routeOutageRestorationRecognition.law.toProjectionLaw PUnit.unit
          (jointRoot.emitted (temporalVisitAt depth).current)) ∧
      restoration.actual.rootOccurrence =
        jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
          (temporalVisitAt depth) ∧
      restoration.actual.installed.payload.sourceEntry =
        RootInquiryU8CompletionRegression.entry ∧
      HEq restoration.actual.installed.payload.selectedRow
        (installedUBIAt depth).payload.selectedRow ∧
      HEq restoration.actual.installed.payload.successor
        (installedUBIAt depth).payload.successor ∧
      restoration.actual.applied.selectedWrite =
        restoration.actual.installed.temporalSelectedRow ∧
      restoration.actual.applied.selectedWrite.sourceRow.CommutesWithWorld ∧
      restoration.actual.applied.wholeLedgerWriteBack =
        (jointRoot.toAuthoritativeRoot.toLedgerRoot
          |>.generatedAtTemporalVisit
            (temporalVisitAt depth)).wholeLedgerWriteBack ∧
      restoration.actual.installed.RootAnswerAndNextFactorizes ∧
      restoration.actual.applied.generatedNext =
        jointRoot.generatedNextCurrentAt (temporalVisitAt depth) ∧
      restoration.actual.applied.generatedNext.visit =
        temporalVisitAt (depth + 1) ∧
      restoration.actual.applied.generatedNext.root.source.lawSurface =
        jointRoot.source.base.lawSurface
  everyDepthTargetPortfolio : ∀ depth : Nat,
    let restoration :=
      sourceGeneratedProofCarryingPeriodicRouteRestorationAt depth
    restoration.targetPortfolio =
        sourceGeneratedActionableFuturePortfolioAt (depth + 1) ∧
      restoration.targetPortfolio.paymentOccurrence.rootOccurrence =
        jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
          (temporalVisitAt (depth + 1)) ∧
      (geometryCompilerAt (depth + 1)).actionableExitCapacity = 1 ∧
      (∀ domain : EssentialAccessRelationAuthority,
        Nonempty (SourceGeneratedEssentialDomainActionableAt
          (depth + 1) domain) ∧
        Nonempty
          (SourceGeneratedProofCarryingPeriodicRouteRestorationAt.TargetDomainFeasibleAt
            restoration domain) ∧
        Nonempty
          (SourceGeneratedProofCarryingPeriodicRouteRestorationAt.TargetDomainRouteReceiptAt
            restoration domain))
  everyDepthStrictControls : ∀ depth : Nat,
    IsEmpty (SourceGeneratedProofCarryingPeriodicRouteRestorationAt
        depth .removeCapture) ∧
      (IsEmpty (SourceGeneratedPeriodicRouteOutageRestorationAt depth) →
        IsEmpty (SourceGeneratedProofCarryingPeriodicRouteRestorationAt
          depth (canonicalRepairAt (routeBottleneckOriginAt depth)))) ∧
      IsEmpty (SourceAppliedRouteRestorationAt
        M10OccurrenceCapacityProcessFixture.focalSeed
        SourceGeneratedUBIRouteReceiptAt SourceGeneratedUBIRouteReceiptAt
        .routeBottleneck .restoreRoute) ∧
      IsEmpty (SourceInstalledProofCarryingExitRepairRenewalAt
        depth .restoreRoute) ∧
      jointRouteOutageRestorationProjection ≠ jointUBIProjection
  privateCarrierMouth : True

theorem proofCarryingPeriodicRouteRestorationDirectConsumerAt
    {source : TenureCaptureRouteRepairNoGoCertificate}
    (origin : ProofCarryingActualRouteOriginCertificateAt source) :
    ProofCarryingPeriodicRouteRestorationCertificateAt origin where
  sourceProvenance := origin.sourceProvenance
  everyDepthSourceAndRepair := proofCarryingRouteSourceAndRepairExact
  everyDepthRootLedgerNext := proofCarryingRouteRootLedgerAndNextExact
  everyDepthTargetPortfolio := proofCarryingRouteTargetPortfolioExact
  everyDepthStrictControls := proofCarryingRouteStrictControls
  privateCarrierMouth := proofCarryingRouteCarrierConstructorIsPrivate

end
end M14ProofCarryingPeriodicRouteRestorationRegression
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingPeriodicRouteRestorationRegression.proofCarryingRouteSourceAndRepairExact
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingPeriodicRouteRestorationRegression.proofCarryingRouteRootLedgerAndNextExact
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingPeriodicRouteRestorationRegression.proofCarryingRouteTargetPortfolioExact
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingPeriodicRouteRestorationRegression.proofCarryingRouteStrictControls
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingPeriodicRouteRestorationRegression.proofCarryingPeriodicRouteRestorationDirectConsumerAt
