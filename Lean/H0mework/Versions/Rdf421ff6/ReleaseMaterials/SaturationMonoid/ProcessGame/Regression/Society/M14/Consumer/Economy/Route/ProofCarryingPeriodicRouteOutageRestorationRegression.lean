import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Root.Economy.Route.PeriodicRouteOutageRestoration
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Consumer.Economy.Route.ProofCarryingSameRootRouteCoordinateRegression

/-!
# M14 direct consumer for periodic actual route restoration

At every generated finite visit, the independently installed route coordinate
now produces its own actual outage/restoration event, writes through the
existing row and whole ledger, and generates the same-law next.  Only after
that update does this consumer read an existing target route receipt,
feasible exit, and capacity one at the next visit.

This consumer neither identifies the route event with the UBI-tenure action
nor constructs a repair-origin facade, trace, measure, U8 branch, second root,
or completed future.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingPeriodicRouteOutageRestorationRegression

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations Settlement Money Renewal UBI Policy
open Capacity Space CrossingCost
open UBI.Capacity UBI.Capacity.SourceOwnedExitGeometryCompilerAt
open M3ExchangeSettlementPriceRegression
open M9ProofCarryingRenewalInquiryRoot
open M10OccurrenceCapacityProcessFixture
open M10OccurrenceCapacityDebitedRunFixture
open M14UBIExitCapacityFixture
open M14UBIProofCarryingRootRestriction
open M14EssentialAccessRelationFixture
open M14UBIPeriodicRootHistory
open M14UBIPeriodicActualServiceCapacity
open M14SourceRouteOutageRestoration
open M14PeriodicRouteOutageRestoration
open M14ProofCarryingSameRootRouteCoordinateRegression

theorem periodicRouteSourceAndActionExact (depth : Nat) :
    let restoration := sourceGeneratedPeriodicRouteOutageRestorationAt depth
    restoration.installed.payload.sourceSeed = focalSeed ∧
      restoration.installed.payload.consumer = sourceRouteOutageRestriction ∧
      restoration.installed.payload.disposition =
        sourceGeneratedRouteRestoration ∧
      SourceAppliedRouteRestorationAt.failureKindAt
          restoration.installed.payload.disposition = .routeBottleneck ∧
      SourceAppliedRouteRestorationAt.repairAt
          restoration.installed.payload.disposition = .restoreRoute ∧
      essentialAccessRelationCompiler.GeneratedInterestAt
        tenureActor tenureRelation ∧
      tenureActor = Money.exactCounterpartyActor exactResidualActivation ∧
      essentialAccessRelationCompiler.phaseStep tenureRelation = .tenure ∧
      essentialAccessRelationCompiler.RelationRoleAt
        tenureActor tenureRelation .target .tenureProvider ∧
      ¬ noCapture.Captures ExitFutureCode.leave ∧
      Nonempty (SourceBackedUBIPaymentReceiptAt
        exitCapacityProgram.purchasingPowerStanding ExitFutureCode.leave) := by
  let restoration := sourceGeneratedPeriodicRouteOutageRestorationAt depth
  exact ⟨restoration.seedExact,
    restoration.consumerExact,
    restoration.actionExact,
    restoration.failureKindExact,
    restoration.repairExact,
    restoration.sourceTenureInterest,
    restoration.sourceTenureActorIsCounterparty,
    restoration.sourceTenurePhase,
    restoration.sourceTenureRole,
    restoration.sourceUncaptured,
    ⟨restoration.sourcePaymentReceipt⟩⟩

theorem periodicRouteRootLedgerAndNextExact (depth : Nat) :
    let restoration := sourceGeneratedPeriodicRouteOutageRestorationAt depth
    restoration.rootOccurrence =
        jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
          (temporalVisitAt depth) ∧
      (periodicSourceBackedPaymentAt depth).rootOccurrence =
        restoration.rootOccurrence ∧
      restoration.installed.payload.sourceEntry =
        RootInquiryU8CompletionRegression.entry ∧
      HEq restoration.installed.payload.selectedRow
        (installedUBIAt depth).payload.selectedRow ∧
      HEq restoration.installed.payload.successor
        (installedUBIAt depth).payload.successor ∧
      restoration.applied.selectedWrite =
        restoration.installed.temporalSelectedRow ∧
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
      restoration.applied.generatedNext.root.source.lawSurface =
        jointRoot.source.base.lawSurface := by
  let restoration := sourceGeneratedPeriodicRouteOutageRestorationAt depth
  exact ⟨restoration.rootOccurrenceExact,
    restoration.paymentRootShared,
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

theorem periodicRouteRestoresTheMissingAxis (depth : Nat) :
    IsEmpty (RouteOutageRoutesAt ExitFutureCode.leave
        (routeRestorationTargetCrossingAt depth)) ∧
      Nonempty (SourceGeneratedUBIRouteReceiptAt ExitFutureCode.leave
        (routeRestorationTargetCrossingAt depth)) ∧
      Nonempty (ExactServedCrossingDebitedRunAt
        (anomiePhaseAt depth) debited (serviceCompilerAt depth)) ∧
      Nonempty (ExactFeasibleExitEdgeAt
        (geometryCompilerAt (depth + 1)) ExitFutureCode.leave
          (firstSlotAt (depth + 1))) ∧
      (geometryCompilerAt (depth + 1)).actionableExitCapacity = 1 := by
  let restoration := sourceGeneratedPeriodicRouteOutageRestorationAt depth
  exact ⟨restoration.sourceRouteMissing _,
    ⟨restoration.targetRouteReceipt⟩,
    restoration.actualService,
    ⟨restoration.targetFeasibleExit⟩,
    restoration.targetCapacityExact⟩

theorem periodicRouteAuthorityAndRetypingControls :
    (jointRouteOutageRestorationProjection ≠
        jointEssentialServiceRestorationProjection ∧
      jointRouteOutageRestorationProjection ≠ jointMandateProjection ∧
      jointRouteOutageRestorationProjection ≠
        jointRecognitionWitnessProjection ∧
      jointRouteOutageRestorationProjection ≠ jointUBIProjection ∧
      jointRouteOutageRestorationProjection ≠
        jointProofCarryingProjection ∧
      jointRouteOutageRestorationProjection ≠ jointInquiryProjection ∧
      jointRouteOutageRestorationProjection ≠ jointFailureProjection) ∧
      IsEmpty
        (SourceAppliedRouteRestorationAt focalSeed RouteOutageRoutesAt
          SourceGeneratedUBIRouteReceiptAt .routeBottleneck .removeCapture) ∧
      IsEmpty
        (SourceAppliedRouteRestorationAt focalSeed RouteOutageRoutesAt
          SourceGeneratedUBIRouteReceiptAt .tenureCapture .restoreRoute) ∧
      IsEmpty
        (SourceRouteOutageRestrictionAt focalSeed
          SourceGeneratedUBIRouteReceiptAt) ∧
      IsEmpty
        (SourceAppliedRouteRestorationAt focalSeed
          SourceGeneratedUBIRouteReceiptAt
          SourceGeneratedUBIRouteReceiptAt
          .routeBottleneck .restoreRoute) ∧
      IsEmpty
        (SourceAppliedRouteRestorationAt focalSeed RouteOutageRoutesAt
          RouteOutageRoutesAt .routeBottleneck .restoreRoute) := by
  exact ⟨routeOutage_projection_distinct_from_existing_coordinates,
    proofCarryingSameRootRouteCoordinateDirectConsumer.strictControls⟩

structure ProofCarryingPeriodicRouteOutageRestorationCertificate : Prop where
  everyDepth : ∀ depth : Nat,
    Nonempty (SourceGeneratedPeriodicRouteOutageRestorationAt depth)
  sourceAndActionExact : ∀ depth : Nat,
    let restoration := sourceGeneratedPeriodicRouteOutageRestorationAt depth
    restoration.installed.payload.sourceSeed = focalSeed ∧
      restoration.installed.payload.consumer = sourceRouteOutageRestriction ∧
      restoration.installed.payload.disposition =
        sourceGeneratedRouteRestoration ∧
      SourceAppliedRouteRestorationAt.failureKindAt
          restoration.installed.payload.disposition = .routeBottleneck ∧
      SourceAppliedRouteRestorationAt.repairAt
          restoration.installed.payload.disposition = .restoreRoute ∧
      essentialAccessRelationCompiler.GeneratedInterestAt
        tenureActor tenureRelation ∧
      tenureActor = Money.exactCounterpartyActor exactResidualActivation ∧
      essentialAccessRelationCompiler.phaseStep tenureRelation = .tenure ∧
      essentialAccessRelationCompiler.RelationRoleAt
        tenureActor tenureRelation .target .tenureProvider ∧
      ¬ noCapture.Captures ExitFutureCode.leave ∧
      Nonempty (SourceBackedUBIPaymentReceiptAt
        exitCapacityProgram.purchasingPowerStanding ExitFutureCode.leave)
  rootLedgerAndNextExact : ∀ depth : Nat,
    let restoration := sourceGeneratedPeriodicRouteOutageRestorationAt depth
    restoration.rootOccurrence =
        jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
          (temporalVisitAt depth) ∧
      (periodicSourceBackedPaymentAt depth).rootOccurrence =
        restoration.rootOccurrence ∧
      restoration.installed.payload.sourceEntry =
        RootInquiryU8CompletionRegression.entry ∧
      HEq restoration.installed.payload.selectedRow
        (installedUBIAt depth).payload.selectedRow ∧
      HEq restoration.installed.payload.successor
        (installedUBIAt depth).payload.successor ∧
      restoration.applied.selectedWrite =
        restoration.installed.temporalSelectedRow ∧
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
      restoration.applied.generatedNext.root.source.lawSurface =
        jointRoot.source.base.lawSurface
  restoresMissingAxis : ∀ depth : Nat,
    IsEmpty (RouteOutageRoutesAt ExitFutureCode.leave
        (routeRestorationTargetCrossingAt depth)) ∧
      Nonempty (SourceGeneratedUBIRouteReceiptAt ExitFutureCode.leave
        (routeRestorationTargetCrossingAt depth)) ∧
      Nonempty (ExactServedCrossingDebitedRunAt
        (anomiePhaseAt depth) debited (serviceCompilerAt depth)) ∧
      Nonempty (ExactFeasibleExitEdgeAt
        (geometryCompilerAt (depth + 1)) ExitFutureCode.leave
          (firstSlotAt (depth + 1))) ∧
      (geometryCompilerAt (depth + 1)).actionableExitCapacity = 1
  authorityAndRetypingControls :
    (jointRouteOutageRestorationProjection ≠
        jointEssentialServiceRestorationProjection ∧
      jointRouteOutageRestorationProjection ≠ jointMandateProjection ∧
      jointRouteOutageRestorationProjection ≠
        jointRecognitionWitnessProjection ∧
      jointRouteOutageRestorationProjection ≠ jointUBIProjection ∧
      jointRouteOutageRestorationProjection ≠
        jointProofCarryingProjection ∧
      jointRouteOutageRestorationProjection ≠ jointInquiryProjection ∧
      jointRouteOutageRestorationProjection ≠ jointFailureProjection) ∧
      IsEmpty
        (SourceAppliedRouteRestorationAt focalSeed RouteOutageRoutesAt
          SourceGeneratedUBIRouteReceiptAt .routeBottleneck .removeCapture) ∧
      IsEmpty
        (SourceAppliedRouteRestorationAt focalSeed RouteOutageRoutesAt
          SourceGeneratedUBIRouteReceiptAt .tenureCapture .restoreRoute) ∧
      IsEmpty
        (SourceRouteOutageRestrictionAt focalSeed
          SourceGeneratedUBIRouteReceiptAt) ∧
      IsEmpty
        (SourceAppliedRouteRestorationAt focalSeed
          SourceGeneratedUBIRouteReceiptAt
          SourceGeneratedUBIRouteReceiptAt
          .routeBottleneck .restoreRoute) ∧
      IsEmpty
        (SourceAppliedRouteRestorationAt focalSeed RouteOutageRoutesAt
          RouteOutageRoutesAt .routeBottleneck .restoreRoute)

theorem proofCarryingPeriodicRouteOutageRestorationDirectConsumer :
    ProofCarryingPeriodicRouteOutageRestorationCertificate where
  everyDepth := every_generated_period_has_actual_route_outage_restoration
  sourceAndActionExact := periodicRouteSourceAndActionExact
  rootLedgerAndNextExact := periodicRouteRootLedgerAndNextExact
  restoresMissingAxis := periodicRouteRestoresTheMissingAxis
  authorityAndRetypingControls := periodicRouteAuthorityAndRetypingControls

end
end M14ProofCarryingPeriodicRouteOutageRestorationRegression
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingPeriodicRouteOutageRestorationRegression.periodicRouteSourceAndActionExact
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingPeriodicRouteOutageRestorationRegression.periodicRouteRootLedgerAndNextExact
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingPeriodicRouteOutageRestorationRegression.periodicRouteRestoresTheMissingAxis
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingPeriodicRouteOutageRestorationRegression.periodicRouteAuthorityAndRetypingControls
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingPeriodicRouteOutageRestorationRegression.proofCarryingPeriodicRouteOutageRestorationDirectConsumer
