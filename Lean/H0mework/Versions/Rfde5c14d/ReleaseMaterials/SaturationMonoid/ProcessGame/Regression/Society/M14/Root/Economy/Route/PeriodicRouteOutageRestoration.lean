import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M9.JointRoot.ProofCarryingRenewalInquiryRoot
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Route.SourceRouteOutageRestoration
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Root.UBIPeriodicActualServiceCapacity
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedInstitutionalRevision

/-!
# M14 actual periodic route-outage restoration

At every generated finite root visit, the same-root route coordinate emits
the exact PEmpty-route source and compiler-generated restoration action.  Its
installed operational authority generates the selected row, whole-ledger
write-back, and same-law next.  Only after that next does the depth-only
producer read an existing target route receipt, feasible exit, and the next
visit's positive actionable-exit capacity.

This is the low route layer: it deliberately does not import or construct a
`RepairFailureOriginAt`.  The public producer accepts only `depth`; source,
action, root occurrence, row, target receipt, capacity, and next are all
generated internally.  No root, ledger, occurrence registry, trace, measure,
U8 object, or completed future is introduced.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14PeriodicRouteOutageRestoration

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations Settlement Money Renewal Revision UBI
open Policy Capacity Space CrossingCost
open UBI.Capacity UBI.Capacity.SourceOwnedExitGeometryCompilerAt
open M3FiniteExchangeFixture M3ExchangeSettlementPriceRegression
open M9ProofCarryingRenewalInquiryRoot
open M10OccurrenceCapacityProcessFixture
open M10OccurrenceCapacityDebitedRunFixture
open M14UBIExitCapacityFixture
open M14UBIProofCarryingRootRestriction
open M14EssentialAccessRelationFixture
open M14UBIPeriodicRootHistory
open M14UBIPeriodicActualServiceCapacity
open M14SourceRouteOutageRestoration

/-! ## Installed action-bearing coordinate -/

def installedRouteOutageRestorationAt (depth : Nat) :
    SourceInstalledRenewalAt routeOutageRestorationRecognition
      (temporalVisitAt depth) :=
  SourceInstalledRenewalAt.generate PUnit.unit rfl

/-- Same-row bounded reform whose applied action is literally the route
disposition installed before this root occurrence is emitted. -/
structure SourceInstalledAppliedRouteRestorationAt
    (depth : Nat)
    (installed : SourceInstalledRenewalAt
      routeOutageRestorationRecognition (temporalVisitAt depth))
    (applied : RouteRestorationDispositionAt
      installed.payload.sourceSeed) : Type 3 where
  private mk ::
  applied_eq : applied = installed.payload.disposition
  reform : SourceNativeBoundedInstitutionalReformAt
    installed.operationalAuthority
  rootConsumer : RenewalResponsibilityConsumerAt
    installed.operationalAuthority
  rootFactorization : installed.RootAnswerAndNextFactorizes

namespace SourceInstalledAppliedRouteRestorationAt

def generate (depth : Nat)
    (installed : SourceInstalledRenewalAt
      routeOutageRestorationRecognition (temporalVisitAt depth)) :
    SourceInstalledAppliedRouteRestorationAt depth installed
      installed.payload.disposition where
  applied_eq := rfl
  reform := SourceNativeBoundedInstitutionalReformAt.generate
    installed.operationalAuthority
  rootConsumer := installed.rootResponsibilityConsumer
  rootFactorization := installed.rootAnswerAndNext_factorizes

variable {depth : Nat}
variable {installed : SourceInstalledRenewalAt
  routeOutageRestorationRecognition (temporalVisitAt depth)}
variable {applied : RouteRestorationDispositionAt
  installed.payload.sourceSeed}

def selectedWrite
    (restoration : SourceInstalledAppliedRouteRestorationAt
      depth installed applied) :=
  restoration.reform.residualRow

theorem selectedWrite_eq_installedSelectedRow
    (restoration : SourceInstalledAppliedRouteRestorationAt
      depth installed applied) :
    restoration.selectedWrite = installed.temporalSelectedRow :=
  rfl

theorem selectedWrite_commutes
    (restoration : SourceInstalledAppliedRouteRestorationAt
      depth installed applied) :
    restoration.selectedWrite.sourceRow.CommutesWithWorld :=
  restoration.reform.residualRow_commutes_with_wholeLedger

def wholeLedgerWriteBack
    (restoration : SourceInstalledAppliedRouteRestorationAt
      depth installed applied) :=
  restoration.reform.wholeLedgerWriteBack

def generatedNext
    (restoration : SourceInstalledAppliedRouteRestorationAt
      depth installed applied) :=
  restoration.reform.generatedNext

theorem generatedNext_eq_rootCompiler
    (restoration : SourceInstalledAppliedRouteRestorationAt
      depth installed applied) :
    restoration.generatedNext =
      jointRoot.generatedNextCurrentAt (temporalVisitAt depth) :=
  restoration.reform.generatedNext_eq_rootCompiler

theorem lawSurface_preserved
    (restoration : SourceInstalledAppliedRouteRestorationAt
      depth installed applied) :
    restoration.generatedNext.root.source.lawSurface =
      jointRoot.source.base.lawSurface :=
  restoration.reform.lawSurface_preserved

end SourceInstalledAppliedRouteRestorationAt

/-! ## Exact target readout -/

def routeRestorationTargetCrossingAt (depth : Nat) : ConcreteCrossing :=
  ExactServedCrossingDebitedRunAt.servicedCrossingAt
    (phase := anomiePhaseAt (depth + 1))
    (crossingCompiler := crossingCompilerAt (depth + 1))
    (firstSlotAt (depth + 1))

/-! ## Full visit-indexed actual carrier -/

structure SourceGeneratedPeriodicRouteOutageRestorationAt
    (depth : Nat) : Type 18 where
  private mk ::
  installed : SourceInstalledRenewalAt
    routeOutageRestorationRecognition (temporalVisitAt depth)
  seedExact : installed.payload.sourceSeed = focalSeed
  consumerExact : installed.payload.consumer = sourceRouteOutageRestriction
  actionExact : installed.payload.disposition =
    sourceGeneratedRouteRestoration
  failureKindExact :
    SourceAppliedRouteRestorationAt.failureKindAt
      installed.payload.disposition = ExactExitFailureKind.routeBottleneck
  repairExact : SourceAppliedRouteRestorationAt.repairAt
    installed.payload.disposition = ExactExitRepair.restoreRoute
  sourceTenureInterest :
    essentialAccessRelationCompiler.GeneratedInterestAt
      tenureActor tenureRelation
  sourceTenureActorIsCounterparty :
    tenureActor = Money.exactCounterpartyActor exactResidualActivation
  sourceTenurePhase :
    essentialAccessRelationCompiler.phaseStep tenureRelation = .tenure
  sourceTenureRole : essentialAccessRelationCompiler.RelationRoleAt
    tenureActor tenureRelation .target .tenureProvider
  sourceUncaptured : ¬ noCapture.Captures ExitFutureCode.leave
  sourcePaymentReceipt : SourceBackedUBIPaymentReceiptAt
    exitCapacityProgram.purchasingPowerStanding ExitFutureCode.leave
  sourceRouteMissing : (crossing : ConcreteCrossing) →
    IsEmpty (RouteOutageRoutesAt ExitFutureCode.leave crossing)
  actualService : Nonempty (ExactServedCrossingDebitedRunAt
    (anomiePhaseAt depth) debited (serviceCompilerAt depth))
  rootOccurrence : ExactTemporalCausalRootEventAt
    jointRoot.toAuthoritativeRoot.toLedgerRoot (temporalVisitAt depth)
  rootOccurrenceExact : rootOccurrence =
    jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
      (temporalVisitAt depth)
  paymentRootShared :
    (periodicSourceBackedPaymentAt depth).rootOccurrence = rootOccurrence
  componentOutcomeExact :
    routeOutageRestorationRecognition.law.toProjectionLaw.outcomeAt PUnit.unit
        (jointRoot.emitted (temporalVisitAt depth).current) =
      (.inl ⟨installed.active, installed.payload⟩ :
        SourceNativeProjectionFiberAt
          routeOutageRestorationRecognition.law.toProjectionLaw PUnit.unit
          (jointRoot.emitted (temporalVisitAt depth).current))
  sourceEntryExact : installed.payload.sourceEntry =
    RootInquiryU8CompletionRegression.entry
  selectedRowSharedWithUBI :
    HEq installed.payload.selectedRow
      (installedUBIAt depth).payload.selectedRow
  successorSharedWithUBI :
    HEq installed.payload.successor
      (installedUBIAt depth).payload.successor
  applied : SourceInstalledAppliedRouteRestorationAt
    depth installed installed.payload.disposition
  selectedWriteExact : applied.selectedWrite = installed.temporalSelectedRow
  selectedWriteCommutes : applied.selectedWrite.sourceRow.CommutesWithWorld
  wholeLedgerExact : applied.wholeLedgerWriteBack =
    (jointRoot.toAuthoritativeRoot.toLedgerRoot
      |>.generatedAtTemporalVisit
        (temporalVisitAt depth)).wholeLedgerWriteBack
  rootFactorization : installed.RootAnswerAndNextFactorizes
  generatedNextExact : applied.generatedNext =
    jointRoot.generatedNextCurrentAt (temporalVisitAt depth)
  lawSurfacePreserved : applied.generatedNext.root.source.lawSurface =
    jointRoot.source.base.lawSurface
  nextVisitExact : applied.generatedNext.visit =
    temporalVisitAt (depth + 1)
  targetRouteReceipt : SourceGeneratedUBIRouteReceiptAt
    ExitFutureCode.leave (routeRestorationTargetCrossingAt depth)
  targetFeasibleExit : ExactFeasibleExitEdgeAt
    (geometryCompilerAt (depth + 1)) ExitFutureCode.leave
      (firstSlotAt (depth + 1))
  targetCapacityExact :
    (geometryCompilerAt (depth + 1)).actionableExitCapacity = 1
  routeProjectionDistinctFromExisting :
    jointRouteOutageRestorationProjection ≠
        jointEssentialServiceRestorationProjection ∧
      jointRouteOutageRestorationProjection ≠ jointMandateProjection ∧
      jointRouteOutageRestorationProjection ≠
        jointRecognitionWitnessProjection ∧
      jointRouteOutageRestorationProjection ≠ jointUBIProjection ∧
      jointRouteOutageRestorationProjection ≠
        jointProofCarryingProjection ∧
      jointRouteOutageRestorationProjection ≠ jointInquiryProjection ∧
      jointRouteOutageRestorationProjection ≠ jointFailureProjection

/-- Sole actual producer.  No source/action/result/root candidate enters its
mouth; every field is regenerated from the exact finite visit. -/
def sourceGeneratedPeriodicRouteOutageRestorationAt (depth : Nat) :
    SourceGeneratedPeriodicRouteOutageRestorationAt depth := by
  let installed := installedRouteOutageRestorationAt depth
  let applied :=
    SourceInstalledAppliedRouteRestorationAt.generate depth installed
  exact
    { installed := installed
      seedExact := rfl
      consumerExact := rfl
      actionExact := rfl
      failureKindExact := rfl
      repairExact := rfl
      sourceTenureInterest := installed.payload.consumer.tenureInterest
      sourceTenureActorIsCounterparty :=
        installed.payload.consumer.tenureActorIsCounterparty
      sourceTenurePhase := installed.payload.consumer.tenurePhase
      sourceTenureRole := installed.payload.consumer.tenureRole
      sourceUncaptured := installed.payload.consumer.uncaptured
      sourcePaymentReceipt := installed.payload.consumer.paymentReceipt
      sourceRouteMissing := installed.payload.consumer.routeMissing
      actualService := ⟨actualSettlementAt depth⟩
      rootOccurrence :=
        jointRoot.toAuthoritativeRoot.toLedgerRoot
          |>.exactTemporalCausalEventAt (temporalVisitAt depth)
      rootOccurrenceExact := rfl
      paymentRootShared :=
        (periodicSourceBackedPaymentAt depth).rootOccurrence_eq
      componentOutcomeExact := installed.componentOutcome_eq_activePayload
      sourceEntryExact := rfl
      selectedRowSharedWithUBI := HEq.rfl
      successorSharedWithUBI := HEq.rfl
      applied := applied
      selectedWriteExact := applied.selectedWrite_eq_installedSelectedRow
      selectedWriteCommutes := applied.selectedWrite_commutes
      wholeLedgerExact := rfl
      rootFactorization := applied.rootFactorization
      generatedNextExact := applied.generatedNext_eq_rootCompiler
      lawSurfacePreserved := applied.lawSurface_preserved
      nextVisitExact := rfl
      targetRouteReceipt := SourceGeneratedUBIRouteReceiptAt.generate _
      targetFeasibleExit := firstFeasibleExitAt (depth + 1)
      targetCapacityExact := actionableExitCapacity_eq_one_at (depth + 1)
      routeProjectionDistinctFromExisting :=
        routeOutage_projection_distinct_from_existing_coordinates }

theorem every_generated_period_has_actual_route_outage_restoration
    (depth : Nat) :
    Nonempty (SourceGeneratedPeriodicRouteOutageRestorationAt depth) :=
  ⟨sourceGeneratedPeriodicRouteOutageRestorationAt depth⟩

theorem periodic_route_source_empty_target_route_live (depth : Nat) :
    IsEmpty (RouteOutageRoutesAt ExitFutureCode.leave
        (routeRestorationTargetCrossingAt depth)) ∧
      Nonempty (SourceGeneratedUBIRouteReceiptAt ExitFutureCode.leave
        (routeRestorationTargetCrossingAt depth)) :=
  let restoration := sourceGeneratedPeriodicRouteOutageRestorationAt depth
  ⟨restoration.sourceRouteMissing _, ⟨restoration.targetRouteReceipt⟩⟩

theorem periodic_route_restoration_root_and_next_exact (depth : Nat) :
    let restoration := sourceGeneratedPeriodicRouteOutageRestorationAt depth
    restoration.rootOccurrence =
        jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
          (temporalVisitAt depth) ∧
      restoration.applied.wholeLedgerWriteBack =
        (jointRoot.toAuthoritativeRoot.toLedgerRoot
          |>.generatedAtTemporalVisit
            (temporalVisitAt depth)).wholeLedgerWriteBack ∧
      restoration.applied.generatedNext =
        jointRoot.generatedNextCurrentAt (temporalVisitAt depth) :=
  let restoration := sourceGeneratedPeriodicRouteOutageRestorationAt depth
  ⟨restoration.rootOccurrenceExact, restoration.wholeLedgerExact,
    restoration.generatedNextExact⟩

theorem periodic_route_restoration_mouth_has_no_submitted_target_or_future
    (depth : Nat) : True := by
  let restoration := sourceGeneratedPeriodicRouteOutageRestorationAt depth
  fail_if_success exact restoration.sourceCandidate
  fail_if_success exact restoration.actionCandidate
  fail_if_success exact restoration.rootCandidate
  fail_if_success exact restoration.rowCandidate
  fail_if_success exact restoration.targetCandidate
  fail_if_success exact restoration.capacityPremise
  fail_if_success exact restoration.nextCandidate
  fail_if_success exact restoration.trace
  fail_if_success exact restoration.measure
  fail_if_success exact restoration.probability
  fail_if_success exact restoration.u8Core
  fail_if_success exact restoration.completedFuture
  trivial

end
end M14PeriodicRouteOutageRestoration
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14PeriodicRouteOutageRestoration.installedRouteOutageRestorationAt
#print axioms SaturationMonoid.ProcessGame.Society.M14PeriodicRouteOutageRestoration.sourceGeneratedPeriodicRouteOutageRestorationAt
#print axioms SaturationMonoid.ProcessGame.Society.M14PeriodicRouteOutageRestoration.periodic_route_source_empty_target_route_live
#print axioms SaturationMonoid.ProcessGame.Society.M14PeriodicRouteOutageRestoration.periodic_route_restoration_root_and_next_exact
