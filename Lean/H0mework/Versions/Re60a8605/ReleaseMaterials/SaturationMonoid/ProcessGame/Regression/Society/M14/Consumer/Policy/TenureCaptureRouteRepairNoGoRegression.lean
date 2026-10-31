import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Consumer.Sector.EssentialAccessSectorRegression
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Consumer.Identification.ZeroCapacityCausalNonidentifiabilityRegression
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Root.Economy.Route.PeriodicRouteOutageRestoration

/-!
# M14 capacity-only repair-selection no-go

Two exact post-emission failures have the same visible exit capacity `0`:
tenure-side price capture and an uncaptured missing-route bottleneck.  Their
effective repairs are opposite.  Removing capture restores the first but not
the second; restoring route restores the second but not the first.

All four outcome capacities are computed by the existing canonical matching
geometry.  Neither failure stores a capacity result and neither repair stores
an effectiveness verdict.  Hence a policy selector which observes only the
natural-number failure capacity cannot choose an effective repair for both.
No welfare oracle, policy registry, second matching, ledger, or completed
future is introduced.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14TenureCaptureRouteRepairNoGoRegression

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open UBI Renewal Capacity
open UBI.Policy
open UBI.Capacity.SourceOwnedExitGeometryCompilerAt
open M3ExchangeSettlementPriceRegression
open M14UBIExitCapacityFixture
open M14UBIPeriodicRootHistory
open M14UBIPeriodicActualServiceCapacity
open M14CaptureResponsibilityDispositionRegression
open M14EmploymentOutsideOptionGeometryRegression
open M14ZeroCapacityCausalNonidentifiabilityRegression
open M14EssentialAccessRelationFixture
open M14EssentialAccessSectorRegression
open M14SourceRouteOutageRestoration
open M14PeriodicRouteOutageRestoration

/-- Exact tenure-capture cause.  This deliberately does not reuse
`PeriodicTenureCaptureRenewalAt`: that downstream bundle already contains
capacity/exit results.  Every field here is source-side and no capacity or
emptiness value appears in the signature. -/
structure TenureCaptureFailureAt (depth : Nat) : Prop where
  private mk ::
  captureSignature : PriceCaptureSignatureAt depth
  tenureInterest : essentialAccessRelationCompiler.GeneratedInterestAt
    tenureActor tenureRelation
  tenureActorIsCounterparty :
    tenureActor = Money.exactCounterpartyActor exactResidualActivation
  tenurePhase : essentialAccessRelationCompiler.phaseStep tenureRelation =
    .tenure
  tenureRole : essentialAccessRelationCompiler.RelationRoleAt
    tenureActor tenureRelation .target .tenureProvider

/-- Exact infrastructure cause.  The tenure relation still exists, payment
and actual service exist, capture is absent, and only route incidence is
missing.  No capacity value appears in the signature. -/
structure RouteBottleneckFailureAt (depth : Nat) : Prop where
  private mk ::
  actualRouteRestoration :
    Nonempty (SourceGeneratedPeriodicRouteOutageRestorationAt depth)
  tenureInterest : essentialAccessRelationCompiler.GeneratedInterestAt
    tenureActor tenureRelation
  tenureActorIsCounterparty :
    tenureActor = Money.exactCounterpartyActor exactResidualActivation
  tenurePhase : essentialAccessRelationCompiler.phaseStep tenureRelation =
    .tenure
  tenureRole : essentialAccessRelationCompiler.RelationRoleAt
    tenureActor tenureRelation .target .tenureProvider
  routeSignature : RouteIncidenceMissingSignatureAt depth

theorem tenureCaptureFailureAt (depth : Nat) :
    TenureCaptureFailureAt depth :=
  let sourceFailure :=
    (periodicUBISourceAt depth).installed.payload.disposition.sourceFailure
  { captureSignature :=
      { captured := sourceFailure.captured
        captureDisposition := fixedCaptureDisposition
        exactTemporalPayment :=
          (periodicSourceBackedPaymentAt depth).rootOccurrence_eq
        paymentPresent := (captured_payment_and_route_present_at depth).1
        routePresent := (captured_payment_and_route_present_at depth).2
        servicePresent := actual_service_present_at depth }
    tenureInterest := sourceFailure.tenureInterest
    tenureActorIsCounterparty := sourceFailure.tenureActorIsCounterparty
    tenurePhase := sourceFailure.tenurePhase
    tenureRole := sourceFailure.tenureRole }

theorem routeBottleneckFailureAt (depth : Nat) :
    RouteBottleneckFailureAt depth :=
  let actual := sourceGeneratedPeriodicRouteOutageRestorationAt depth
  { actualRouteRestoration := ⟨actual⟩
    tenureInterest := actual.sourceTenureInterest
    tenureActorIsCounterparty := actual.sourceTenureActorIsCounterparty
    tenurePhase := actual.sourceTenurePhase
    tenureRole := actual.sourceTenureRole
    routeSignature :=
      { uncaptured := actual.sourceUncaptured
        exactTemporalPayment :=
          actual.paymentRootShared.trans actual.rootOccurrenceExact
        paymentPresent := ⟨actual.sourcePaymentReceipt⟩
        routeMissing :=
          actual.sourceRouteMissing (firstServicedCrossingAt depth)
        servicePresent := actual.actualService } }

/-- Exact provenance of the route origin.  The missing route is read from
the independently installed action-bearing route coordinate, not from the
standalone diagnostic signature producer. -/
abbrev ActualRouteOriginProvenanceAt (depth : Nat) : Prop :=
  let actual := sourceGeneratedPeriodicRouteOutageRestorationAt depth
  actual.installed.payload.consumer = sourceRouteOutageRestriction ∧
    actual.installed.payload.disposition =
      sourceGeneratedRouteRestoration ∧
    Nonempty (SourceGeneratedPeriodicRouteOutageRestorationAt depth) ∧
    essentialAccessRelationCompiler.GeneratedInterestAt
      tenureActor tenureRelation ∧
    tenureActor = Money.exactCounterpartyActor exactResidualActivation ∧
    essentialAccessRelationCompiler.phaseStep tenureRelation = .tenure ∧
    essentialAccessRelationCompiler.RelationRoleAt
      tenureActor tenureRelation .target .tenureProvider ∧
    actual.rootOccurrence =
      (M9ProofCarryingRenewalInquiryRoot.jointRoot.toAuthoritativeRoot.toLedgerRoot
        |>.exactTemporalCausalEventAt (temporalVisitAt depth)) ∧
    (periodicSourceBackedPaymentAt depth).rootOccurrence =
      actual.rootOccurrence ∧
    Nonempty ((routeIncidenceMissingGeometryAt depth).PaysForAt
      exitCapacityProgram.purchasingPowerStanding ExitFutureCode.leave) ∧
    IsEmpty ((routeIncidenceMissingGeometryAt depth).RoutesAt
      ExitFutureCode.leave (firstServicedCrossingAt depth)) ∧
    Nonempty (ActualServiceAt depth)

theorem routeBottleneckFailure_actual_provenance (depth : Nat) :
    ActualRouteOriginProvenanceAt depth :=
  let actual := sourceGeneratedPeriodicRouteOutageRestorationAt depth
  ⟨actual.consumerExact, actual.actionExact,
    ⟨actual⟩,
    actual.sourceTenureInterest,
    actual.sourceTenureActorIsCounterparty,
    actual.sourceTenurePhase,
    actual.sourceTenureRole,
    actual.rootOccurrenceExact,
    actual.paymentRootShared, ⟨actual.sourcePaymentReceipt⟩,
    actual.sourceRouteMissing (firstServicedCrossingAt depth),
    actual.actualService⟩

/-- Source-backed two-point failure carrier. -/
inductive RepairFailureOriginAt (depth : Nat) where
  | tenureCapture (failure : TenureCaptureFailureAt depth)
  | routeBottleneck (failure : RouteBottleneckFailureAt depth)

def tenureCaptureOriginAt (depth : Nat) : RepairFailureOriginAt depth :=
  .tenureCapture (tenureCaptureFailureAt depth)

def routeBottleneckOriginAt (depth : Nat) : RepairFailureOriginAt depth :=
  .routeBottleneck (routeBottleneckFailureAt depth)

/-- Forget only the proof payload after the exact source origin has already
been generated.  This kind is the input language of the pre-emitter repair
compiler; it is not accepted as a substitute for `RepairFailureOriginAt`. -/
def RepairFailureOriginAt.failureKind {depth : Nat} :
    RepairFailureOriginAt depth → ExactExitFailureKind
  | .tenureCapture _ => .tenureCapture
  | .routeBottleneck _ => .routeBottleneck

/-- Both source causes retain the exact temporal payment occurrence of their
indexed period.  This is the bridge used by an actual root renewal; the
numeric failure readout carries no such authority. -/
theorem RepairFailureOriginAt.exactTemporalPayment
    {depth : Nat} (origin : RepairFailureOriginAt depth) :
    (periodicSourceBackedPaymentAt depth).rootOccurrence =
      M9ProofCarryingRenewalInquiryRoot.jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
        (temporalVisitAt depth) := by
  cases origin with
  | tenureCapture failure => exact failure.captureSignature.exactTemporalPayment
  | routeBottleneck failure => exact failure.routeSignature.exactTemporalPayment

/-- Failure readout before intervention. -/
noncomputable def failureCapacityReadoutAt (depth : Nat) :
    RepairFailureOriginAt depth → Nat
  | .tenureCapture _ =>
      (capturedGeometryCompilerAt depth).actionableExitCapacity
  | .routeBottleneck _ =>
      (routeIncidenceMissingGeometryAt depth).actionableExitCapacity

/-- Counterfactual outcome of one exact repair.

* removing capture changes only `fullCapture` to `noCapture`;
* restoring route changes only the empty route incidence to the existing
  generated route receipt family.

Applying a repair to the wrong cause leaves its missing incidence untouched. -/
noncomputable def repairOutcomeCapacityAt (depth : Nat) :
    RepairFailureOriginAt depth → ExactExitRepair → Nat
  | .tenureCapture _, .removeCapture =>
      (geometryCompilerAt depth).actionableExitCapacity
  | .tenureCapture _, .restoreRoute =>
      (capturedGeometryCompilerAt depth).actionableExitCapacity
  | .routeBottleneck _, .removeCapture =>
      (routeIncidenceMissingGeometryAt depth).actionableExitCapacity
  | .routeBottleneck _, .restoreRoute =>
      (geometryCompilerAt depth).actionableExitCapacity

theorem tenure_capture_failure_readout_eq_zero (depth : Nat) :
    failureCapacityReadoutAt depth (tenureCaptureOriginAt depth) = 0 :=
  captured_nominal_capacity_eq_zero_at depth

theorem route_bottleneck_failure_readout_eq_zero (depth : Nat) :
    failureCapacityReadoutAt depth (routeBottleneckOriginAt depth) = 0 :=
  route_missing_capacity_eq_zero_at depth

theorem failure_readouts_equal (depth : Nat) :
    failureCapacityReadoutAt depth (tenureCaptureOriginAt depth) =
      failureCapacityReadoutAt depth (routeBottleneckOriginAt depth) := by
  rw [tenure_capture_failure_readout_eq_zero,
    route_bottleneck_failure_readout_eq_zero]

theorem remove_capture_repairs_tenure_at (depth : Nat) :
    repairOutcomeCapacityAt depth (tenureCaptureOriginAt depth)
      .removeCapture = 1 :=
  actionableExitCapacity_eq_one_at depth

theorem restore_route_does_not_repair_capture_at (depth : Nat) :
    repairOutcomeCapacityAt depth (tenureCaptureOriginAt depth)
      .restoreRoute = 0 :=
  captured_nominal_capacity_eq_zero_at depth

theorem remove_capture_does_not_repair_route_at (depth : Nat) :
    repairOutcomeCapacityAt depth (routeBottleneckOriginAt depth)
      .removeCapture = 0 :=
  route_missing_capacity_eq_zero_at depth

theorem restore_route_repairs_bottleneck_at (depth : Nat) :
    repairOutcomeCapacityAt depth (routeBottleneckOriginAt depth)
      .restoreRoute = 1 :=
  actionableExitCapacity_eq_one_at depth

/-- Exact intervention guard.  Removing capture preserves program data and
both receipt families; restoring route preserves payment incidence.  All
four geometries are already indexed by the same phase/run/service/settlement. -/
theorem repairs_preserve_every_non_target_axis (depth : Nat) :
    capturedProgram.payment = exitCapacityProgram.payment ∧
      capturedProgram.purchasingPowerStanding =
        exitCapacityProgram.purchasingPowerStanding ∧
      capturedProgram.employmentLoss = exitCapacityProgram.employmentLoss ∧
      capturedProgram.exitInterest = exitCapacityProgram.exitInterest ∧
      (∀ code,
        (capturedGeometryCompilerAt depth).PaysForAt
            capturedProgram.purchasingPowerStanding code =
          (geometryCompilerAt depth).PaysForAt
            exitCapacityProgram.purchasingPowerStanding code) ∧
      (∀ code crossing,
        (capturedGeometryCompilerAt depth).RoutesAt code crossing =
          (geometryCompilerAt depth).RoutesAt code crossing) ∧
      (∀ code,
        (routeIncidenceMissingGeometryAt depth).PaysForAt
            exitCapacityProgram.purchasingPowerStanding code =
          (geometryCompilerAt depth).PaysForAt
            exitCapacityProgram.purchasingPowerStanding code) :=
  ⟨captured_counterfactual_same_payment,
    captured_counterfactual_same_purchasingPowerStanding,
    captured_counterfactual_same_employmentLoss,
    captured_counterfactual_same_exitInterest,
    captured_counterfactual_same_payment_receipt_family depth,
    captured_counterfactual_same_route_receipt_family depth,
    fun _code => rfl⟩

def EffectiveRepairAt (depth : Nat) (origin : RepairFailureOriginAt depth)
    (repair : ExactExitRepair) : Prop :=
  0 < repairOutcomeCapacityAt depth origin repair

theorem tenure_effective_repair_iff (depth : Nat) (repair : ExactExitRepair) :
    EffectiveRepairAt depth (tenureCaptureOriginAt depth) repair ↔
      repair = .removeCapture := by
  cases repair with
  | removeCapture =>
      rw [EffectiveRepairAt, remove_capture_repairs_tenure_at]
      simp
  | restoreRoute =>
      rw [EffectiveRepairAt, restore_route_does_not_repair_capture_at]
      simp

theorem route_effective_repair_iff (depth : Nat) (repair : ExactExitRepair) :
    EffectiveRepairAt depth (routeBottleneckOriginAt depth) repair ↔
      repair = .restoreRoute := by
  cases repair with
  | removeCapture =>
      rw [EffectiveRepairAt, remove_capture_does_not_repair_route_at]
      simp
  | restoreRoute =>
      rw [EffectiveRepairAt, restore_route_repairs_bottleneck_at]
      simp

theorem each_failure_has_unique_effective_repair (depth : Nat) :
    (∃! repair : ExactExitRepair,
      EffectiveRepairAt depth (tenureCaptureOriginAt depth) repair) ∧
    (∃! repair : ExactExitRepair,
      EffectiveRepairAt depth (routeBottleneckOriginAt depth) repair) := by
  constructor
  · refine ⟨.removeCapture,
      (tenure_effective_repair_iff depth .removeCapture).2 rfl, ?_⟩
    intro candidate effective
    exact (tenure_effective_repair_iff depth candidate).1 effective
  · refine ⟨.restoreRoute,
      (route_effective_repair_iff depth .restoreRoute).2 rfl, ?_⟩
    intro candidate effective
    exact (route_effective_repair_iff depth candidate).1 effective

theorem no_single_repair_handles_both_failures (depth : Nat) :
    ¬ ∃ repair : ExactExitRepair,
      EffectiveRepairAt depth (tenureCaptureOriginAt depth) repair ∧
      EffectiveRepairAt depth (routeBottleneckOriginAt depth) repair := by
  rintro ⟨repair, tenureEffective, routeEffective⟩
  have remove := (tenure_effective_repair_iff depth repair).1 tenureEffective
  have restore := (route_effective_repair_iff depth repair).1 routeEffective
  rw [remove] at restore
  cases restore

/-- Strong policy no-go: a selector seeing only the visible Nat capacity
must return one repair at the shared value `0`, so it fails one exact cause. -/
theorem no_capacity_only_effective_repair_selector (depth : Nat) :
    ¬ ∃ selectRepair : Nat → ExactExitRepair,
      (∀ origin : RepairFailureOriginAt depth,
        EffectiveRepairAt depth origin
          (selectRepair (failureCapacityReadoutAt depth origin))) := by
  rintro ⟨selectRepair, effective⟩
  let selected := selectRepair
    (failureCapacityReadoutAt depth (tenureCaptureOriginAt depth))
  have tenureEffective :
      EffectiveRepairAt depth (tenureCaptureOriginAt depth) selected :=
    effective (tenureCaptureOriginAt depth)
  have routeEffective :
      EffectiveRepairAt depth (routeBottleneckOriginAt depth) selected := by
    have generated := effective (routeBottleneckOriginAt depth)
    rw [← failure_readouts_equal depth] at generated
    exact generated
  exact no_single_repair_handles_both_failures depth
    ⟨selected, tenureEffective, routeEffective⟩

structure TenureCaptureRouteRepairNoGoCertificate : Prop where
  everyDepthActualRouteOriginProvenance : ∀ depth : Nat,
    ActualRouteOriginProvenanceAt depth
  everyDepthInterventionGuard : ∀ depth : Nat,
    capturedProgram.payment = exitCapacityProgram.payment ∧
      capturedProgram.purchasingPowerStanding =
        exitCapacityProgram.purchasingPowerStanding ∧
      capturedProgram.employmentLoss = exitCapacityProgram.employmentLoss ∧
      capturedProgram.exitInterest = exitCapacityProgram.exitInterest ∧
      (∀ code,
        (capturedGeometryCompilerAt depth).PaysForAt
            capturedProgram.purchasingPowerStanding code =
          (geometryCompilerAt depth).PaysForAt
            exitCapacityProgram.purchasingPowerStanding code) ∧
      (∀ code crossing,
        (capturedGeometryCompilerAt depth).RoutesAt code crossing =
          (geometryCompilerAt depth).RoutesAt code crossing) ∧
      (∀ code,
        (routeIncidenceMissingGeometryAt depth).PaysForAt
            exitCapacityProgram.purchasingPowerStanding code =
          (geometryCompilerAt depth).PaysForAt
            exitCapacityProgram.purchasingPowerStanding code)
  everyDepthSameFailureReadout : ∀ depth : Nat,
    failureCapacityReadoutAt depth (tenureCaptureOriginAt depth) = 0 ∧
      failureCapacityReadoutAt depth (routeBottleneckOriginAt depth) = 0
  everyDepthRepairMatrix : ∀ depth : Nat,
    repairOutcomeCapacityAt depth (tenureCaptureOriginAt depth)
        .removeCapture = 1 ∧
      repairOutcomeCapacityAt depth (tenureCaptureOriginAt depth)
        .restoreRoute = 0 ∧
      repairOutcomeCapacityAt depth (routeBottleneckOriginAt depth)
        .removeCapture = 0 ∧
      repairOutcomeCapacityAt depth (routeBottleneckOriginAt depth)
        .restoreRoute = 1
  everyDepthUniqueRepairs : ∀ depth : Nat,
    (∃! repair : ExactExitRepair,
      EffectiveRepairAt depth (tenureCaptureOriginAt depth) repair) ∧
    (∃! repair : ExactExitRepair,
      EffectiveRepairAt depth (routeBottleneckOriginAt depth) repair)
  everyDepthNoUniversalRepair : ∀ depth : Nat,
    ¬ ∃ repair : ExactExitRepair,
      EffectiveRepairAt depth (tenureCaptureOriginAt depth) repair ∧
      EffectiveRepairAt depth (routeBottleneckOriginAt depth) repair
  everyDepthNoCapacityOnlySelector : ∀ depth : Nat,
    ¬ ∃ selectRepair : Nat → ExactExitRepair,
      ∀ origin : RepairFailureOriginAt depth,
        EffectiveRepairAt depth origin
          (selectRepair (failureCapacityReadoutAt depth origin))

theorem tenureCaptureRouteRepairNoGoDirectConsumer :
    TenureCaptureRouteRepairNoGoCertificate where
  everyDepthActualRouteOriginProvenance :=
    routeBottleneckFailure_actual_provenance
  everyDepthInterventionGuard := repairs_preserve_every_non_target_axis
  everyDepthSameFailureReadout := fun depth =>
    ⟨tenure_capture_failure_readout_eq_zero depth,
      route_bottleneck_failure_readout_eq_zero depth⟩
  everyDepthRepairMatrix := fun depth =>
    ⟨remove_capture_repairs_tenure_at depth,
      restore_route_does_not_repair_capture_at depth,
      remove_capture_does_not_repair_route_at depth,
      restore_route_repairs_bottleneck_at depth⟩
  everyDepthUniqueRepairs := each_failure_has_unique_effective_repair
  everyDepthNoUniversalRepair := no_single_repair_handles_both_failures
  everyDepthNoCapacityOnlySelector :=
    no_capacity_only_effective_repair_selector

end
end M14TenureCaptureRouteRepairNoGoRegression
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14TenureCaptureRouteRepairNoGoRegression.each_failure_has_unique_effective_repair
#print axioms SaturationMonoid.ProcessGame.Society.M14TenureCaptureRouteRepairNoGoRegression.routeBottleneckFailure_actual_provenance
#print axioms SaturationMonoid.ProcessGame.Society.M14TenureCaptureRouteRepairNoGoRegression.no_capacity_only_effective_repair_selector
#print axioms SaturationMonoid.ProcessGame.Society.M14TenureCaptureRouteRepairNoGoRegression.tenureCaptureRouteRepairNoGoDirectConsumer
