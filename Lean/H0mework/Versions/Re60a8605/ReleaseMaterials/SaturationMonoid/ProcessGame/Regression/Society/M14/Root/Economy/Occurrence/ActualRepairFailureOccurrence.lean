import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Root.Economy.Route.ProofCarryingPeriodicRouteRestoration

/-!
# M14 common actual repair-failure facade

Actual tenure capture and actual route outage retain distinct installed
coordinate authorities.  This file does not combine them in a new sum or
registry: `ActualRepairFailureAt` is definitionally a dependent match on the
existing `RepairFailureOriginAt` constructors.  The tenure branch is the
existing UBI remove-capture renewal; the route branch is the independently
installed proof-carrying route restoration.

Both branch producers accept only `depth`.  Common readouts expose exact root
occurrence, source entry, branch-native source consumer and installed action,
selected-write commutation, whole-ledger write-back, generated next,
projection, and repair without erasing branch authority.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ActualRepairFailureOccurrence

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Renewal UBI Policy
open M9ProofCarryingRenewalInquiryRoot
open M14UBIProofCarryingRootRestriction
open M14UBIPeriodicRootHistory
open M14SourceRouteOutageRestoration
open M14TenureCaptureRouteRepairNoGoRegression
open M14ProofCarryingExitRepairRegression
open M14ProofCarryingExitRepairRenewalRegression
open M14ProofCarryingPeriodicRouteRestoration

/-- Common actual fibre, assembled only by dependent reduction to one of the
two already installed coordinate carriers. -/
abbrev ActualRepairFailureAt
    (depth : Nat) (origin : RepairFailureOriginAt depth) : Type 18 :=
  match origin with
  | .tenureCapture _ =>
      ULift.{18, 3}
        (SourceInstalledProofCarryingExitRepairRenewalAt depth .removeCapture)
  | .routeBottleneck _ =>
      SourceGeneratedProofCarryingPeriodicRouteRestorationAt
        depth .restoreRoute

/-- Depth-only canonical tenure producer. -/
def sourceGeneratedActualTenureRepairFailureAt (depth : Nat) :
    ActualRepairFailureAt depth (tenureCaptureOriginAt depth) :=
  ULift.up (SourceInstalledProofCarryingExitRepairRenewalAt.generate depth)

/-- Depth-only canonical route producer. -/
def sourceGeneratedActualRouteRepairFailureAt (depth : Nat) :
    ActualRepairFailureAt depth (routeBottleneckOriginAt depth) :=
  sourceGeneratedProofCarryingPeriodicRouteRestorationAt depth

/-- Every clean origin in the existing two-constructor carrier has its own
actual installed branch.  Proof payloads do not choose a coordinate. -/
theorem every_origin_has_actualRepairFailure
    (depth : Nat) (origin : RepairFailureOriginAt depth) :
    Nonempty (ActualRepairFailureAt depth origin) := by
  cases origin with
  | tenureCapture _ =>
      exact ⟨sourceGeneratedActualTenureRepairFailureAt depth⟩
  | routeBottleneck _ =>
      exact ⟨sourceGeneratedActualRouteRepairFailureAt depth⟩

namespace ActualRepairFailureAt

variable {depth : Nat} {origin : RepairFailureOriginAt depth}

def rootOccurrence
    (actual : ActualRepairFailureAt depth origin) :
    ExactTemporalCausalRootEventAt
      jointRoot.toAuthoritativeRoot.toLedgerRoot (temporalVisitAt depth) := by
  cases origin with
  | tenureCapture _ => exact actual.down.rootOccurrence
  | routeBottleneck _ => exact actual.actual.rootOccurrence

def sourceEntry (actual : ActualRepairFailureAt depth origin) := by
  cases origin with
  | tenureCapture _ => exact actual.down.source.installed.payload.sourceEntry
  | routeBottleneck _ => exact actual.actual.installed.payload.sourceEntry

/-- The two branches retain their differently typed source consumers.  This
dependent proposition states exactness without inventing a common consumer
carrier. -/
def SourceConsumerExactAt
    (origin : RepairFailureOriginAt depth) :
    ActualRepairFailureAt depth origin → Prop :=
  match origin with
  | .tenureCapture _ => fun actual =>
      actual.down.source.installed.payload.consumer =
        sourceGeneratedUBIRootRestriction
  | .routeBottleneck _ => fun actual =>
      actual.actual.installed.payload.consumer =
        sourceRouteOutageRestriction

theorem sourceConsumerExact
    (actual : ActualRepairFailureAt depth origin) :
    SourceConsumerExactAt origin actual := by
  cases origin with
  | tenureCapture _ => exact actual.down.source.exactRestriction
  | routeBottleneck _ => exact actual.originConsumerExact

/-- The installed actions likewise remain branch-native: UBI removes tenure
capture, while the route coordinate restores the route. -/
def InstalledActionExactAt
    (origin : RepairFailureOriginAt depth) :
    ActualRepairFailureAt depth origin → Prop :=
  match origin with
  | .tenureCapture _ => fun actual =>
      actual.down.source.installed.payload.disposition =
        sourceGeneratedUBIDisposition
  | .routeBottleneck _ => fun actual =>
      actual.actual.installed.payload.disposition =
        sourceGeneratedRouteRestoration

theorem installedActionExact
    (actual : ActualRepairFailureAt depth origin) :
    InstalledActionExactAt origin actual := by
  cases origin with
  | tenureCapture _ => exact actual.down.source.exactDisposition
  | routeBottleneck _ => exact actual.originActionExact

def SelectedWriteCommutesAt
    (origin : RepairFailureOriginAt depth) :
    ActualRepairFailureAt depth origin → Prop :=
  match origin with
  | .tenureCapture _ => fun actual =>
      actual.down.ordinarySelectedWrite.sourceRow.CommutesWithWorld
  | .routeBottleneck _ => fun actual =>
      actual.actual.applied.selectedWrite.sourceRow.CommutesWithWorld

/-- Branch-polymorphic selected-write commuting proof. -/
theorem selectedWriteCommutes (actual : ActualRepairFailureAt depth origin) :
    SelectedWriteCommutesAt origin actual := by
  cases origin with
  | tenureCapture _ => exact actual.down.ordinarySelectedWrite_commutes
  | routeBottleneck _ => exact actual.selectedWriteCommutes

def RootFactorizesAt
    (origin : RepairFailureOriginAt depth) :
    ActualRepairFailureAt depth origin → Prop :=
  match origin with
  | .tenureCapture _ => fun actual =>
      actual.down.source.installed.RootAnswerAndNextFactorizes
  | .routeBottleneck _ => fun actual =>
      actual.actual.installed.RootAnswerAndNextFactorizes

theorem rootFactorizes (actual : ActualRepairFailureAt depth origin) :
    RootFactorizesAt origin actual := by
  cases origin with
  | tenureCapture _ => exact actual.down.appliedReform.rootFactorization
  | routeBottleneck _ => exact actual.rootFactorization

def ComponentOutcomeExactAt
    (origin : RepairFailureOriginAt depth) :
    ActualRepairFailureAt depth origin → Prop :=
  match origin with
  | .tenureCapture _ => fun actual =>
      ubiRecognition.law.toProjectionLaw.outcomeAt PUnit.unit
          (jointRoot.emitted (temporalVisitAt depth).current) =
        (.inl ⟨actual.down.source.installed.active,
          actual.down.source.installed.payload⟩ :
          SourceNativeProjectionFiberAt ubiRecognition.law.toProjectionLaw
            PUnit.unit (jointRoot.emitted
              (temporalVisitAt depth).current))
  | .routeBottleneck _ => fun actual =>
      routeOutageRestorationRecognition.law.toProjectionLaw.outcomeAt
          PUnit.unit (jointRoot.emitted
            (temporalVisitAt depth).current) =
        (.inl ⟨actual.actual.installed.active,
          actual.actual.installed.payload⟩ :
          SourceNativeProjectionFiberAt
            routeOutageRestorationRecognition.law.toProjectionLaw PUnit.unit
            (jointRoot.emitted (temporalVisitAt depth).current))

theorem componentOutcomeExact
    (actual : ActualRepairFailureAt depth origin) :
    ComponentOutcomeExactAt origin actual := by
  cases origin with
  | tenureCapture _ => exact actual.down.componentOutcome_eq_activePayload
  | routeBottleneck _ => exact actual.componentOutcomeExact

def wholeLedgerWriteBack
    (actual : ActualRepairFailureAt depth origin) := by
  cases origin with
  | tenureCapture _ => exact actual.down.wholeLedgerWriteBack
  | routeBottleneck _ => exact actual.actual.applied.wholeLedgerWriteBack

def generatedNext
    (actual : ActualRepairFailureAt depth origin) :
    SourceNativeAuthoritativeRootCurrentAt
      M9ProofCarryingRenewalInquiryRoot.N := by
  cases origin with
  | tenureCapture _ => exact actual.down.generatedNext
  | routeBottleneck _ => exact actual.actual.applied.generatedNext

def projection
    (_actual : ActualRepairFailureAt depth origin) :
    jointRoot.toAuthoritativeRoot.source.projectionLaw.Projection :=
  match origin with
  | .tenureCapture _ => jointUBIProjection
  | .routeBottleneck _ => jointRouteOutageRestorationProjection

def repair (_actual : ActualRepairFailureAt depth origin) : ExactExitRepair :=
  match origin with
  | .tenureCapture _ => .removeCapture
  | .routeBottleneck _ => .restoreRoute

end ActualRepairFailureAt

/-! ## Common exactness -/

theorem actualRepairFailure_rootOccurrence_exact
    {depth : Nat} {origin : RepairFailureOriginAt depth}
    (actual : ActualRepairFailureAt depth origin) :
    actual.rootOccurrence =
      jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
        (temporalVisitAt depth) := by
  cases origin with
  | tenureCapture _ => exact actual.down.rootOccurrence_eq
  | routeBottleneck _ => exact actual.rootOccurrenceExact

theorem actualRepairFailure_wholeLedger_exact
    {depth : Nat} {origin : RepairFailureOriginAt depth}
    (actual : ActualRepairFailureAt depth origin) :
    HEq actual.wholeLedgerWriteBack
      (jointRoot.toAuthoritativeRoot.toLedgerRoot
        |>.generatedAtTemporalVisit
          (temporalVisitAt depth)).wholeLedgerWriteBack := by
  cases origin with
  | tenureCapture _ => exact heq_of_eq rfl
  | routeBottleneck _ => exact heq_of_eq actual.wholeLedgerExact

theorem actualRepairFailure_generatedNext_exact
    {depth : Nat} {origin : RepairFailureOriginAt depth}
    (actual : ActualRepairFailureAt depth origin) :
    actual.generatedNext =
      jointRoot.generatedNextCurrentAt (temporalVisitAt depth) := by
  cases origin with
  | tenureCapture _ => exact actual.down.generatedNext_eq_rootCompiler
  | routeBottleneck _ => exact actual.generatedNextExact

theorem actualRepairFailure_projection_exact
    {depth : Nat} {origin : RepairFailureOriginAt depth}
    (actual : ActualRepairFailureAt depth origin) :
    actual.projection =
      match origin with
      | .tenureCapture _ => jointUBIProjection
      | .routeBottleneck _ => jointRouteOutageRestorationProjection := by
  cases origin <;> rfl

theorem actualRepairFailure_repair_exact
    {depth : Nat} {origin : RepairFailureOriginAt depth}
    (actual : ActualRepairFailureAt depth origin) :
    actual.repair = canonicalRepairAt origin := by
  cases origin <;> rfl

/-! ## Exact two-branch authority geometry -/

theorem canonical_actual_pair_shared_root_distinct_authority (depth : Nat) :
    let tenure := sourceGeneratedActualTenureRepairFailureAt depth
    let route := sourceGeneratedActualRouteRepairFailureAt depth
    tenure.rootOccurrence = route.rootOccurrence ∧
      HEq tenure.sourceEntry route.sourceEntry ∧
      ActualRepairFailureAt.SourceConsumerExactAt
        (tenureCaptureOriginAt depth) tenure ∧
      ActualRepairFailureAt.SourceConsumerExactAt
        (routeBottleneckOriginAt depth) route ∧
      ActualRepairFailureAt.InstalledActionExactAt
        (tenureCaptureOriginAt depth) tenure ∧
      ActualRepairFailureAt.InstalledActionExactAt
        (routeBottleneckOriginAt depth) route ∧
      HEq tenure.wholeLedgerWriteBack route.wholeLedgerWriteBack ∧
      tenure.generatedNext = route.generatedNext ∧
      tenure.projection ≠ route.projection ∧
      tenure.repair ≠ route.repair := by
  let tenure := sourceGeneratedActualTenureRepairFailureAt depth
  let route := sourceGeneratedActualRouteRepairFailureAt depth
  refine ⟨?_, HEq.rfl,
    ActualRepairFailureAt.sourceConsumerExact tenure,
    ActualRepairFailureAt.sourceConsumerExact route,
    ActualRepairFailureAt.installedActionExact tenure,
    ActualRepairFailureAt.installedActionExact route,
    ?_, ?_, ?_, ?_⟩
  · calc
      tenure.rootOccurrence =
          (jointRoot.toAuthoritativeRoot.toLedgerRoot
            |>.exactTemporalCausalEventAt (temporalVisitAt depth)) :=
        actualRepairFailure_rootOccurrence_exact tenure
      _ = route.rootOccurrence :=
        (actualRepairFailure_rootOccurrence_exact route).symm
  · exact (actualRepairFailure_wholeLedger_exact tenure).trans
      (actualRepairFailure_wholeLedger_exact route).symm
  · calc
      tenure.generatedNext =
          jointRoot.generatedNextCurrentAt (temporalVisitAt depth) :=
        actualRepairFailure_generatedNext_exact tenure
      _ = route.generatedNext :=
        (actualRepairFailure_generatedNext_exact route).symm
  · exact routeOutage_projection_ne_ubi_projection.symm
  · change ExactExitRepair.removeCapture ≠ ExactExitRepair.restoreRoute
    decide

theorem canonical_cross_retypes_are_empty (depth : Nat) :
    IsEmpty (SourceInstalledProofCarryingExitRepairRenewalAt
        depth .restoreRoute) ∧
      IsEmpty (SourceGeneratedProofCarryingPeriodicRouteRestorationAt
        depth .removeCapture) :=
  ⟨M14ProofCarryingExitRepairRenewalRegression.SourceInstalledProofCarryingExitRepairRenewalAt.restoreRoute_is_not_actual_in_tenure_coordinate
      depth,
    periodicRouteRemoveCapture_isEmpty depth⟩

theorem actualRepairFailure_mouth_has_no_registry_trace_or_future
    (depth : Nat) : True := by
  let tenure := sourceGeneratedActualTenureRepairFailureAt depth
  let route := sourceGeneratedActualRouteRepairFailureAt depth
  fail_if_success exact tenure.origin
  fail_if_success exact route.origin
  fail_if_success exact tenure.domainRegistry
  fail_if_success exact route.domainRegistry
  fail_if_success exact tenure.coverage
  fail_if_success exact route.coverage
  fail_if_success exact tenure.trace
  fail_if_success exact route.trace
  fail_if_success exact tenure.measure
  fail_if_success exact route.measure
  fail_if_success exact tenure.probability
  fail_if_success exact route.probability
  fail_if_success exact tenure.completedFuture
  fail_if_success exact route.completedFuture
  trivial

end
end M14ActualRepairFailureOccurrence
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ActualRepairFailureOccurrence.sourceGeneratedActualTenureRepairFailureAt
#print axioms SaturationMonoid.ProcessGame.Society.M14ActualRepairFailureOccurrence.sourceGeneratedActualRouteRepairFailureAt
#print axioms SaturationMonoid.ProcessGame.Society.M14ActualRepairFailureOccurrence.every_origin_has_actualRepairFailure
#print axioms SaturationMonoid.ProcessGame.Society.M14ActualRepairFailureOccurrence.ActualRepairFailureAt.sourceConsumerExact
#print axioms SaturationMonoid.ProcessGame.Society.M14ActualRepairFailureOccurrence.ActualRepairFailureAt.installedActionExact
#print axioms SaturationMonoid.ProcessGame.Society.M14ActualRepairFailureOccurrence.ActualRepairFailureAt.rootFactorizes
#print axioms SaturationMonoid.ProcessGame.Society.M14ActualRepairFailureOccurrence.ActualRepairFailureAt.componentOutcomeExact
#print axioms SaturationMonoid.ProcessGame.Society.M14ActualRepairFailureOccurrence.canonical_actual_pair_shared_root_distinct_authority
#print axioms SaturationMonoid.ProcessGame.Society.M14ActualRepairFailureOccurrence.canonical_cross_retypes_are_empty
