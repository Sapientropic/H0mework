import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Consumer.Policy.ProofCarryingExitRepairRenewalRegression
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Consumer.Economy.Route.ProofCarryingPeriodicRouteOutageRestorationRegression

/-!
# M14 direct consumer for the actual-source-generated route origin

The canonical route-bottleneck origin now carries the independently installed
periodic route-restoration occurrence as a private source witness.  Its old
zero-capacity geometry remains a diagnostic readout; it no longer creates the
origin.  The same source then feeds the existing proof-carrying repair
compiler, which returns the unique effective `restoreRoute` action.

The UBI-tenure coordinate still rejects `restoreRoute`; this is authority
separation, not evidence that the independent route occurrence is absent.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingActualRouteOriginRegression

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Renewal UBI Policy
open M9ProofCarryingRenewalInquiryRoot
open M14UBIPeriodicRootHistory
open M14SourceRouteOutageRestoration
open M14PeriodicRouteOutageRestoration
open M14TenureCaptureRouteRepairNoGoRegression
open M14ProofCarryingExitRepairRegression
open M14ProofCarryingExitRepairRenewalRegression

theorem actualRouteOriginAt (depth : Nat) :
    let actual := sourceGeneratedPeriodicRouteOutageRestorationAt depth
    Nonempty (SourceGeneratedPeriodicRouteOutageRestorationAt depth) ∧
      actual.installed.payload.consumer = sourceRouteOutageRestriction ∧
      actual.installed.payload.disposition =
        sourceGeneratedRouteRestoration ∧
      canonicalRepairAt (routeBottleneckOriginAt depth) = .restoreRoute ∧
      failureCapacityReadoutAt depth (routeBottleneckOriginAt depth) = 0 ∧
      repairOutcomeCapacityAt depth (routeBottleneckOriginAt depth)
        .restoreRoute = 1 ∧
      (∀ candidate : ExactExitRepair,
        EffectiveRepairAt depth (routeBottleneckOriginAt depth) candidate ↔
          candidate = .restoreRoute) := by
  let actual := sourceGeneratedPeriodicRouteOutageRestorationAt depth
  exact ⟨(routeBottleneckFailureAt depth).actualRouteRestoration,
    actual.consumerExact,
    actual.actionExact,
    rfl,
    route_bottleneck_failure_readout_eq_zero depth,
    restore_route_repairs_bottleneck_at depth,
    route_effective_repair_iff depth⟩

theorem actualRouteAndTenureCoordinateAreDistinct (depth : Nat) :
    Nonempty (SourceGeneratedPeriodicRouteOutageRestorationAt depth) ∧
      IsEmpty (SourceInstalledProofCarryingExitRepairRenewalAt
        depth .restoreRoute) ∧
      jointRouteOutageRestorationProjection ≠ jointUBIProjection :=
  ⟨⟨sourceGeneratedPeriodicRouteOutageRestorationAt depth⟩,
    SourceInstalledProofCarryingExitRepairRenewalAt.restoreRoute_is_not_actual_in_tenure_coordinate
      depth,
    routeOutage_projection_ne_ubi_projection⟩

/-- External-mouth regression: neither exact failure wrapper exposes a public
constructor after importing this module. -/
theorem exactFailureConstructorsArePrivate : True := by
  fail_if_success exact RouteBottleneckFailureAt.mk
  fail_if_success exact TenureCaptureFailureAt.mk
  trivial

structure ProofCarryingActualRouteOriginCertificateAt
    (source : TenureCaptureRouteRepairNoGoCertificate) : Prop where
  sourceProvenance : ∀ depth : Nat,
    ActualRouteOriginProvenanceAt depth
  everyDepthActualOrigin : ∀ depth : Nat,
    let actual := sourceGeneratedPeriodicRouteOutageRestorationAt depth
    Nonempty (SourceGeneratedPeriodicRouteOutageRestorationAt depth) ∧
      actual.installed.payload.consumer = sourceRouteOutageRestriction ∧
      actual.installed.payload.disposition =
        sourceGeneratedRouteRestoration ∧
      canonicalRepairAt (routeBottleneckOriginAt depth) = .restoreRoute ∧
      failureCapacityReadoutAt depth (routeBottleneckOriginAt depth) = 0 ∧
      repairOutcomeCapacityAt depth (routeBottleneckOriginAt depth)
        .restoreRoute = 1 ∧
      (∀ candidate : ExactExitRepair,
        EffectiveRepairAt depth (routeBottleneckOriginAt depth) candidate ↔
          candidate = .restoreRoute)
  everyDepthAuthoritySeparation : ∀ depth : Nat,
    Nonempty (SourceGeneratedPeriodicRouteOutageRestorationAt depth) ∧
      IsEmpty (SourceInstalledProofCarryingExitRepairRenewalAt
        depth .restoreRoute) ∧
      jointRouteOutageRestorationProjection ≠ jointUBIProjection
  privateFailureMouth : True

theorem proofCarryingActualRouteOriginDirectConsumerAt
    (source : TenureCaptureRouteRepairNoGoCertificate) :
    ProofCarryingActualRouteOriginCertificateAt source where
  sourceProvenance := source.everyDepthActualRouteOriginProvenance
  everyDepthActualOrigin := actualRouteOriginAt
  everyDepthAuthoritySeparation :=
    actualRouteAndTenureCoordinateAreDistinct
  privateFailureMouth := exactFailureConstructorsArePrivate

theorem proofCarryingActualRouteOriginDirectConsumer :
    ProofCarryingActualRouteOriginCertificateAt
      tenureCaptureRouteRepairNoGoDirectConsumer :=
  proofCarryingActualRouteOriginDirectConsumerAt
    tenureCaptureRouteRepairNoGoDirectConsumer

end
end M14ProofCarryingActualRouteOriginRegression
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingActualRouteOriginRegression.actualRouteOriginAt
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingActualRouteOriginRegression.actualRouteAndTenureCoordinateAreDistinct
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingActualRouteOriginRegression.proofCarryingActualRouteOriginDirectConsumerAt
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingActualRouteOriginRegression.proofCarryingActualRouteOriginDirectConsumer
