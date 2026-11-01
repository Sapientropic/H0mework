import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Root.Economy.Robustness.CaptureChokepointBasinRecovery
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Consumer.Policy.ProofCarryingExitRepairRegression

/-!
# M14 full-domain reachability collision

The scalar zero-capacity collision survives the strongest currently generated
domain readout.  Structural tenure capture and an uncaptured missing-route
bottleneck each erase the feasible edge of every generated essential-access
domain, so both induce the same empty `Set`-valued reachability mask.  Their
exact source origins and canonical proof-carrying repairs nevertheless remain
different.  Capture provenance retains an activated, source-owned settlement
residual; route provenance instead supplies no capture verdict and exact
missing-route witnesses.

The mask is computed after both causes have been generated.  It is not a
producer premise, sector registry, coverage table, or second matching fold.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14FullDomainReachabilityCollision

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations Exchange Settlement Price Money UBI Policy
open Renewal Capacity Space CrossingCost
open Settlement.SourceOwnedSettlementCompiler
open UBI.Capacity UBI.Capacity.SourceOwnedExitGeometryCompilerAt
open UBI.Capture
open M3FiniteExchangeFixture M3ExchangeSettlementPriceRegression
open M14UBIExitCapacityFixture
open M14CaptureResponsibilityDispositionRegression
open M14ZeroCapacityCausalNonidentifiabilityRegression
open M14EssentialAccessRelationFixture
open M14EssentialAccessSectorRegression
open M14ActionableFuturePortfolio
open M14PortfolioMaintenanceDeath
open M14PortfolioCaptureDeath
open M14TenureCaptureRouteRepairNoGoRegression
open M14ProofCarryingExitRepairRegression
open M14PeriodicDeathRepairNormalization
open M14PeriodicViabilityRenewalReceipt
open M14EconomicViability
open M14AdjacentEconomicViabilityBoundary
open M14StructuralRentCaptureRegression
open M14CaptureChokepointBasinRecovery

/-! ## One dependent feasible-edge fibre over the existing cause carrier -/

abbrev RouteMissingDomainActionableAt
    (depth : Nat) (domain : EssentialAccessRelationAuthority) :=
  ExactFeasibleExitEdgeAt (routeIncidenceMissingGeometryAt depth)
    ExitFutureCode.leave (domainSlotAt depth domain)

/-- The existing exact failure origin selects the relevant feasible-edge
fibre.  No new cause tag or domain registry is introduced. -/
def DomainFeasibleAt
    (depth : Nat) (origin : RepairFailureOriginAt depth)
    (domain : EssentialAccessRelationAuthority) : Type :=
  match origin with
  | .tenureCapture _ =>
      M14PortfolioCaptureDeath.CapturedDomainActionableAt depth domain
  | .routeBottleneck _ => RouteMissingDomainActionableAt depth domain

theorem captureOrigin_blocks_every_domain
    (depth : Nat) (domain : EssentialAccessRelationAuthority) :
    IsEmpty (DomainFeasibleAt depth (tenureCaptureOriginAt depth) domain) := by
  change IsEmpty
    (M14PortfolioCaptureDeath.CapturedDomainActionableAt depth domain)
  exact fullCapture_blocks_every_essential_domain depth domain

theorem routeMissing_blocks_every_domain
    (depth : Nat) (domain : EssentialAccessRelationAuthority) :
    IsEmpty (RouteMissingDomainActionableAt depth domain) :=
  ⟨fun edge =>
    (route_incidence_missing_at depth ExitFutureCode.leave
      (domainCrossingAt depth domain)).false edge.routeReceipt⟩

theorem routeOrigin_blocks_every_domain
    (depth : Nat) (domain : EssentialAccessRelationAuthority) :
    IsEmpty (DomainFeasibleAt depth (routeBottleneckOriginAt depth) domain) := by
  change IsEmpty (RouteMissingDomainActionableAt depth domain)
  exact routeMissing_blocks_every_domain depth domain

/-! ## Full observation, computed rather than submitted -/

def domainReachabilityMaskAt
    (depth : Nat) (origin : RepairFailureOriginAt depth) :
    Set EssentialAccessRelationAuthority :=
  {domain | Nonempty (DomainFeasibleAt depth origin domain)}

abbrev FullDomainReachabilityObservation :=
  Nat × Set EssentialAccessRelationAuthority

def fullDomainReachabilityObservationAt
    (depth : Nat) (origin : RepairFailureOriginAt depth) :
    FullDomainReachabilityObservation :=
  (failureCapacityReadoutAt depth origin,
    domainReachabilityMaskAt depth origin)

theorem canonical_domain_masks_equal (depth : Nat) :
    domainReachabilityMaskAt depth (tenureCaptureOriginAt depth) =
      domainReachabilityMaskAt depth (routeBottleneckOriginAt depth) := by
  funext domain
  apply propext
  change
    Nonempty
        (DomainFeasibleAt depth (tenureCaptureOriginAt depth) domain) ↔
      Nonempty
        (DomainFeasibleAt depth (routeBottleneckOriginAt depth) domain)
  constructor
  · rintro ⟨edge⟩
    exact False.elim ((captureOrigin_blocks_every_domain depth domain).false edge)
  · rintro ⟨edge⟩
    exact False.elim ((routeOrigin_blocks_every_domain depth domain).false edge)

theorem canonical_full_observations_equal (depth : Nat) :
    fullDomainReachabilityObservationAt depth (tenureCaptureOriginAt depth) =
      fullDomainReachabilityObservationAt depth
        (routeBottleneckOriginAt depth) := by
  apply Prod.ext
  · exact failure_readouts_equal depth
  · exact canonical_domain_masks_equal depth

theorem canonical_origins_distinct (depth : Nat) :
    tenureCaptureOriginAt depth ≠ routeBottleneckOriginAt depth := by
  intro equality
  cases equality

/-! ## Source-generated collision -/

/-- Two exact, distinct causes indexed by one depth-only producer.  The
collision records the full domain mask only as a generated readout; causal
origin, repair authority, and residual authority remain source-side. -/
structure SourceGeneratedFullDomainReachabilityCollisionAt
    (depth : Nat)
    (left right : RepairFailureOriginAt depth) : Type 18 where
  private mk ::
  leftExact : left = tenureCaptureOriginAt depth
  rightExact : right = routeBottleneckOriginAt depth
  captureChokepoint :
    SourceGeneratedCaptureChokepointBasinRecoveryAt depth
      (periodicStructuralRentCaptureAt depth)
      (portfolioCaptureDeathAt depth)
      (sourceGeneratedAdjacentEconomicViabilityBoundaryAt depth)
      (sourceGeneratedPeriodicEconomicViabilityAt depth)
  leftRepair : SourceGeneratedProofCarryingExitRepairAt left
    (canonicalRepairAt left)
  rightRepair : SourceGeneratedProofCarryingExitRepairAt right
    (canonicalRepairAt right)
  leftDomainsEmpty : (domain : EssentialAccessRelationAuthority) →
    IsEmpty (DomainFeasibleAt depth left domain)
  rightDomainsEmpty : (domain : EssentialAccessRelationAuthority) →
    IsEmpty (DomainFeasibleAt depth right domain)
  sameScalar : failureCapacityReadoutAt depth left =
    failureCapacityReadoutAt depth right
  sameMask : domainReachabilityMaskAt depth left =
    domainReachabilityMaskAt depth right
  sameObservation : fullDomainReachabilityObservationAt depth left =
    fullDomainReachabilityObservationAt depth right
  originsDistinct : left ≠ right
  repairsDistinct : canonicalRepairAt left ≠ canonicalRepairAt right
  captureResidualLive : Nonempty
    (OpenSettlementAt.ActivatedResidualConsumerAt
      (exactOpenSettlement exactResidualActivation))
  captureResidualSourceOwned : Nonempty (SourceOwnsResponsibilityIncidence V
    (P.boundarySource
      capturedProgram.purchasingPowerStanding.activatedConsumer.activation)
    (exactOpenSettlement exactResidualActivation).obligation)
  routeUncaptured : ¬ noCapture.Captures ExitFutureCode.leave
  routeIncidenceMissing : (domain : EssentialAccessRelationAuthority) →
    IsEmpty ((routeIncidenceMissingGeometryAt depth).RoutesAt
      ExitFutureCode.leave (domainCrossingAt depth domain))

/-- Sole producer: the two causes, full observation, canonical repairs, and
capture residual are regenerated from `depth`. -/
def sourceGeneratedFullDomainReachabilityCollisionAt (depth : Nat) :
    SourceGeneratedFullDomainReachabilityCollisionAt depth
      (tenureCaptureOriginAt depth) (routeBottleneckOriginAt depth) := by
  let capture := sourceGeneratedCaptureChokepointBasinRecoveryAt depth
  exact
    { leftExact := rfl
      rightExact := rfl
      captureChokepoint := capture
      leftRepair :=
        SourceGeneratedProofCarryingExitRepairAt.generate
          (tenureCaptureOriginAt depth)
      rightRepair :=
        SourceGeneratedProofCarryingExitRepairAt.generate
          (routeBottleneckOriginAt depth)
      leftDomainsEmpty := captureOrigin_blocks_every_domain depth
      rightDomainsEmpty := routeOrigin_blocks_every_domain depth
      sameScalar := failure_readouts_equal depth
      sameMask := canonical_domain_masks_equal depth
      sameObservation := canonical_full_observations_equal depth
      originsDistinct := canonical_origins_distinct depth
      repairsDistinct := exact_causes_generate_different_repairs depth
      captureResidualLive := capture.activatedResidualConsumer
      captureResidualSourceOwned := capture.sourceOwnedResidual
      routeUncaptured := uncaptured_leave_has_no_capture_verdict
      routeIncidenceMissing := fun domain =>
        route_incidence_missing_at depth ExitFutureCode.leave
          (domainCrossingAt depth domain) }

theorem every_depth_generates_full_domain_reachability_collision
    (depth : Nat) :
    Nonempty (SourceGeneratedFullDomainReachabilityCollisionAt depth
      (tenureCaptureOriginAt depth) (routeBottleneckOriginAt depth)) :=
  ⟨sourceGeneratedFullDomainReachabilityCollisionAt depth⟩

/-! ## Controls and mouth guards -/

theorem good_full_noCapture_keeps_every_domain
    (depth : Nat) (domain : EssentialAccessRelationAuthority) :
    Nonempty (SourceGeneratedEssentialDomainActionableAt depth domain) ∧
      ¬ noCapture.Captures ExitFutureCode.leave :=
  ⟨⟨sourceGeneratedEssentialDomainActionableAt depth domain⟩,
    uncaptured_leave_has_no_capture_verdict⟩

theorem maintenance_is_not_full_domain_zero_collision (depth : Nat) :
    (stableGeometryCompilerAt depth).actionableExitCapacity = 1 ∧
      Nonempty (SourceGeneratedStableEssentialDomainActionableAt
        depth tenureAuthority) ∧
      IsEmpty (SourceGeneratedStableDomainServiceIncidenceAt depth
        (exactEssentialAccessSeed .health)) ∧
      ¬ noCapture.Captures ExitFutureCode.leave :=
  let death := portfolioMaintenanceDeathAt depth
  ⟨death.exactCapacity, ⟨death.tenureActionable⟩,
    death.healthServiceEmpty, death.uncaptured⟩

theorem collision_mouth_has_no_submitted_observation_or_future
    (depth : Nat) : True := by
  let collision := sourceGeneratedFullDomainReachabilityCollisionAt depth
  fail_if_success exact collision.submittedMask
  fail_if_success exact collision.capacityPremise
  fail_if_success exact collision.domainTable
  fail_if_success exact collision.sectorRegistry
  fail_if_success exact collision.reconstruct
  fail_if_success exact collision.coverage
  fail_if_success exact collision.completedHistory
  fail_if_success exact collision.futureTable
  fail_if_success exact collision.perturbationRegistry
  trivial

end
end M14FullDomainReachabilityCollision
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14FullDomainReachabilityCollision.captureOrigin_blocks_every_domain
#print axioms SaturationMonoid.ProcessGame.Society.M14FullDomainReachabilityCollision.routeOrigin_blocks_every_domain
#print axioms SaturationMonoid.ProcessGame.Society.M14FullDomainReachabilityCollision.canonical_full_observations_equal
#print axioms SaturationMonoid.ProcessGame.Society.M14FullDomainReachabilityCollision.sourceGeneratedFullDomainReachabilityCollisionAt
