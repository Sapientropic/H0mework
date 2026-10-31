import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Root.Economy.Identification.FullDomainReachabilityCollision

/-!
# M14 full-domain reachability observer no-section

Capacity together with the full generated essential-domain reachability mask
still cannot reconstruct either the exact failure origin or its canonical
proof-carrying repair.  Structural capture and an uncaptured missing-route
bottleneck have the same computed observation, while their source origins and
repairs are distinct.

The observer is a readout of already generated failures.  It is never accepted
as a cause, repair, domain table, or policy premise.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingFullDomainReachabilityNoSectionRegression

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations Exchange Settlement Price Money UBI Policy
open Renewal Capacity Space CrossingCost
open UBI.Capacity
open M14UBIExitCapacityFixture
open M14EssentialAccessRelationFixture
open M14EssentialAccessSectorRegression
open M14ActionableFuturePortfolio
open M14PortfolioMaintenanceDeath
open M14TenureCaptureRouteRepairNoGoRegression
open M14ProofCarryingExitRepairRegression
open M14ActualEconomicViabilityPath
open M14CaptureChokepointBasinRecovery
open M14FullDomainReachabilityCollision

theorem fullDomainReachabilityCollisionAt (depth : Nat) :
    Nonempty (SourceGeneratedFullDomainReachabilityCollisionAt depth
        (tenureCaptureOriginAt depth) (routeBottleneckOriginAt depth)) ∧
      fullDomainReachabilityObservationAt depth
          (tenureCaptureOriginAt depth) =
        fullDomainReachabilityObservationAt depth
          (routeBottleneckOriginAt depth) ∧
      tenureCaptureOriginAt depth ≠ routeBottleneckOriginAt depth ∧
      canonicalRepairAt (tenureCaptureOriginAt depth) ≠
        canonicalRepairAt (routeBottleneckOriginAt depth) := by
  let collision := sourceGeneratedFullDomainReachabilityCollisionAt depth
  exact
    ⟨⟨collision⟩, collision.sameObservation,
      collision.originsDistinct, collision.repairsDistinct⟩

/-- No section of the full observer can recover every exact source cause.
The `LeftInverse` direction is deliberate: reconstruction follows observation. -/
theorem no_full_domain_observation_leftInverse_reconstructs_cause
    (depth : Nat) :
    ¬ ∃ reconstruct :
        FullDomainReachabilityObservation → RepairFailureOriginAt depth,
      Function.LeftInverse reconstruct
        (fullDomainReachabilityObservationAt depth) := by
  rintro ⟨reconstruct, leftInverse⟩
  let collision := sourceGeneratedFullDomainReachabilityCollisionAt depth
  have originsEqual :
      tenureCaptureOriginAt depth = routeBottleneckOriginAt depth := by
    calc
      tenureCaptureOriginAt depth =
          reconstruct (fullDomainReachabilityObservationAt depth
            (tenureCaptureOriginAt depth)) :=
        (leftInverse (tenureCaptureOriginAt depth)).symm
      _ = reconstruct (fullDomainReachabilityObservationAt depth
            (routeBottleneckOriginAt depth)) :=
        congrArg reconstruct collision.sameObservation
      _ = routeBottleneckOriginAt depth :=
        leftInverse (routeBottleneckOriginAt depth)
  exact collision.originsDistinct originsEqual

/-- Even a weaker demand—recover only the canonical repair attached to every
source cause—is impossible from the same observation. -/
theorem no_full_domain_observation_reconstructs_canonical_repair
    (depth : Nat) :
    ¬ ∃ reconstruct : FullDomainReachabilityObservation → ExactExitRepair,
      ∀ origin : RepairFailureOriginAt depth,
        reconstruct (fullDomainReachabilityObservationAt depth origin) =
          canonicalRepairAt origin := by
  rintro ⟨reconstruct, reconstructs⟩
  let collision := sourceGeneratedFullDomainReachabilityCollisionAt depth
  have repairsEqual :
      canonicalRepairAt (tenureCaptureOriginAt depth) =
        canonicalRepairAt (routeBottleneckOriginAt depth) := by
    calc
      canonicalRepairAt (tenureCaptureOriginAt depth) =
          reconstruct (fullDomainReachabilityObservationAt depth
            (tenureCaptureOriginAt depth)) :=
        (reconstructs (tenureCaptureOriginAt depth)).symm
      _ = reconstruct (fullDomainReachabilityObservationAt depth
            (routeBottleneckOriginAt depth)) :=
        congrArg reconstruct collision.sameObservation
      _ = canonicalRepairAt (routeBottleneckOriginAt depth) :=
        reconstructs (routeBottleneckOriginAt depth)
  exact collision.repairsDistinct repairsEqual

theorem fullDomainReachabilityCollisionControls (depth : Nat) :
    (∀ domain : EssentialAccessRelationAuthority,
      Nonempty (SourceGeneratedEssentialDomainActionableAt depth domain)) ∧
      (stableGeometryCompilerAt depth).actionableExitCapacity = 1 ∧
      Nonempty (SourceGeneratedStableEssentialDomainActionableAt
        depth tenureAuthority) ∧
      IsEmpty (SourceGeneratedStableDomainServiceIncidenceAt depth
        (exactEssentialAccessSeed .health)) ∧
      IsEmpty (repairedConfigurationAt depth ⟶
        captureConfigurationAt (depth + 1)) := by
  let maintenance := maintenance_is_not_full_domain_zero_collision depth
  exact
    ⟨fun domain => (good_full_noCapture_keeps_every_domain depth domain).1,
      maintenance.1, maintenance.2.1, maintenance.2.2.1,
      current_quiver_has_no_viable_to_capture_shock depth⟩

structure ProofCarryingFullDomainReachabilityCollisionCertificate : Prop where
  everyDepthCollision : ∀ depth : Nat,
    Nonempty (SourceGeneratedFullDomainReachabilityCollisionAt depth
        (tenureCaptureOriginAt depth) (routeBottleneckOriginAt depth)) ∧
      fullDomainReachabilityObservationAt depth
          (tenureCaptureOriginAt depth) =
        fullDomainReachabilityObservationAt depth
          (routeBottleneckOriginAt depth) ∧
      tenureCaptureOriginAt depth ≠ routeBottleneckOriginAt depth ∧
      canonicalRepairAt (tenureCaptureOriginAt depth) ≠
        canonicalRepairAt (routeBottleneckOriginAt depth)
  noCauseLeftInverse : ∀ depth : Nat,
    ¬ ∃ reconstruct :
        FullDomainReachabilityObservation → RepairFailureOriginAt depth,
      Function.LeftInverse reconstruct
        (fullDomainReachabilityObservationAt depth)
  noCanonicalRepairReconstruction : ∀ depth : Nat,
    ¬ ∃ reconstruct : FullDomainReachabilityObservation → ExactExitRepair,
      ∀ origin : RepairFailureOriginAt depth,
        reconstruct (fullDomainReachabilityObservationAt depth origin) =
          canonicalRepairAt origin
  controls : ∀ depth : Nat,
    (∀ domain : EssentialAccessRelationAuthority,
      Nonempty (SourceGeneratedEssentialDomainActionableAt depth domain)) ∧
      (stableGeometryCompilerAt depth).actionableExitCapacity = 1 ∧
      Nonempty (SourceGeneratedStableEssentialDomainActionableAt
        depth tenureAuthority) ∧
      IsEmpty (SourceGeneratedStableDomainServiceIncidenceAt depth
        (exactEssentialAccessSeed .health)) ∧
      IsEmpty (repairedConfigurationAt depth ⟶
        captureConfigurationAt (depth + 1))

theorem proofCarryingFullDomainReachabilityCollisionDirectConsumer :
    ProofCarryingFullDomainReachabilityCollisionCertificate where
  everyDepthCollision := fullDomainReachabilityCollisionAt
  noCauseLeftInverse :=
    no_full_domain_observation_leftInverse_reconstructs_cause
  noCanonicalRepairReconstruction :=
    no_full_domain_observation_reconstructs_canonical_repair
  controls := fullDomainReachabilityCollisionControls

end
end M14ProofCarryingFullDomainReachabilityNoSectionRegression
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingFullDomainReachabilityNoSectionRegression.fullDomainReachabilityCollisionAt
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingFullDomainReachabilityNoSectionRegression.no_full_domain_observation_leftInverse_reconstructs_cause
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingFullDomainReachabilityNoSectionRegression.no_full_domain_observation_reconstructs_canonical_repair
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingFullDomainReachabilityNoSectionRegression.proofCarryingFullDomainReachabilityCollisionDirectConsumer
