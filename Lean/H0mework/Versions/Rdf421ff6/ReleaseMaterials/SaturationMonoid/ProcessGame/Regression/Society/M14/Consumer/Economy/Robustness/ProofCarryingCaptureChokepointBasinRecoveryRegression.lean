import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Root.Economy.Robustness.CaptureChokepointBasinRecovery

/-!
# M14 direct consumer for capture-chokepoint basin recovery

This Prop-only consumer verifies that the same source-generated full-price
capture removes every existing essential-domain edge, while the exact
structural-rent responsibility, actual remove-capture edge, minimal basin
entry, and arbitrary requested finite viable continuation remain connected.

The uncaptured domain family is a same-source control, not a pre-shock
history.  The current Quiver explicitly has no viable-to-capture shock edge.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingCaptureChokepointBasinRecoveryRegression

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Exchange Settlement Price Money UBI Policy
open Renewal Capacity Space CrossingCost
open Settlement.SourceOwnedSettlementCompiler
open M3FiniteExchangeFixture M3ExchangeSettlementPriceRegression
open M14UBIExitCapacityFixture
open M14ZeroCapacityCausalNonidentifiabilityRegression
open M14EssentialAccessRelationFixture
open M14EssentialAccessSectorRegression
open M14ActionableFuturePortfolio
open M14PortfolioCaptureDeath
open M14TenureCaptureRouteRepairNoGoRegression
open M14StructuralRentCaptureRegression
open M14PeriodicViabilityRenewalReceipt
open M14AdjacentEconomicViabilityBoundary
open M14EconomicViability
open M14ActualEconomicViabilityPath
open M14MinimalEconomicViabilityHittingTime
open M14CaptureChokepointBasinRecovery

theorem captureChokepointBasinRecoveryAt
    (depth horizon : Nat) :
    Nonempty (SourceGeneratedCaptureChokepointBasinRecoveryAt depth
        (periodicStructuralRentCaptureAt depth)
        (portfolioCaptureDeathAt depth)
        (sourceGeneratedAdjacentEconomicViabilityBoundaryAt depth)
        (sourceGeneratedPeriodicEconomicViabilityAt depth)) ∧
      (∀ domain : EssentialAccessRelationAuthority,
        Nonempty (SourceGeneratedEssentialDomainActionableAt depth domain) ∧
          IsEmpty (M14PortfolioCaptureDeath.CapturedDomainActionableAt
            depth domain)) ∧
      domainCrossingAt depth tenureAuthority ≠
        domainCrossingAt depth healthAuthority ∧
      Nonempty (SourceGeneratedStructuralRentCaptureAt depth) ∧
      Nonempty (captureConfigurationAt depth ⟶
        repairedConfigurationAt depth) ∧
      Nonempty (SourceGeneratedViabilityPathCandidateAt
        (captureConfigurationAt depth)) ∧
      captureViabilityHittingTimeAt depth = 1 ∧
      captureViabilityHittingTimeAt depth ≤
        (captureFiniteViabilityPathCandidateAt depth horizon).path.length ∧
      (captureFiniteAttractorPathAt depth horizon).length = horizon + 1 ∧
      Nonempty ((repairedConfigurationAt (depth + horizon)).Viable) := by
  rcases structural_capture_chokepoint_is_in_viability_basin depth horizon with
    ⟨domains, crossings, rent, recoveryEdge,
      minimum, finitePath, targetViable⟩
  exact
    ⟨every_generated_structural_capture_is_a_domainwise_chokepoint depth,
      domains,
      crossings,
      rent,
      recoveryEdge,
      ⟨captureFiniteViabilityPathCandidateAt depth horizon⟩,
      minimum,
      capture_finite_continuation_respects_minimum depth horizon,
      finitePath,
      targetViable⟩

theorem captureChokepointStrictControls (depth : Nat) :
    IsEmpty (SourceGeneratedPortfolioCaptureDeathAt depth
        (fullPortfolioSourceAt depth) noCapture) ∧
      (¬ noCapture.Captures ExitFutureCode.leave) ∧
      failureCapacityReadoutAt depth (tenureCaptureOriginAt depth) =
        failureCapacityReadoutAt depth (routeBottleneckOriginAt depth) ∧
      failureCapacityReadoutAt depth (routeBottleneckOriginAt depth) = 0 ∧
      (∀ domain : EssentialAccessRelationAuthority,
        IsEmpty ((routeIncidenceMissingGeometryAt depth).RoutesAt
          ExitFutureCode.leave (domainCrossingAt depth domain))) ∧
      (stableGeometryCompilerAt depth).actionableExitCapacity = 1 ∧
      IsEmpty (SourceGeneratedStableDomainServiceIncidenceAt depth
        (exactEssentialAccessSeed .health)) ∧
      (∀ _fully : FullyFulfilledExchangeAt settlementCompiler openOccurrence,
        IsEmpty (RootInstalledTenurePurposeCaptureAt depth)) ∧
      IsEmpty (repairedConfigurationAt depth ⟶
        captureConfigurationAt (depth + 1)) := by
  let maintenance := maintenance_failure_is_not_capture_chokepoint depth
  exact
    ⟨noCapture_cannot_generate_capture_chokepoint depth,
      uncaptured_leave_has_no_structural_rent_verdict,
      failure_readouts_equal depth,
      route_bottleneck_failure_readout_eq_zero depth,
      fun domain =>
        (route_missing_is_not_capture_chokepoint_authority
          depth domain).1,
      maintenance.1,
      maintenance.2.1,
      fully_fulfilled_same_payment_has_no_chokepoint_rent depth,
      current_quiver_has_no_viable_to_capture_shock depth⟩

structure ProofCarryingCaptureChokepointBasinRecoveryCertificate : Prop where
  everyDepth : ∀ depth horizon : Nat,
    Nonempty (SourceGeneratedCaptureChokepointBasinRecoveryAt depth
        (periodicStructuralRentCaptureAt depth)
        (portfolioCaptureDeathAt depth)
        (sourceGeneratedAdjacentEconomicViabilityBoundaryAt depth)
        (sourceGeneratedPeriodicEconomicViabilityAt depth)) ∧
      (∀ domain : EssentialAccessRelationAuthority,
        Nonempty (SourceGeneratedEssentialDomainActionableAt depth domain) ∧
          IsEmpty (M14PortfolioCaptureDeath.CapturedDomainActionableAt
            depth domain)) ∧
      domainCrossingAt depth tenureAuthority ≠
        domainCrossingAt depth healthAuthority ∧
      Nonempty (SourceGeneratedStructuralRentCaptureAt depth) ∧
      Nonempty (captureConfigurationAt depth ⟶
        repairedConfigurationAt depth) ∧
      Nonempty (SourceGeneratedViabilityPathCandidateAt
        (captureConfigurationAt depth)) ∧
      captureViabilityHittingTimeAt depth = 1 ∧
      captureViabilityHittingTimeAt depth ≤
        (captureFiniteViabilityPathCandidateAt depth horizon).path.length ∧
      (captureFiniteAttractorPathAt depth horizon).length = horizon + 1 ∧
      Nonempty ((repairedConfigurationAt (depth + horizon)).Viable)
  strictControls : ∀ depth : Nat,
    IsEmpty (SourceGeneratedPortfolioCaptureDeathAt depth
        (fullPortfolioSourceAt depth) noCapture) ∧
      (¬ noCapture.Captures ExitFutureCode.leave) ∧
      failureCapacityReadoutAt depth (tenureCaptureOriginAt depth) =
        failureCapacityReadoutAt depth (routeBottleneckOriginAt depth) ∧
      failureCapacityReadoutAt depth (routeBottleneckOriginAt depth) = 0 ∧
      (∀ domain : EssentialAccessRelationAuthority,
        IsEmpty ((routeIncidenceMissingGeometryAt depth).RoutesAt
          ExitFutureCode.leave (domainCrossingAt depth domain))) ∧
      (stableGeometryCompilerAt depth).actionableExitCapacity = 1 ∧
      IsEmpty (SourceGeneratedStableDomainServiceIncidenceAt depth
        (exactEssentialAccessSeed .health)) ∧
      (∀ _fully : FullyFulfilledExchangeAt settlementCompiler openOccurrence,
        IsEmpty (RootInstalledTenurePurposeCaptureAt depth)) ∧
      IsEmpty (repairedConfigurationAt depth ⟶
        captureConfigurationAt (depth + 1))

theorem proofCarryingCaptureChokepointBasinRecoveryDirectConsumer :
    ProofCarryingCaptureChokepointBasinRecoveryCertificate where
  everyDepth := captureChokepointBasinRecoveryAt
  strictControls := captureChokepointStrictControls

end
end M14ProofCarryingCaptureChokepointBasinRecoveryRegression
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingCaptureChokepointBasinRecoveryRegression.captureChokepointBasinRecoveryAt
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingCaptureChokepointBasinRecoveryRegression.captureChokepointStrictControls
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingCaptureChokepointBasinRecoveryRegression.proofCarryingCaptureChokepointBasinRecoveryDirectConsumer
