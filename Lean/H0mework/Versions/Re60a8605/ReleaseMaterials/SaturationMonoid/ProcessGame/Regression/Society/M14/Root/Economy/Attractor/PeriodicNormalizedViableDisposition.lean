import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Root.Economy.Attractor.FixedOneStepViabilityAttractor

/-!
# M14 periodic normalized viable disposition

Every source-generated normalization at depth `d` is installed into the
existing viable summand at visit `d + 1`.  This is a pointwise periodic
producer, not a stored `Nat →` future.  It reuses the generalized existing
post-repair viable carrier and the unchanged four-way `EconomicDispositionAt`.

The public mouth accepts only `depth`; target portfolio, capacity, image,
landing, rank, coverage, branch, and U8 authority are all absent.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14PeriodicNormalizedViableDisposition

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Renewal UBI Capacity Space CrossingCost
open ConstructiveRoot.RootInquiryCompletion
open M9ProofCarryingRenewalInquiryRoot
open M14UBIExitCapacityFixture
open M14UBIPeriodicRootHistory
open M14UBIPeriodicActualServiceCapacity
open M14EssentialAccessRelationFixture
open M14EssentialAccessSectorRegression
open M14ActionableFuturePortfolio
open M14EconomicSingleFold
open M14GeneratedEconomicDisposition
open M14PortfolioCaptureDeath
open M14PeriodicDeathRepairNormalization
open M14FixedOneStepViabilityAttractor

/-- A periodic normalization and its next-visit portfolio-viable carrier are
dependent indices of one existing viable economic disposition. -/
structure SourceGeneratedPeriodicNormalizedViableDispositionAt
    (depth : Nat)
    (normalization : SourceGeneratedPeriodicDeathRepairNormalizationAt depth)
    (viable : SourceGeneratedPortfolioViableEconomicDispositionAt
      (postRepairViableExposureAt depth) (postRepairViableImageAt depth)
        (ordinaryEconomicLandingAt depth)) : Type 18 where
  private mk ::
  normalizationExact : normalization =
    sourceGeneratedPeriodicDeathRepairNormalizationAt depth
  viableExact : viable = portfolioViableEconomicDispositionAt depth
  viableDepthExact : viable.depth = depth
  targetPortfolioExact : HEq normalization.normalForm.targetPortfolio
    viable.portfolio
  targetPaymentIsViableExit : HEq
    normalization.normalForm.targetPortfolio.paymentOccurrence
      viable.viable.actualExit.paymentOccurrence
  targetNextExact : normalization.normalForm.generatedNext =
    viable.viable.ordinary.renewal.generatedNext
  targetNextIsRoot : normalization.normalForm.generatedNext =
    jointRoot.generatedNextCurrentAt (temporalVisitAt depth)
  targetVisitExact : HEq normalization.normalForm.generatedNext.visit
    (temporalVisitAt (depth + 1))
  targetLandingExact : ordinaryEconomicLandingAt depth = some
    (⟨M9ProofCarryingRenewalInquiryRoot.N,
      normalization.normalForm.generatedNext⟩ : AnyAuthoritativeRootCurrent)
  targetOccurrenceExact :
    (postRepairViableExposureAt depth).root.erasedRootEvent =
      ⟨temporalVisitAt (depth + 1),
        normalization.normalForm.targetPortfolio.paymentOccurrence.rootOccurrence⟩
  targetImageExact : postRepairViableImageAt depth =
    economicImage (postRepairViableExposureAt depth)
  targetCapacityExact :
    (geometryCompilerAt (depth + 1)).actionableExitCapacity = 1
  targetUncaptured : ¬ noCapture.Captures ExitFutureCode.leave
  viableDisposition : EconomicDispositionAt
    (postRepairViableExposureAt depth) (postRepairViableImageAt depth)
      (ordinaryEconomicLandingAt depth)
  viableDispositionExact : viableDisposition = .inl viable.viable
  sourceMaintenanceStillEmpty : IsEmpty
    (CompletePortfolioAt depth (stablePortfolioSourceAt depth))
  sourceCaptureStillEmpty : IsEmpty
    (CapturedActionableFuturePortfolioAt depth)
  groundedTerminalEmpty : IsEmpty
    (SourceGeneratedGroundedEconomicTerminalAt
      (tenureRepairExposureAt depth) (tenureEconomicImageAt depth) none)
  adjacentOccurrencesDistinct : periodicPaymentOccurrenceAt depth ≠
    periodicPaymentOccurrenceAt (depth + 1)
  lawSurfacePreserved :
    normalization.normalForm.generatedNext.root.source.lawSurface =
      jointRoot.source.base.lawSurface

namespace SourceGeneratedPeriodicNormalizedViableDispositionAt

def normalization
    {depth : Nat}
    {normalization : SourceGeneratedPeriodicDeathRepairNormalizationAt depth}
    {viable : SourceGeneratedPortfolioViableEconomicDispositionAt
      (postRepairViableExposureAt depth) (postRepairViableImageAt depth)
        (ordinaryEconomicLandingAt depth)}
    (_entry : SourceGeneratedPeriodicNormalizedViableDispositionAt
      depth normalization viable) := normalization

def viable
    {depth : Nat}
    {normalization : SourceGeneratedPeriodicDeathRepairNormalizationAt depth}
    {viable : SourceGeneratedPortfolioViableEconomicDispositionAt
      (postRepairViableExposureAt depth) (postRepairViableImageAt depth)
        (ordinaryEconomicLandingAt depth)}
    (_entry : SourceGeneratedPeriodicNormalizedViableDispositionAt
      depth normalization viable) := viable

end SourceGeneratedPeriodicNormalizedViableDispositionAt

/-- Sole pointwise producer. -/
def sourceGeneratedPeriodicNormalizedViableDispositionAt (depth : Nat) :
    SourceGeneratedPeriodicNormalizedViableDispositionAt depth
      (sourceGeneratedPeriodicDeathRepairNormalizationAt depth)
      (portfolioViableEconomicDispositionAt depth) := by
  let normalization := sourceGeneratedPeriodicDeathRepairNormalizationAt depth
  let viable := portfolioViableEconomicDispositionAt depth
  exact
    { normalizationExact := rfl
      viableExact := rfl
      viableDepthExact := rfl
      targetPortfolioExact := HEq.rfl
      targetPaymentIsViableExit := HEq.rfl
      targetNextExact := normalization.normalForm.nextIsRoot.trans
        viable.viable.ordinary.generatedNextExact.symm
      targetNextIsRoot := normalization.normalForm.nextIsRoot
      targetVisitExact := normalization.normalForm.nextVisitExact
      targetLandingExact := normalization.normalForm.ordinaryLandingExact
      targetOccurrenceExact := by
        rw [postRepairViableExposureAt_rootEvent,
          normalization.normalForm.targetPortfolio.paymentOccurrence_eq]
      targetImageExact := viable.sameImage
      targetCapacityExact := normalization.normalForm.targetCapacity
      targetUncaptured := normalization.normalForm.targetUncaptured
      viableDisposition := .inl viable.viable
      viableDispositionExact := rfl
      sourceMaintenanceStillEmpty :=
        normalization.serviceCannotBeReplacedByCaptureRepair
      sourceCaptureStillEmpty :=
        normalization.captureCannotBeReplacedByServiceRepair
      groundedTerminalEmpty := normalization.groundedTerminalEmpty
      adjacentOccurrencesDistinct := normalization.adjacentOccurrencesDistinct
      lawSurfacePreserved := normalization.normalForm.lawSurfacePreserved }

theorem every_generated_normalization_enters_viable_disposition
    (depth : Nat) :
    Nonempty (SourceGeneratedPeriodicNormalizedViableDispositionAt depth
      (sourceGeneratedPeriodicDeathRepairNormalizationAt depth)
      (portfolioViableEconomicDispositionAt depth)) ∧
      Nonempty (EconomicDispositionAt (postRepairViableExposureAt depth)
        (postRepairViableImageAt depth)
          (ordinaryEconomicLandingAt depth)) :=
  ⟨⟨sourceGeneratedPeriodicNormalizedViableDispositionAt depth⟩,
    ⟨(sourceGeneratedPeriodicNormalizedViableDispositionAt depth)
      |>.viableDisposition⟩⟩

/-- The periodic depth-zero restriction is definitionally the already signed
fixed attractor data; it does not create a second viability authority. -/
theorem depthZero_periodic_restricts_to_fixed :
    let periodic := sourceGeneratedPeriodicNormalizedViableDispositionAt 0
    let fixed := sourceGeneratedFixedOneStepViabilityAttractor
    periodic.normalization = fixed.normalization ∧
      periodic.viable = fixed.viable ∧
      periodic.viableDisposition = fixed.viableDisposition := by
  exact ⟨rfl, rfl, rfl⟩

theorem periodic_viable_mouth_has_no_rank_coverage_or_completed_history
    (depth : Nat) : True := by
  let entry := sourceGeneratedPeriodicNormalizedViableDispositionAt depth
  fail_if_success exact entry.rank
  fail_if_success exact entry.decreases
  fail_if_success exact entry.coverage
  fail_if_success exact entry.completedHistory
  fail_if_success exact entry.u8Gate
  fail_if_success exact entry.firstWrite
  trivial

end
end M14PeriodicNormalizedViableDisposition
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14PeriodicNormalizedViableDisposition.sourceGeneratedPeriodicNormalizedViableDispositionAt
#print axioms SaturationMonoid.ProcessGame.Society.M14PeriodicNormalizedViableDisposition.every_generated_normalization_enters_viable_disposition
#print axioms SaturationMonoid.ProcessGame.Society.M14PeriodicNormalizedViableDisposition.depthZero_periodic_restricts_to_fixed
