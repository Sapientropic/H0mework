import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Root.Economy.Attractor.EconomicViability

/-!
# M14 adjacent economic-viability boundary

The two source death faces and the repaired target now share one
`EconomicViabilityAt` predicate.  This sealed boundary records that both
offset-zero source configurations are nonviable while the actual offset-one
target is viable, with exact root, next, and occurrence provenance.

It is deliberately not called a hitting time or rank: no path-candidate fibre
or minimization authority exists yet.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14AdjacentEconomicViabilityBoundary

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Renewal UBI Capacity Space CrossingCost
open M9ProofCarryingRenewalInquiryRoot
open M14UBIExitCapacityFixture
open M14UBIPeriodicRootHistory
open M14UBIPeriodicActualServiceCapacity
open M14ActionableFuturePortfolio
open M14EconomicSingleFold
open M14GeneratedEconomicDisposition
open M14PortfolioCaptureDeath
open M14PeriodicDeathRepairNormalization
open M14PeriodicNormalizedViableDisposition
open M14EconomicViability

/-- Receipt-indexed adjacent boundary.  Neither an entry nor a target can be
supplied to the public producer. -/
structure SourceGeneratedAdjacentEconomicViabilityBoundaryAt
    (depth : Nat)
    (entry : SourceGeneratedPeriodicNormalizedViableDispositionAt depth
      (sourceGeneratedPeriodicDeathRepairNormalizationAt depth)
      (portfolioViableEconomicDispositionAt depth))
    (target : EconomicViabilityAt (depth + 1)
      (fullPortfolioSourceAt (depth + 1)) noCapture) : Type 18 where
  private mk ::
  entryExact : entry =
    sourceGeneratedPeriodicNormalizedViableDispositionAt depth
  targetExact : target = sourceGeneratedPeriodicEconomicViabilityAt depth
  maintenanceOffsetZeroEmpty : IsEmpty (EconomicViabilityAt depth
    (stablePortfolioSourceAt depth) noCapture)
  captureOffsetZeroEmpty : IsEmpty (EconomicViabilityAt depth
    (fullPortfolioSourceAt depth) fullCapture)
  targetOffsetOneLive : Nonempty (EconomicViabilityAt (depth + 1)
    (fullPortfolioSourceAt (depth + 1)) noCapture)
  maintenanceRootExact :
    entry.normalization.service.sourceDeath.stable.paymentOccurrence.rootOccurrence =
      jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
        (temporalVisitAt depth)
  captureRootExact :
    entry.normalization.captureDeath.fullServices.paymentOccurrence.rootOccurrence =
      jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
        (temporalVisitAt depth)
  targetRootExact : target.portfolio.paymentOccurrence.rootOccurrence =
    jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
      (temporalVisitAt (depth + 1))
  targetOccurrenceExact : target.occurrence.root.erasedRootEvent =
    ⟨temporalVisitAt (depth + 1),
      target.portfolio.paymentOccurrence.rootOccurrence⟩
  targetImageExact : target.image = economicImage target.occurrence
  targetDispositionExact : HEq target.toDisposition entry.viableDisposition
  targetNextExact : entry.normalization.normalForm.generatedNext =
    jointRoot.generatedNextCurrentAt (temporalVisitAt depth)
  targetVisitExact : HEq entry.normalization.normalForm.generatedNext.visit
    (temporalVisitAt (depth + 1))
  adjacentOccurrencesDistinct : periodicPaymentOccurrenceAt depth ≠
    periodicPaymentOccurrenceAt (depth + 1)
  sourceCapacityOne :
    (stableGeometryCompilerAt depth).actionableExitCapacity = 1
  targetCapacityOne :
    (geometryCompilerAt (depth + 1)).actionableExitCapacity = 1
  lawSurfacePreserved :
    entry.normalization.normalForm.generatedNext.root.source.lawSurface =
      jointRoot.source.base.lawSurface

namespace SourceGeneratedAdjacentEconomicViabilityBoundaryAt

def entry
    {depth : Nat}
    {entry : SourceGeneratedPeriodicNormalizedViableDispositionAt depth
      (sourceGeneratedPeriodicDeathRepairNormalizationAt depth)
      (portfolioViableEconomicDispositionAt depth)}
    {target : EconomicViabilityAt (depth + 1)
      (fullPortfolioSourceAt (depth + 1)) noCapture}
    (_boundary : SourceGeneratedAdjacentEconomicViabilityBoundaryAt
      depth entry target) := entry

def target
    {depth : Nat}
    {entry : SourceGeneratedPeriodicNormalizedViableDispositionAt depth
      (sourceGeneratedPeriodicDeathRepairNormalizationAt depth)
      (portfolioViableEconomicDispositionAt depth)}
    {target : EconomicViabilityAt (depth + 1)
      (fullPortfolioSourceAt (depth + 1)) noCapture}
    (_boundary : SourceGeneratedAdjacentEconomicViabilityBoundaryAt
      depth entry target) := target

end SourceGeneratedAdjacentEconomicViabilityBoundaryAt

/-- Sole boundary producer. -/
def sourceGeneratedAdjacentEconomicViabilityBoundaryAt (depth : Nat) :
    SourceGeneratedAdjacentEconomicViabilityBoundaryAt depth
      (sourceGeneratedPeriodicNormalizedViableDispositionAt depth)
      (sourceGeneratedPeriodicEconomicViabilityAt depth) := by
  let entry := sourceGeneratedPeriodicNormalizedViableDispositionAt depth
  let target := sourceGeneratedPeriodicEconomicViabilityAt depth
  exact
    { entryExact := rfl
      targetExact := rfl
      maintenanceOffsetZeroEmpty :=
        maintenanceEconomicViability_isEmpty depth
      captureOffsetZeroEmpty := captureEconomicViability_isEmpty depth
      targetOffsetOneLive := ⟨target⟩
      maintenanceRootExact :=
        entry.normalization.service.sourceDeath.paymentRootExact
      captureRootExact := entry.normalization.captureDeath.paymentRootExact
      targetRootExact :=
        entry.normalization.normalForm.targetPortfolioRootExact
      targetOccurrenceExact := by
        change (postRepairViableExposureAt depth).root.erasedRootEvent =
          ⟨temporalVisitAt (depth + 1),
            (sourceGeneratedActionableFuturePortfolioAt
              (depth + 1)).paymentOccurrence.rootOccurrence⟩
        rw [postRepairViableExposureAt_rootEvent,
          (sourceGeneratedActionableFuturePortfolioAt
            (depth + 1)).paymentOccurrence_eq]
      targetImageExact := rfl
      targetDispositionExact := HEq.rfl
      targetNextExact := entry.targetNextIsRoot
      targetVisitExact := entry.targetVisitExact
      adjacentOccurrencesDistinct := entry.adjacentOccurrencesDistinct
      sourceCapacityOne :=
        entry.normalization.service.sourceDeathCapacityExact
      targetCapacityOne := entry.targetCapacityExact
      lawSurfacePreserved := entry.lawSurfacePreserved }

theorem every_generated_period_crosses_the_same_viability_predicate
    (depth : Nat) :
    IsEmpty (EconomicViabilityAt depth
      (stablePortfolioSourceAt depth) noCapture) ∧
      IsEmpty (EconomicViabilityAt depth
        (fullPortfolioSourceAt depth) fullCapture) ∧
      Nonempty (EconomicViabilityAt (depth + 1)
        (fullPortfolioSourceAt (depth + 1)) noCapture) ∧
      Nonempty (SourceGeneratedAdjacentEconomicViabilityBoundaryAt depth
        (sourceGeneratedPeriodicNormalizedViableDispositionAt depth)
        (sourceGeneratedPeriodicEconomicViabilityAt depth)) :=
  ⟨maintenanceEconomicViability_isEmpty depth,
    captureEconomicViability_isEmpty depth,
    ⟨sourceGeneratedPeriodicEconomicViabilityAt depth⟩,
    ⟨sourceGeneratedAdjacentEconomicViabilityBoundaryAt depth⟩⟩

theorem adjacent_boundary_mouth_has_no_hitting_time_or_rank
    (depth : Nat) : True := by
  let boundary := sourceGeneratedAdjacentEconomicViabilityBoundaryAt depth
  fail_if_success exact boundary.steps
  fail_if_success exact boundary.rank
  fail_if_success exact boundary.minimum
  fail_if_success exact boundary.decreases
  fail_if_success exact boundary.coverage
  fail_if_success exact boundary.completedHistory
  fail_if_success exact boundary.u8Gate
  trivial

end
end M14AdjacentEconomicViabilityBoundary
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14AdjacentEconomicViabilityBoundary.sourceGeneratedAdjacentEconomicViabilityBoundaryAt
#print axioms SaturationMonoid.ProcessGame.Society.M14AdjacentEconomicViabilityBoundary.every_generated_period_crosses_the_same_viability_predicate
