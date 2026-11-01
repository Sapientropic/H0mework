import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Root.Economy.Attractor.AdjacentEconomicViabilityBoundary

/-!
# M14 periodic viability-renewal receipt

The viable target generated at depth `d` and the next adjacent boundary at
depth `d + 1` meet at one literal temporal root occurrence.  This module
seals that meeting into an action-bearing whole-root renewal receipt whose
target is the viable face at depth `d + 2`.

The public producer accepts only `depth`.  Source and target viability,
service and capture actions, selected rows, whole-ledger write-back, root
next, and both endpoint occurrences are read from the existing adjacent
boundaries.  No path, rank, coverage table, optimizer, new root, ledger, or
completed future is introduced.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14PeriodicViabilityRenewalReceipt

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Renewal UBI Capacity Space CrossingCost
open M9ProofCarryingRenewalInquiryRoot
open M14UBIExitCapacityFixture
open M14UBIProofCarryingRootRestriction
open M14UBIPeriodicRootHistory
open M14UBIPeriodicActualServiceCapacity
open M14ActionableFuturePortfolio
open M14EconomicSingleFold
open M14GeneratedEconomicDisposition
open M14PortfolioCaptureDeath
open M14SourceEssentialServiceRestoration
open M14PeriodicEssentialServiceRestoration
open M14PeriodicDeathRepairNormalization
open M14PeriodicNormalizedViableDisposition
open M14EconomicViability
open M14AdjacentEconomicViabilityBoundary

/-- The already generated adjacent boundary at one exact depth.  This alias
is local to the receipt layer so the later path module may import this file
without an import cycle. -/
abbrev PeriodicViabilityBoundaryAt (depth : Nat) :=
  SourceGeneratedAdjacentEconomicViabilityBoundaryAt depth
    (sourceGeneratedPeriodicNormalizedViableDispositionAt depth)
    (sourceGeneratedPeriodicEconomicViabilityAt depth)

/-- One actual whole-root renewal from an already viable visit to the next
viable visit.  The three arguments are dependent indices; the sole public
producer below computes all of them from `depth`. -/
structure SourceGeneratedPeriodicViabilityRenewalAt
    (depth : Nat)
    (source : EconomicViabilityAt (depth + 1)
      (fullPortfolioSourceAt (depth + 1)) noCapture)
    (transition : PeriodicViabilityBoundaryAt (depth + 1))
    (target : EconomicViabilityAt (depth + 2)
      (fullPortfolioSourceAt (depth + 2)) noCapture) : Type 18 where
  private mk ::
  sourceExact : source = sourceGeneratedPeriodicEconomicViabilityAt depth
  transitionExact : transition =
    sourceGeneratedAdjacentEconomicViabilityBoundaryAt (depth + 1)
  targetExact : target =
    sourceGeneratedPeriodicEconomicViabilityAt (depth + 1)
  sourceRootExact : source.portfolio.paymentOccurrence.rootOccurrence =
    jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
      (temporalVisitAt (depth + 1))
  serviceRootExact : transition.entry.normalization.service.rootOccurrence =
    jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
      (temporalVisitAt (depth + 1))
  captureRootExact : HEq
    transition.entry.normalization.captureDeath.ordinaryRepair.renewal.rootOccurrence
    (jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
      (temporalVisitAt (depth + 1)))
  sourceRootSharedWithService :
    source.portfolio.paymentOccurrence.rootOccurrence =
      transition.entry.normalization.service.rootOccurrence
  sourceRootSharedWithCapturePortfolio :
    source.portfolio.paymentOccurrence.rootOccurrence =
      (transition.entry.normalization.captureDeath.fullServices.paymentOccurrence).rootOccurrence
  serviceActionExact :
    transition.entry.normalization.service.installed.payload.disposition =
      sourceGeneratedHealthServiceRestoration
  captureActionExact :
    ((transition.entry.normalization.captureDeath.ordinaryRepair.renewal.source).installed.payload).disposition =
      sourceGeneratedUBIDisposition
  serviceRowSharedWithUBI : HEq
    transition.entry.normalization.service.installed.payload.selectedRow
      (installedUBIAt (depth + 1)).payload.selectedRow
  captureRowSharedWithUBI : HEq
    ((transition.entry.normalization.captureDeath.ordinaryRepair.renewal.source).installed.payload).selectedRow
      (installedUBIAt (depth + 1)).payload.selectedRow
  serviceSelectedWriteCommutes :
    (transition.entry.normalization.service.applied.selectedWrite.sourceRow).CommutesWithWorld
  captureSelectedWriteCommutes :
    (transition.entry.normalization.captureDeath.ordinaryRepair.renewal.ordinarySelectedWrite.sourceRow).CommutesWithWorld
  wholeLedgerShared :
    transition.entry.normalization.service.applied.wholeLedgerWriteBack =
      transition.entry.normalization.captureDeath.ordinaryRepair.renewal.wholeLedgerWriteBack
  serviceWholeLedgerExact :
    transition.entry.normalization.service.applied.wholeLedgerWriteBack =
      (jointRoot.toAuthoritativeRoot.toLedgerRoot
        |>.generatedAtTemporalVisit
          (temporalVisitAt (depth + 1))).wholeLedgerWriteBack
  generatedNextExact :
    transition.entry.normalization.normalForm.generatedNext =
      jointRoot.generatedNextCurrentAt (temporalVisitAt (depth + 1))
  generatedNextIsService :
    transition.entry.normalization.normalForm.generatedNext =
      transition.entry.normalization.service.applied.generatedNext
  generatedNextIsCapture :
    transition.entry.normalization.normalForm.generatedNext =
      transition.entry.normalization.captureDeath.ordinaryRepair.renewal.generatedNext
  targetVisitExact : HEq
    transition.entry.normalization.normalForm.generatedNext.visit
      (temporalVisitAt (depth + 2))
  targetRootExact : target.portfolio.paymentOccurrence.rootOccurrence =
    jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
      (temporalVisitAt (depth + 2))
  targetOccurrenceExact : target.occurrence.root.erasedRootEvent =
    ⟨temporalVisitAt (depth + 2),
      target.portfolio.paymentOccurrence.rootOccurrence⟩
  sourceDispositionExact : HEq source.toDisposition
    (sourceGeneratedPeriodicNormalizedViableDispositionAt depth
      |>.viableDisposition)
  targetDispositionExact : HEq target.toDisposition
    transition.entry.viableDisposition
  adjacentOccurrencesDistinct :
    periodicPaymentOccurrenceAt (depth + 1) ≠
      periodicPaymentOccurrenceAt (depth + 2)
  lawSurfacePreserved :
    transition.entry.normalization.normalForm.generatedNext.root.source.lawSurface =
      jointRoot.source.base.lawSurface

namespace SourceGeneratedPeriodicViabilityRenewalAt

/-- Exact source viability readout from the dependent index. -/
def source
    {depth : Nat}
    {source : EconomicViabilityAt (depth + 1)
      (fullPortfolioSourceAt (depth + 1)) noCapture}
    {transition : PeriodicViabilityBoundaryAt (depth + 1)}
    {target : EconomicViabilityAt (depth + 2)
      (fullPortfolioSourceAt (depth + 2)) noCapture}
    (_renewal : SourceGeneratedPeriodicViabilityRenewalAt
      depth source transition target) := source

/-- Exact boundary readout from the dependent index. -/
def transition
    {depth : Nat}
    {source : EconomicViabilityAt (depth + 1)
      (fullPortfolioSourceAt (depth + 1)) noCapture}
    {transition : PeriodicViabilityBoundaryAt (depth + 1)}
    {target : EconomicViabilityAt (depth + 2)
      (fullPortfolioSourceAt (depth + 2)) noCapture}
    (_renewal : SourceGeneratedPeriodicViabilityRenewalAt
      depth source transition target) := transition

/-- Exact target viability readout from the dependent index. -/
def target
    {depth : Nat}
    {source : EconomicViabilityAt (depth + 1)
      (fullPortfolioSourceAt (depth + 1)) noCapture}
    {transition : PeriodicViabilityBoundaryAt (depth + 1)}
    {target : EconomicViabilityAt (depth + 2)
      (fullPortfolioSourceAt (depth + 2)) noCapture}
    (_renewal : SourceGeneratedPeriodicViabilityRenewalAt
      depth source transition target) := target

end SourceGeneratedPeriodicViabilityRenewalAt

/-- Sole depth-only producer. -/
def sourceGeneratedPeriodicViabilityRenewalAt (depth : Nat) :
    SourceGeneratedPeriodicViabilityRenewalAt depth
      (sourceGeneratedPeriodicEconomicViabilityAt depth)
      (sourceGeneratedAdjacentEconomicViabilityBoundaryAt (depth + 1))
      (sourceGeneratedPeriodicEconomicViabilityAt (depth + 1)) := by
  let source := sourceGeneratedPeriodicEconomicViabilityAt depth
  let transition :=
    sourceGeneratedAdjacentEconomicViabilityBoundaryAt (depth + 1)
  let target := sourceGeneratedPeriodicEconomicViabilityAt (depth + 1)
  exact
    { sourceExact := rfl
      transitionExact := rfl
      targetExact := rfl
      sourceRootExact := source.portfolio.rootOccurrenceExact
      serviceRootExact := transition.entry.normalization.normalForm
        |>.serviceRootOccurrenceExact
      captureRootExact := transition.entry.normalization.normalForm
        |>.captureRootOccurrenceExact
      sourceRootSharedWithService :=
        source.portfolio.rootOccurrenceExact.trans
          (transition.entry.normalization.normalForm
            |>.serviceRootOccurrenceExact).symm
      sourceRootSharedWithCapturePortfolio :=
        source.portfolio.rootOccurrenceExact.trans
          transition.entry.normalization.captureRootExact.symm
      serviceActionExact := transition.entry.normalization.normalForm
        |>.serviceActionExact
      captureActionExact := transition.entry.normalization.normalForm
        |>.captureActionExact
      serviceRowSharedWithUBI := transition.entry.normalization.normalForm
        |>.serviceRowSharedWithUBI
      captureRowSharedWithUBI := transition.entry.normalization.normalForm
        |>.captureRowSharedWithUBI
      serviceSelectedWriteCommutes := transition.entry.normalization.normalForm
        |>.serviceSelectedWriteCommutes
      captureSelectedWriteCommutes := transition.entry.normalization.normalForm
        |>.captureSelectedWriteCommutes
      wholeLedgerShared := transition.entry.normalization.normalForm
        |>.wholeLedgerShared
      serviceWholeLedgerExact :=
        transition.entry.normalization.service.wholeLedgerExact
      generatedNextExact := transition.entry.targetNextIsRoot
      generatedNextIsService := transition.entry.normalization.normalForm
        |>.nextIsService
      generatedNextIsCapture := transition.entry.normalization.normalForm
        |>.nextIsCapture
      targetVisitExact := transition.entry.targetVisitExact
      targetRootExact := target.portfolio.rootOccurrenceExact
      targetOccurrenceExact := by
        change (postRepairViableExposureAt (depth + 1)).root.erasedRootEvent =
          ⟨temporalVisitAt (depth + 2),
            (sourceGeneratedActionableFuturePortfolioAt (depth + 2))
              |>.paymentOccurrence |>.rootOccurrence⟩
        rw [postRepairViableExposureAt_rootEvent,
          (sourceGeneratedActionableFuturePortfolioAt (depth + 2))
            |>.paymentOccurrence_eq]
      sourceDispositionExact := HEq.rfl
      targetDispositionExact := HEq.rfl
      adjacentOccurrencesDistinct := transition.adjacentOccurrencesDistinct
      lawSurfacePreserved := transition.lawSurfacePreserved }

theorem every_generated_viable_visit_has_actual_renewal
    (depth : Nat) :
    Nonempty (SourceGeneratedPeriodicViabilityRenewalAt depth
      (sourceGeneratedPeriodicEconomicViabilityAt depth)
      (sourceGeneratedAdjacentEconomicViabilityBoundaryAt (depth + 1))
      (sourceGeneratedPeriodicEconomicViabilityAt (depth + 1))) :=
  ⟨sourceGeneratedPeriodicViabilityRenewalAt depth⟩

/-! ## Wrong-index and bare-mouth controls -/

theorem stable_source_cannot_index_viability_renewal (depth : Nat) :
    IsEmpty (EconomicViabilityAt (depth + 1)
      (stablePortfolioSourceAt (depth + 1)) noCapture) :=
  targetStableEconomicViability_isEmpty depth

theorem captured_target_cannot_index_viability_renewal (depth : Nat) :
    IsEmpty (EconomicViabilityAt (depth + 2)
      (fullPortfolioSourceAt (depth + 2)) fullCapture) :=
  targetCapturedEconomicViability_isEmpty (depth + 1)

theorem renewal_source_and_target_occurrences_are_distinct (depth : Nat) :
    periodicPaymentOccurrenceAt (depth + 1) ≠
      periodicPaymentOccurrenceAt (depth + 2) :=
  (sourceGeneratedPeriodicViabilityRenewalAt depth)
    |>.adjacentOccurrencesDistinct

theorem periodic_viability_renewal_mouth_has_no_path_or_future_fields
    (depth : Nat) : True := by
  let renewal := sourceGeneratedPeriodicViabilityRenewalAt depth
  fail_if_success exact renewal.path
  fail_if_success exact renewal.rank
  fail_if_success exact renewal.decreases
  fail_if_success exact renewal.coverage
  fail_if_success exact renewal.optimizer
  fail_if_success exact renewal.completedHistory
  fail_if_success exact renewal.u8Gate
  trivial

end
end M14PeriodicViabilityRenewalReceipt
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14PeriodicViabilityRenewalReceipt.sourceGeneratedPeriodicViabilityRenewalAt
#print axioms SaturationMonoid.ProcessGame.Society.M14PeriodicViabilityRenewalReceipt.every_generated_viable_visit_has_actual_renewal
#print axioms SaturationMonoid.ProcessGame.Society.M14PeriodicViabilityRenewalReceipt.renewal_source_and_target_occurrences_are_distinct
