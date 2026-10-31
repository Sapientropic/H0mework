import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Root.Economy.Attractor.AdjacentEconomicViabilityBoundary

/-!
# M14 direct consumer for the adjacent economic-viability boundary

The same dependent predicate is empty on maintenance and capture sources and
inhabited on the actual next-visit target.  This consumer checks root/next/
occurrence provenance, exact viable-summand landing, wrong-target controls,
and the capacity-one counterexample.  It does not manufacture a rank.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingAdjacentEconomicViabilityBoundaryRegression

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
open M14AdjacentEconomicViabilityBoundary

theorem same_predicate_separates_both_sources_from_target (depth : Nat) :
    IsEmpty (EconomicViabilityAt depth
      (stablePortfolioSourceAt depth) noCapture) ∧
      IsEmpty (EconomicViabilityAt depth
        (fullPortfolioSourceAt depth) fullCapture) ∧
      Nonempty (EconomicViabilityAt (depth + 1)
        (fullPortfolioSourceAt (depth + 1)) noCapture) ∧
      (stableGeometryCompilerAt depth).actionableExitCapacity = 1 ∧
      (geometryCompilerAt (depth + 1)).actionableExitCapacity = 1 := by
  let boundary := sourceGeneratedAdjacentEconomicViabilityBoundaryAt depth
  exact ⟨boundary.maintenanceOffsetZeroEmpty,
    boundary.captureOffsetZeroEmpty,
    boundary.targetOffsetOneLive,
    boundary.sourceCapacityOne,
    boundary.targetCapacityOne⟩

theorem boundary_root_next_and_disposition_commute (depth : Nat) :
    let boundary := sourceGeneratedAdjacentEconomicViabilityBoundaryAt depth
    boundary.entry.normalization.service.sourceDeath.stable.paymentOccurrence.rootOccurrence =
        jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
          (temporalVisitAt depth) ∧
      boundary.entry.normalization.captureDeath.fullServices.paymentOccurrence.rootOccurrence =
        jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
          (temporalVisitAt depth) ∧
      boundary.target.portfolio.paymentOccurrence.rootOccurrence =
        jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
          (temporalVisitAt (depth + 1)) ∧
      boundary.target.occurrence.root.erasedRootEvent =
        ⟨temporalVisitAt (depth + 1),
          boundary.target.portfolio.paymentOccurrence.rootOccurrence⟩ ∧
      boundary.target.image = economicImage boundary.target.occurrence ∧
      HEq boundary.target.toDisposition boundary.entry.viableDisposition ∧
      boundary.entry.normalization.normalForm.generatedNext =
        jointRoot.generatedNextCurrentAt (temporalVisitAt depth) ∧
      HEq boundary.entry.normalization.normalForm.generatedNext.visit
        (temporalVisitAt (depth + 1)) ∧
      periodicPaymentOccurrenceAt depth ≠
        periodicPaymentOccurrenceAt (depth + 1) ∧
      boundary.entry.normalization.normalForm.generatedNext.root.source.lawSurface =
        jointRoot.source.base.lawSurface := by
  let boundary := sourceGeneratedAdjacentEconomicViabilityBoundaryAt depth
  exact ⟨boundary.maintenanceRootExact,
    boundary.captureRootExact,
    boundary.targetRootExact,
    boundary.targetOccurrenceExact,
    boundary.targetImageExact,
    boundary.targetDispositionExact,
    boundary.targetNextExact,
    boundary.targetVisitExact,
    boundary.adjacentOccurrencesDistinct,
    boundary.lawSurfacePreserved⟩

theorem wrong_target_axes_remain_nonviable (depth : Nat) :
    IsEmpty (EconomicViabilityAt (depth + 1)
      (stablePortfolioSourceAt (depth + 1)) noCapture) ∧
      IsEmpty (EconomicViabilityAt (depth + 1)
        (fullPortfolioSourceAt (depth + 1)) fullCapture) :=
  ⟨targetStableEconomicViability_isEmpty depth,
    targetCapturedEconomicViability_isEmpty depth⟩

structure ProofCarryingAdjacentEconomicViabilityBoundaryCertificate : Prop where
  everyDepthBoundary : ∀ depth : Nat,
    Nonempty (SourceGeneratedAdjacentEconomicViabilityBoundaryAt depth
      (sourceGeneratedPeriodicNormalizedViableDispositionAt depth)
      (sourceGeneratedPeriodicEconomicViabilityAt depth))
  everyDepthSamePredicate : ∀ depth : Nat,
    IsEmpty (EconomicViabilityAt depth
      (stablePortfolioSourceAt depth) noCapture) ∧
      IsEmpty (EconomicViabilityAt depth
        (fullPortfolioSourceAt depth) fullCapture) ∧
      Nonempty (EconomicViabilityAt (depth + 1)
        (fullPortfolioSourceAt (depth + 1)) noCapture) ∧
      (stableGeometryCompilerAt depth).actionableExitCapacity = 1 ∧
      (geometryCompilerAt (depth + 1)).actionableExitCapacity = 1
  everyDepthCommuting : ∀ depth : Nat,
    let boundary := sourceGeneratedAdjacentEconomicViabilityBoundaryAt depth
    boundary.entry.normalization.service.sourceDeath.stable.paymentOccurrence.rootOccurrence =
        jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
          (temporalVisitAt depth) ∧
      boundary.entry.normalization.captureDeath.fullServices.paymentOccurrence.rootOccurrence =
        jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
          (temporalVisitAt depth) ∧
      boundary.target.portfolio.paymentOccurrence.rootOccurrence =
        jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
          (temporalVisitAt (depth + 1)) ∧
      boundary.target.occurrence.root.erasedRootEvent =
        ⟨temporalVisitAt (depth + 1),
          boundary.target.portfolio.paymentOccurrence.rootOccurrence⟩ ∧
      boundary.target.image = economicImage boundary.target.occurrence ∧
      HEq boundary.target.toDisposition boundary.entry.viableDisposition ∧
      boundary.entry.normalization.normalForm.generatedNext =
        jointRoot.generatedNextCurrentAt (temporalVisitAt depth) ∧
      HEq boundary.entry.normalization.normalForm.generatedNext.visit
        (temporalVisitAt (depth + 1)) ∧
      periodicPaymentOccurrenceAt depth ≠
        periodicPaymentOccurrenceAt (depth + 1) ∧
      boundary.entry.normalization.normalForm.generatedNext.root.source.lawSurface =
        jointRoot.source.base.lawSurface
  everyDepthWrongTargets : ∀ depth : Nat,
    IsEmpty (EconomicViabilityAt (depth + 1)
      (stablePortfolioSourceAt (depth + 1)) noCapture) ∧
      IsEmpty (EconomicViabilityAt (depth + 1)
        (fullPortfolioSourceAt (depth + 1)) fullCapture)
  noRankOrCompletedHistory : ∀ _depth : Nat, True

theorem proofCarryingAdjacentEconomicViabilityBoundaryDirectConsumer :
    ProofCarryingAdjacentEconomicViabilityBoundaryCertificate where
  everyDepthBoundary := fun depth =>
    ⟨sourceGeneratedAdjacentEconomicViabilityBoundaryAt depth⟩
  everyDepthSamePredicate :=
    same_predicate_separates_both_sources_from_target
  everyDepthCommuting := boundary_root_next_and_disposition_commute
  everyDepthWrongTargets := wrong_target_axes_remain_nonviable
  noRankOrCompletedHistory :=
    adjacent_boundary_mouth_has_no_hitting_time_or_rank

end
end M14ProofCarryingAdjacentEconomicViabilityBoundaryRegression
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingAdjacentEconomicViabilityBoundaryRegression.same_predicate_separates_both_sources_from_target
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingAdjacentEconomicViabilityBoundaryRegression.boundary_root_next_and_disposition_commute
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingAdjacentEconomicViabilityBoundaryRegression.proofCarryingAdjacentEconomicViabilityBoundaryDirectConsumer
