import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Root.Economy.Probability.ActualRepairFailureRefinedObserverFold

/-!
# M14 direct consumer for actual repair-failure probability

This consumer certifies the whole actual-trace probability geometry.
Canonical unit counting is generated from the paired trace.  The strongest
coarse exact-root/full-domain observer assigns probability one half to the
installed remove-capture event while remaining unable to reconstruct repair
authority.  Adding the existing failure kind separates the actual fibres,
restores repair factorization, and yields exact probabilities one and zero.

The certificate is Prop-only.  It stores no trace, weights, support,
normalizer, probability oracle, root, ledger, registry, or completed future.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingActualRepairFailureProbabilityRegression

noncomputable section

open UBI Policy
open Observer
open Probability Measure Kernel
open M14FiniteActualRepairFailureTrace
open M14ActualRepairFailureCountingMeasure
open M14ActualRepairFailureObserverKernelFold
open M14ActualRepairFailureRefinedObserverFold

local instance actualRepairFailureVisibleDecidableEq :
    DecidableEq ActualRepairFailureVisible :=
  Classical.decEq _

local instance actualRepairFailureRefinedVisibleDecidableEq :
    DecidableEq ActualRepairFailureRefinedVisible :=
  Classical.decEq _

theorem actualRepairFailureCountingMeasureExact (horizon : Nat) :
    (actualRepairFailureCountingMeasure horizon).occurrenceTrace =
        sourceGeneratedFiniteActualRepairFailureTrace horizon ∧
      (actualRepairFailureCountingMeasure horizon).occurrenceTrace.length =
        2 * horizon ∧
      (actualRepairFailureCountingMeasure horizon).totalMass =
        (2 * horizon : Nat) ∧
      (actualRepairFailureCountingMeasure horizon).occurrenceTrace.Nodup ∧
      (∀ weighted : AnyActualRepairFailure × ℚ≥0,
        weighted ∈
            (actualRepairFailureCountingMeasure horizon).weightedOccurrences →
          weighted.2 = 1 ∧
            CountingMeasureMemberCertificate horizon weighted.1) := by
  refine ⟨countingMeasure_occurrenceTrace horizon,
    countingMeasure_occurrenceTrace_length horizon,
    countingMeasure_totalMass horizon,
    countingMeasure_occurrenceTrace_nodup horizon, ?_⟩
  intro weighted membership
  let provenance :=
    countingMeasure_weighted_member_provenance membership
  have occurrenceMembership :
      weighted.1 ∈
        (actualRepairFailureCountingMeasure horizon).occurrenceTrace := by
    rw [countingMeasure_occurrenceTrace]
    exact provenance.2
  exact ⟨provenance.1,
    countingMeasure_member_exact occurrenceMembership⟩

theorem actualRepairFailureCoarseProbabilityExact (depth : Nat) :
    let fold := sourceGeneratedActualRepairFailureKernelFoldAt depth
    fold.fibre (visibleAt depth) =
        [tenureRepairFailureOccurrenceAt depth,
          routeRepairFailureOccurrenceAt depth] ∧
      fold.eventFibre (visibleAt depth) =
        [tenureRepairFailureOccurrenceAt depth] ∧
      fold.fibreMass (visibleAt depth) = 2 ∧
      fold.eventMass (visibleAt depth) = 1 ∧
      fold.readVisible (visibleAt depth) = some (1 / 2 : ℚ≥0) ∧
      fold.probabilityReadout.read
          (tenureRepairFailureOccurrenceAt depth) =
        fold.probabilityReadout.read
          (routeRepairFailureOccurrenceAt depth) ∧
      ¬ Nonempty
        (AuthorityCompleteReadoutAt actualRepairFailureObserver
          fold.probabilityReadout) :=
  actualRepairFailure_normalized_probability_exact depth

theorem actualRepairFailureZeroHorizonBoundary :
    ∀ visible : ActualRepairFailureVisible,
      (sourceGeneratedActualRepairFailureKernelFoldForHorizon 0).fibre
          visible = [] ∧
        (sourceGeneratedActualRepairFailureKernelFoldForHorizon 0).readVisible
          visible = none :=
  fun visible =>
    ⟨zeroHorizon_fibre_empty visible,
      zeroHorizon_readVisible_none visible⟩

theorem actualRepairFailureRefinedProbabilityExact (depth : Nat) :
    let fold := sourceGeneratedActualRepairFailureRefinedFoldAt depth
    refinedVisibleAt (tenureRepairFailureOccurrenceAt depth) ≠
        refinedVisibleAt (routeRepairFailureOccurrenceAt depth) ∧
      Nonempty (AuthorityFactorization
        actualRepairFailureRefinedObserver) ∧
      fold.fibre
          (refinedVisibleAt (tenureRepairFailureOccurrenceAt depth)) =
        [tenureRepairFailureOccurrenceAt depth] ∧
      fold.fibre
          (refinedVisibleAt (routeRepairFailureOccurrenceAt depth)) =
        [routeRepairFailureOccurrenceAt depth] ∧
      fold.eventFibre
          (refinedVisibleAt (tenureRepairFailureOccurrenceAt depth)) =
        [tenureRepairFailureOccurrenceAt depth] ∧
      fold.eventFibre
          (refinedVisibleAt (routeRepairFailureOccurrenceAt depth)) = [] ∧
      fold.readVisible
          (refinedVisibleAt (tenureRepairFailureOccurrenceAt depth)) =
        some 1 ∧
      fold.readVisible
          (refinedVisibleAt (routeRepairFailureOccurrenceAt depth)) =
        some 0 ∧
      fold.probabilityReadout.read
          (tenureRepairFailureOccurrenceAt depth) ≠
        fold.probabilityReadout.read
          (routeRepairFailureOccurrenceAt depth) :=
  ⟨canonical_refined_visibles_distinct depth,
    ⟨refinedRepairAuthorityFactorization⟩,
    refinedFold_tenure_fibre_exact depth,
    refinedFold_route_fibre_exact depth,
    refinedFold_tenure_eventFibre_exact depth,
    refinedFold_route_eventFibre_empty depth,
    refinedFold_tenure_readVisible_one depth,
    refinedFold_route_readVisible_zero depth,
    refined_probability_separates_actual_pair depth⟩

structure ProofCarryingActualRepairFailureProbabilityCertificate : Prop where
  eventIsSourceFailure : ∀ occurrence : AnyActualRepairFailure,
    removeCaptureEvent occurrence ↔
      occurrence.failureKind = ExactExitFailureKind.tenureCapture
  everyCountingMeasure : ∀ horizon : Nat,
    (actualRepairFailureCountingMeasure horizon).occurrenceTrace =
        sourceGeneratedFiniteActualRepairFailureTrace horizon ∧
      (actualRepairFailureCountingMeasure horizon).occurrenceTrace.length =
        2 * horizon ∧
      (actualRepairFailureCountingMeasure horizon).totalMass =
        (2 * horizon : Nat) ∧
      (actualRepairFailureCountingMeasure horizon).occurrenceTrace.Nodup ∧
      (∀ weighted : AnyActualRepairFailure × ℚ≥0,
        weighted ∈
            (actualRepairFailureCountingMeasure horizon).weightedOccurrences →
          weighted.2 = 1 ∧
            CountingMeasureMemberCertificate horizon weighted.1)
  everyCoarseProbability : ∀ depth : Nat,
    let fold := sourceGeneratedActualRepairFailureKernelFoldAt depth
    fold.fibre (visibleAt depth) =
        [tenureRepairFailureOccurrenceAt depth,
          routeRepairFailureOccurrenceAt depth] ∧
      fold.eventFibre (visibleAt depth) =
        [tenureRepairFailureOccurrenceAt depth] ∧
      fold.fibreMass (visibleAt depth) = 2 ∧
      fold.eventMass (visibleAt depth) = 1 ∧
      fold.readVisible (visibleAt depth) = some (1 / 2 : ℚ≥0) ∧
      fold.probabilityReadout.read
          (tenureRepairFailureOccurrenceAt depth) =
        fold.probabilityReadout.read
          (routeRepairFailureOccurrenceAt depth) ∧
      ¬ Nonempty
        (AuthorityCompleteReadoutAt actualRepairFailureObserver
          fold.probabilityReadout)
  zeroHorizonBoundary : ∀ visible : ActualRepairFailureVisible,
    (sourceGeneratedActualRepairFailureKernelFoldForHorizon 0).fibre
        visible = [] ∧
      (sourceGeneratedActualRepairFailureKernelFoldForHorizon 0).readVisible
        visible = none
  everyRefinedProbability : ∀ depth : Nat,
    let fold := sourceGeneratedActualRepairFailureRefinedFoldAt depth
    refinedVisibleAt (tenureRepairFailureOccurrenceAt depth) ≠
        refinedVisibleAt (routeRepairFailureOccurrenceAt depth) ∧
      Nonempty (AuthorityFactorization
        actualRepairFailureRefinedObserver) ∧
      fold.fibre
          (refinedVisibleAt (tenureRepairFailureOccurrenceAt depth)) =
        [tenureRepairFailureOccurrenceAt depth] ∧
      fold.fibre
          (refinedVisibleAt (routeRepairFailureOccurrenceAt depth)) =
        [routeRepairFailureOccurrenceAt depth] ∧
      fold.eventFibre
          (refinedVisibleAt (tenureRepairFailureOccurrenceAt depth)) =
        [tenureRepairFailureOccurrenceAt depth] ∧
      fold.eventFibre
          (refinedVisibleAt (routeRepairFailureOccurrenceAt depth)) = [] ∧
      fold.readVisible
          (refinedVisibleAt (tenureRepairFailureOccurrenceAt depth)) =
        some 1 ∧
      fold.readVisible
          (refinedVisibleAt (routeRepairFailureOccurrenceAt depth)) =
        some 0 ∧
      fold.probabilityReadout.read
          (tenureRepairFailureOccurrenceAt depth) ≠
        fold.probabilityReadout.read
          (routeRepairFailureOccurrenceAt depth)

theorem proofCarryingActualRepairFailureProbabilityDirectConsumer :
    ProofCarryingActualRepairFailureProbabilityCertificate where
  eventIsSourceFailure := removeCaptureEvent_iff_tenureFailureKind
  everyCountingMeasure := actualRepairFailureCountingMeasureExact
  everyCoarseProbability := actualRepairFailureCoarseProbabilityExact
  zeroHorizonBoundary := actualRepairFailureZeroHorizonBoundary
  everyRefinedProbability := actualRepairFailureRefinedProbabilityExact

end
end M14ProofCarryingActualRepairFailureProbabilityRegression
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingActualRepairFailureProbabilityRegression.actualRepairFailureCountingMeasureExact
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingActualRepairFailureProbabilityRegression.actualRepairFailureCoarseProbabilityExact
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingActualRepairFailureProbabilityRegression.actualRepairFailureRefinedProbabilityExact
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingActualRepairFailureProbabilityRegression.proofCarryingActualRepairFailureProbabilityDirectConsumer
