import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Root.Economy.Probability.ActualRepairFailureObserverKernelFold

/-!
# M14 source-refined actual repair-failure probability

The coarse exact-root/full-domain observer assigns the same normalized
probability to the two actual repair authorities.  Refinement adds only the
already generated failure kind.  This separates the two visible fibres and
restores canonical repair factorization: tenure reads probability one for
the installed remove-capture event, while route reads probability zero.

No new label, repair table, occurrence, measure, root, or probability is
introduced.  The refined geometry is computed from the same counting measure
and the same installed repair authority.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ActualRepairFailureRefinedObserverFold

noncomputable section

open UBI Policy
open Observer
open Probability Measure Kernel
open M14TenureCaptureRouteRepairNoGoRegression
open M14FiniteActualRepairFailureTrace
open M14ActualRepairFailureCountingMeasure
open M14ActualRepairFailureObserverKernelFold

abbrev ActualRepairFailureRefinedVisible :=
  ActualRepairFailureVisible × ExactExitFailureKind

local instance actualRepairFailureRefinedVisibleDecidableEq :
    DecidableEq ActualRepairFailureRefinedVisible :=
  Classical.decEq _

def actualRepairFailureRefinedObserver :
    AuthorityObserver AnyActualRepairFailure
      ActualRepairFailureRefinedVisible ExactExitRepair where
  forget := fun occurrence =>
    (actualRepairFailureObserver.forget occurrence,
      occurrence.failureKind)
  authorityK := actualRepairFailureObserver.authorityK

def refinedVisibleAt (occurrence : AnyActualRepairFailure) :
    ActualRepairFailureRefinedVisible :=
  actualRepairFailureRefinedObserver.forget occurrence

/-- Existing source-owned repair compiler, exposed only under the local
readout name.  No second failure-to-repair table is defined here. -/
abbrev repairAtFailureKind :
    ExactExitFailureKind → ExactExitRepair :=
  exactExitRepairCompiler.compile

theorem repairAtFailureKind_exact (occurrence : AnyActualRepairFailure) :
    repairAtFailureKind occurrence.failureKind =
      actualRepairFailureRefinedObserver.authorityK occurrence := by
  rcases occurrence with ⟨depth, origin, actual⟩
  cases origin <;> rfl

/-- Adding the source failure kind restores visible repair authority. -/
def refinedRepairAuthorityFactorization :
    AuthorityFactorization actualRepairFailureRefinedObserver where
  readAuthority := fun visible => repairAtFailureKind visible.2
  preservesActualAuthority := repairAtFailureKind_exact

theorem canonical_refined_visibles_distinct (depth : Nat) :
    refinedVisibleAt (tenureRepairFailureOccurrenceAt depth) ≠
      refinedVisibleAt (routeRepairFailureOccurrenceAt depth) := by
  intro equality
  have kindEquality := congrArg Prod.snd equality
  cases kindEquality

def sourceGeneratedActualRepairFailureRefinedFoldAt (depth : Nat) :
    NormalizedFiniteObserverKernelFoldAt
      (actualRepairFailureCountingMeasure (depth + 1))
      actualRepairFailureRefinedObserver removeCaptureEvent :=
  NormalizedFiniteObserverKernelFoldAt.generate
    (actualRepairFailureCountingMeasure (depth + 1))
    actualRepairFailureRefinedObserver removeCaptureEvent

theorem tenure_refinedVisible_eq_iff (index depth : Nat) :
    actualRepairFailureRefinedObserver.forget
        (tenureRepairFailureOccurrenceAt index) =
      refinedVisibleAt (tenureRepairFailureOccurrenceAt depth) ↔
        index = depth := by
  constructor
  · intro equality
    have coarseEquality := congrArg (fun visible => visible.1) equality
    exact (tenure_visible_eq_visibleAt_iff index depth).mp coarseEquality
  · rintro rfl
    rfl

theorem route_refinedVisible_eq_iff (index depth : Nat) :
    actualRepairFailureRefinedObserver.forget
        (routeRepairFailureOccurrenceAt index) =
      refinedVisibleAt (routeRepairFailureOccurrenceAt depth) ↔
        index = depth := by
  constructor
  · intro equality
    have rootEquality :=
      congrArg (fun visible => visible.1.1) equality
    have visitEquality := congrArg Sigma.fst rootEquality
    exact M14UBIPeriodicRootHistory.temporalVisitAt_injective visitEquality
  · rintro rfl
    rfl

theorem route_ne_tenure_refinedVisible (index depth : Nat) :
    actualRepairFailureRefinedObserver.forget
        (routeRepairFailureOccurrenceAt index) ≠
      refinedVisibleAt (tenureRepairFailureOccurrenceAt depth) := by
  intro equality
  have kindEquality := congrArg Prod.snd equality
  cases kindEquality

theorem tenure_ne_route_refinedVisible (index depth : Nat) :
    actualRepairFailureRefinedObserver.forget
        (tenureRepairFailureOccurrenceAt index) ≠
      refinedVisibleAt (routeRepairFailureOccurrenceAt depth) := by
  intro equality
  have kindEquality := congrArg Prod.snd equality
  cases kindEquality

private theorem range_succ_filter_eq_last (depth : Nat) :
    (List.range (depth + 1)).filter (fun index => index = depth) =
      [depth] := by
  rw [show depth + 1 = depth.succ by omega, List.range_succ,
    List.filter_append]
  have prefixEmpty :
      (List.range depth).filter (fun index => index = depth) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro index membership
    simpa using Nat.ne_of_lt (List.mem_range.mp membership)
  rw [prefixEmpty]
  simp

theorem refinedFold_tenure_fibre_exact (depth : Nat) :
    let fold := sourceGeneratedActualRepairFailureRefinedFoldAt depth
    fold.fibre
        (refinedVisibleAt (tenureRepairFailureOccurrenceAt depth)) =
      [tenureRepairFailureOccurrenceAt depth] := by
  dsimp only
  unfold NormalizedFiniteObserverKernelFoldAt.fibre
  rw [countingMeasure_occurrenceTrace]
  unfold sourceGeneratedFiniteActualRepairFailureTrace
    finiteActualTenureRepairFailureTrace
    finiteActualRouteRepairFailureTrace
  rw [List.filter_append, List.filter_map, List.filter_map]
  change
    List.map tenureRepairFailureOccurrenceAt
        ((List.range (depth + 1)).filter fun index =>
          actualRepairFailureRefinedObserver.forget
              (tenureRepairFailureOccurrenceAt index) =
            refinedVisibleAt (tenureRepairFailureOccurrenceAt depth)) ++
      List.map routeRepairFailureOccurrenceAt
        ((List.range (depth + 1)).filter fun index =>
          actualRepairFailureRefinedObserver.forget
              (routeRepairFailureOccurrenceAt index) =
            refinedVisibleAt (tenureRepairFailureOccurrenceAt depth)) =
      [tenureRepairFailureOccurrenceAt depth]
  simp_rw [tenure_refinedVisible_eq_iff,
    route_ne_tenure_refinedVisible]
  rw [range_succ_filter_eq_last]
  simp

theorem refinedFold_route_fibre_exact (depth : Nat) :
    let fold := sourceGeneratedActualRepairFailureRefinedFoldAt depth
    fold.fibre
        (refinedVisibleAt (routeRepairFailureOccurrenceAt depth)) =
      [routeRepairFailureOccurrenceAt depth] := by
  dsimp only
  unfold NormalizedFiniteObserverKernelFoldAt.fibre
  rw [countingMeasure_occurrenceTrace]
  unfold sourceGeneratedFiniteActualRepairFailureTrace
    finiteActualTenureRepairFailureTrace
    finiteActualRouteRepairFailureTrace
  rw [List.filter_append, List.filter_map, List.filter_map]
  change
    List.map tenureRepairFailureOccurrenceAt
        ((List.range (depth + 1)).filter fun index =>
          actualRepairFailureRefinedObserver.forget
              (tenureRepairFailureOccurrenceAt index) =
            refinedVisibleAt (routeRepairFailureOccurrenceAt depth)) ++
      List.map routeRepairFailureOccurrenceAt
        ((List.range (depth + 1)).filter fun index =>
          actualRepairFailureRefinedObserver.forget
              (routeRepairFailureOccurrenceAt index) =
            refinedVisibleAt (routeRepairFailureOccurrenceAt depth)) =
      [routeRepairFailureOccurrenceAt depth]
  simp_rw [tenure_ne_route_refinedVisible,
    route_refinedVisible_eq_iff]
  rw [range_succ_filter_eq_last]
  simp

theorem refinedFold_tenure_eventFibre_exact (depth : Nat) :
    let fold := sourceGeneratedActualRepairFailureRefinedFoldAt depth
    fold.eventFibre
        (refinedVisibleAt (tenureRepairFailureOccurrenceAt depth)) =
      [tenureRepairFailureOccurrenceAt depth] := by
  dsimp only
  unfold NormalizedFiniteObserverKernelFoldAt.eventFibre
  rw [countingMeasure_occurrenceTrace]
  unfold sourceGeneratedFiniteActualRepairFailureTrace
    finiteActualTenureRepairFailureTrace
    finiteActualRouteRepairFailureTrace
  rw [List.filter_append, List.filter_map, List.filter_map]
  change
    List.map tenureRepairFailureOccurrenceAt
        ((List.range (depth + 1)).filter fun index =>
          actualRepairFailureRefinedObserver.forget
                (tenureRepairFailureOccurrenceAt index) =
              refinedVisibleAt (tenureRepairFailureOccurrenceAt depth) ∧
            removeCaptureEvent (tenureRepairFailureOccurrenceAt index)) ++
      List.map routeRepairFailureOccurrenceAt
        ((List.range (depth + 1)).filter fun index =>
          actualRepairFailureRefinedObserver.forget
                (routeRepairFailureOccurrenceAt index) =
              refinedVisibleAt (tenureRepairFailureOccurrenceAt depth) ∧
            removeCaptureEvent (routeRepairFailureOccurrenceAt index)) =
      [tenureRepairFailureOccurrenceAt depth]
  simp_rw [tenure_removeCaptureEvent, and_true,
    route_not_removeCaptureEvent, and_false,
    tenure_refinedVisible_eq_iff]
  rw [range_succ_filter_eq_last]
  simp

theorem refinedFold_route_eventFibre_empty (depth : Nat) :
    let fold := sourceGeneratedActualRepairFailureRefinedFoldAt depth
    fold.eventFibre
        (refinedVisibleAt (routeRepairFailureOccurrenceAt depth)) = [] := by
  dsimp only
  unfold NormalizedFiniteObserverKernelFoldAt.eventFibre
  rw [countingMeasure_occurrenceTrace]
  unfold sourceGeneratedFiniteActualRepairFailureTrace
    finiteActualTenureRepairFailureTrace
    finiteActualRouteRepairFailureTrace
  rw [List.filter_append, List.filter_map, List.filter_map]
  change
    List.map tenureRepairFailureOccurrenceAt
        ((List.range (depth + 1)).filter fun index =>
          actualRepairFailureRefinedObserver.forget
                (tenureRepairFailureOccurrenceAt index) =
              refinedVisibleAt (routeRepairFailureOccurrenceAt depth) ∧
            removeCaptureEvent (tenureRepairFailureOccurrenceAt index)) ++
      List.map routeRepairFailureOccurrenceAt
        ((List.range (depth + 1)).filter fun index =>
          actualRepairFailureRefinedObserver.forget
                (routeRepairFailureOccurrenceAt index) =
              refinedVisibleAt (routeRepairFailureOccurrenceAt depth) ∧
            removeCaptureEvent (routeRepairFailureOccurrenceAt index)) = []
  simp_rw [tenure_ne_route_refinedVisible, false_and,
    route_not_removeCaptureEvent, and_false]
  simp

theorem refinedFold_tenure_fibreMass_exact (depth : Nat) :
    let fold := sourceGeneratedActualRepairFailureRefinedFoldAt depth
    fold.fibreMass
        (refinedVisibleAt (tenureRepairFailureOccurrenceAt depth)) = 1 := by
  dsimp only
  unfold NormalizedFiniteObserverKernelFoldAt.fibreMass
  rw [countingMeasure_eventMass_eq_filtered_length]
  have exactFibre := refinedFold_tenure_fibre_exact depth
  change
    ((actualRepairFailureCountingMeasure (depth + 1)).occurrenceTrace.filter
      (fun occurrence =>
        actualRepairFailureRefinedObserver.forget occurrence =
          refinedVisibleAt (tenureRepairFailureOccurrenceAt depth))) =
      [tenureRepairFailureOccurrenceAt depth] at exactFibre
  rw [exactFibre]
  rfl

theorem refinedFold_route_fibreMass_exact (depth : Nat) :
    let fold := sourceGeneratedActualRepairFailureRefinedFoldAt depth
    fold.fibreMass
        (refinedVisibleAt (routeRepairFailureOccurrenceAt depth)) = 1 := by
  dsimp only
  unfold NormalizedFiniteObserverKernelFoldAt.fibreMass
  rw [countingMeasure_eventMass_eq_filtered_length]
  have exactFibre := refinedFold_route_fibre_exact depth
  change
    ((actualRepairFailureCountingMeasure (depth + 1)).occurrenceTrace.filter
      (fun occurrence =>
        actualRepairFailureRefinedObserver.forget occurrence =
          refinedVisibleAt (routeRepairFailureOccurrenceAt depth))) =
      [routeRepairFailureOccurrenceAt depth] at exactFibre
  rw [exactFibre]
  rfl

theorem refinedFold_tenure_eventMass_exact (depth : Nat) :
    let fold := sourceGeneratedActualRepairFailureRefinedFoldAt depth
    fold.eventMass
        (refinedVisibleAt (tenureRepairFailureOccurrenceAt depth)) = 1 := by
  dsimp only
  unfold NormalizedFiniteObserverKernelFoldAt.eventMass
  rw [countingMeasure_eventMass_eq_filtered_length]
  have exactEvent := refinedFold_tenure_eventFibre_exact depth
  change
    ((actualRepairFailureCountingMeasure (depth + 1)).occurrenceTrace.filter
      (fun occurrence =>
        actualRepairFailureRefinedObserver.forget occurrence =
            refinedVisibleAt (tenureRepairFailureOccurrenceAt depth) ∧
          removeCaptureEvent occurrence)) =
      [tenureRepairFailureOccurrenceAt depth] at exactEvent
  rw [exactEvent]
  rfl

theorem refinedFold_route_eventMass_zero (depth : Nat) :
    let fold := sourceGeneratedActualRepairFailureRefinedFoldAt depth
    fold.eventMass
        (refinedVisibleAt (routeRepairFailureOccurrenceAt depth)) = 0 := by
  dsimp only
  unfold NormalizedFiniteObserverKernelFoldAt.eventMass
  rw [countingMeasure_eventMass_eq_filtered_length]
  have exactEvent := refinedFold_route_eventFibre_empty depth
  change
    ((actualRepairFailureCountingMeasure (depth + 1)).occurrenceTrace.filter
      (fun occurrence =>
        actualRepairFailureRefinedObserver.forget occurrence =
            refinedVisibleAt (routeRepairFailureOccurrenceAt depth) ∧
          removeCaptureEvent occurrence)) = [] at exactEvent
  rw [exactEvent]
  rfl

theorem refinedFold_tenure_readVisible_one (depth : Nat) :
    let fold := sourceGeneratedActualRepairFailureRefinedFoldAt depth
    fold.readVisible
        (refinedVisibleAt (tenureRepairFailureOccurrenceAt depth)) =
      some 1 := by
  dsimp only
  let fold := sourceGeneratedActualRepairFailureRefinedFoldAt depth
  have positive : 0 < fold.fibreMass
      (refinedVisibleAt (tenureRepairFailureOccurrenceAt depth)) := by
    rw [refinedFold_tenure_fibreMass_exact]
    norm_num
  rw [fold.readVisible_eq_some_ratio positive,
    refinedFold_tenure_eventMass_exact,
    refinedFold_tenure_fibreMass_exact]
  norm_num

theorem refinedFold_route_readVisible_zero (depth : Nat) :
    let fold := sourceGeneratedActualRepairFailureRefinedFoldAt depth
    fold.readVisible
        (refinedVisibleAt (routeRepairFailureOccurrenceAt depth)) =
      some 0 := by
  dsimp only
  let fold := sourceGeneratedActualRepairFailureRefinedFoldAt depth
  have positive : 0 < fold.fibreMass
      (refinedVisibleAt (routeRepairFailureOccurrenceAt depth)) := by
    rw [refinedFold_route_fibreMass_exact]
    norm_num
  rw [fold.readVisible_eq_some_ratio positive,
    refinedFold_route_eventMass_zero,
    refinedFold_route_fibreMass_exact]
  norm_num

theorem refined_probability_separates_actual_pair (depth : Nat) :
    let fold := sourceGeneratedActualRepairFailureRefinedFoldAt depth
    fold.probabilityReadout.read
        (tenureRepairFailureOccurrenceAt depth) ≠
      fold.probabilityReadout.read
        (routeRepairFailureOccurrenceAt depth) := by
  dsimp only
  rw [NormalizedFiniteObserverKernelFoldAt.probabilityReadout_read,
    NormalizedFiniteObserverKernelFoldAt.probabilityReadout_read]
  change
    (sourceGeneratedActualRepairFailureRefinedFoldAt depth).readVisible
        (refinedVisibleAt (tenureRepairFailureOccurrenceAt depth)) ≠
      (sourceGeneratedActualRepairFailureRefinedFoldAt depth).readVisible
        (refinedVisibleAt (routeRepairFailureOccurrenceAt depth))
  rw [refinedFold_tenure_readVisible_one,
    refinedFold_route_readVisible_zero]
  decide

end
end M14ActualRepairFailureRefinedObserverFold
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ActualRepairFailureRefinedObserverFold.refinedRepairAuthorityFactorization
#print axioms SaturationMonoid.ProcessGame.Society.M14ActualRepairFailureRefinedObserverFold.refinedFold_tenure_readVisible_one
#print axioms SaturationMonoid.ProcessGame.Society.M14ActualRepairFailureRefinedObserverFold.refinedFold_route_readVisible_zero
#print axioms SaturationMonoid.ProcessGame.Society.M14ActualRepairFailureRefinedObserverFold.refined_probability_separates_actual_pair
