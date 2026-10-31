import Mathlib.Data.List.Nodup
import Mathlib.Data.NNRat.BigOperators
import Mathlib.Algebra.Order.Ring.NNRat

/-!
# Neutral finite observer measure

`FiniteObserverMeasure` is finite mathematics, not an authority source.  It
stores an ordered list of occurrence/weight pairs whose occurrence projection
does not repeat.  Zero-weight occurrences remain in that list; mathematical
support is the derived positive-weight sublist.  Total and event mass are
canonical list folds, so this carrier needs no `DecidableEq` on occurrences.

An arbitrary value of this type is only a neutral readout.  The source-owned
producer tying it to actual ProcessGame crossings is defined separately.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace Probability
namespace Measure

universe uOccurrence

section

/-- One neutral finite occurrence mass.  The list retains chronological
occurrence identity, including entries whose coefficient is zero. -/
structure FiniteObserverMeasure (Occurrence : Type uOccurrence) :
    Type uOccurrence where
  weightedOccurrences : List (Occurrence × ℚ≥0)
  occurrence_nodup : (weightedOccurrences.map Prod.fst).Nodup

namespace FiniteObserverMeasure

variable {Occurrence : Type uOccurrence}
variable (measure : FiniteObserverMeasure Occurrence)

/-- Ordered occurrence carrier underlying the finite mass. -/
def occurrenceTrace : List Occurrence :=
  measure.weightedOccurrences.map Prod.fst

theorem occurrenceTrace_nodup : measure.occurrenceTrace.Nodup :=
  measure.occurrence_nodup

/-- Positive weighted support.  Zero-weight occurrences remain in
`weightedOccurrences` but are absent from this mathematical support. -/
def positiveWeightedSupport : List (Occurrence × ℚ≥0) :=
  measure.weightedOccurrences.filter fun weighted => weighted.2 ≠ 0

/-- Occurrence projection of positive weighted support. -/
def support : List Occurrence :=
  measure.positiveWeightedSupport.map Prod.fst

/-- Positive support is a sublist of the full occurrence trace. -/
theorem support_sublist_occurrenceTrace :
    List.Sublist measure.support measure.occurrenceTrace := by
  unfold support positiveWeightedSupport occurrenceTrace
  exact List.Sublist.map Prod.fst List.filter_sublist

theorem support_nodup : measure.support.Nodup :=
  List.Nodup.sublist measure.support_sublist_occurrenceTrace
    measure.occurrenceTrace_nodup

theorem support_subset_occurrenceTrace
    {occurrence : Occurrence}
    (membership : occurrence ∈ measure.support) :
    occurrence ∈ measure.occurrenceTrace :=
  measure.support_sublist_occurrenceTrace.mem membership

/-- Every weighted entry projects to the occurrence trace. -/
theorem occurrence_mem_of_weighted_mem
    {weighted : Occurrence × ℚ≥0}
    (membership : weighted ∈ measure.weightedOccurrences) :
    weighted.1 ∈ measure.occurrenceTrace :=
  List.mem_map.mpr ⟨weighted, membership, rfl⟩

/-- The weighted list itself is duplicate-free because duplicate pairs would
already duplicate their occurrence projections. -/
theorem weightedOccurrences_nodup :
    measure.weightedOccurrences.Nodup :=
  List.Nodup.of_map Prod.fst measure.occurrence_nodup

/-- Canonical total mass fold.  No normalization is performed. -/
def totalMass : ℚ≥0 :=
  measure.weightedOccurrences.foldr
    (fun weighted accumulated => weighted.2 + accumulated) 0

/-- Canonical event-filtered mass fold. -/
def eventMass
    (event : Occurrence → Prop)
    [DecidablePred event] : ℚ≥0 :=
  measure.weightedOccurrences.foldr
    (fun weighted accumulated =>
      if event weighted.1 then weighted.2 + accumulated else accumulated)
    0

@[simp] theorem totalMass_empty :
    (FiniteObserverMeasure.mk [] (by simp) :
      FiniteObserverMeasure Occurrence).totalMass = 0 :=
  rfl

@[simp] theorem eventMass_empty
    (event : Occurrence → Prop)
    [DecidablePred event] :
    (FiniteObserverMeasure.mk [] (by simp) :
      FiniteObserverMeasure Occurrence).eventMass event = 0 :=
  rfl

@[simp] theorem eventMass_false :
    measure.eventMass (fun _occurrence => False) = 0 := by
  unfold eventMass
  induction measure.weightedOccurrences with
  | nil => rfl
  | cons weighted rest inductionHypothesis =>
      simp

@[simp] theorem eventMass_true :
    measure.eventMass (fun _occurrence => True) = measure.totalMass := by
  unfold eventMass totalMass
  induction measure.weightedOccurrences with
  | nil => rfl
  | cons weighted rest inductionHypothesis =>
      simp

private theorem eventFold_le_totalFold
    (weightedOccurrences : List (Occurrence × ℚ≥0))
    (event : Occurrence → Prop)
    [DecidablePred event] :
    weightedOccurrences.foldr
        (fun weighted accumulated =>
          if event weighted.1 then weighted.2 + accumulated else accumulated)
        0 ≤
      weightedOccurrences.foldr
        (fun weighted accumulated => weighted.2 + accumulated) 0 := by
  induction weightedOccurrences with
  | nil => rfl
  | cons weighted rest inductionHypothesis =>
      by_cases observed : event weighted.1
      · simp only [List.foldr_cons, observed, if_pos]
        exact add_le_add_right inductionHypothesis weighted.2
      · simp only [List.foldr_cons, observed]
        exact inductionHypothesis.trans <| by
          have nonnegative := add_le_add_left
            (show (0 : ℚ≥0) ≤ weighted.2 from bot_le)
            (rest.foldr (fun next accumulated => next.2 + accumulated) 0)
          rwa [zero_add] at nonnegative

/-- Filtering an event cannot increase a nonnegative finite mass. -/
theorem eventMass_le_totalMass
    (event : Occurrence → Prop)
    [DecidablePred event] :
    measure.eventMass event ≤ measure.totalMass :=
  eventFold_le_totalFold measure.weightedOccurrences event

/-- Every coefficient is nonnegative by its neutral coefficient carrier. -/
theorem weight_nonnegative
    (weighted : Occurrence × ℚ≥0) :
    0 ≤ weighted.2 :=
  weighted.2.2

/-- An empty retained occurrence trace has zero total mass. -/
theorem totalMass_eq_zero_of_occurrenceTrace_eq_nil
    (empty : measure.occurrenceTrace = []) :
    measure.totalMass = 0 := by
  cases weightedEq : measure.weightedOccurrences with
  | nil => simp [totalMass, weightedEq]
  | cons weighted rest =>
      simp [occurrenceTrace, weightedEq] at empty

end FiniteObserverMeasure

end
end Measure
end Probability
end Society
end ProcessGame
end SaturationMonoid
