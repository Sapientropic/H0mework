import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.Intervals.Data
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.Intervals

def Span.cover (span : Span) : Set ℝ :=
  Set.Ico (span.start : ℝ) (span.finish : ℝ)

def cover (spans : List Span) : Set ℝ :=
  {time | ∃ span ∈ spans, time ∈ span.cover}

def cell (points : Finset ℚ) (left : ℚ) : Set ℝ :=
  Set.Ico (left : ℝ) (following points left : ℝ)

theorem cover_is_exactly_the_occupied_cells (spans : List Span) (points : Finset ℚ)
    (includes : endpoints spans ⊆ points) :
    cover spans = ⋃ left ∈ active points spans, cell points left := by
  classical
  ext time
  simp only [cover, Set.mem_ofPred_eq, Set.mem_iUnion, cell, Span.cover, Set.mem_Ico]
  constructor
  · rintro ⟨span, listed, begins, notFinished⟩
    let passed := points.filter fun (point : ℚ) => (point : ℝ) ≤ time
    have startPassed : span.start ∈ passed :=
      Finset.mem_filter.mpr ⟨includes (start_mem_endpoints listed), begins⟩
    let nonempty : passed.Nonempty := ⟨span.start, startPassed⟩
    let left := passed.max' nonempty
    have observed : left ∈ passed := Finset.max'_mem _ _
    obtain ⟨original, leftPassed⟩ := Finset.mem_filter.mp observed
    have pastStart : span.start ≤ left := Finset.le_max' _ _ startPassed
    have beforeFinish : left < span.finish := Rat.cast_lt.mp (leftPassed.trans_lt notFinished)
    have next := following_spec (includes (finish_mem_endpoints listed)) beforeFinish
    have beforeNext : time < (following points left : ℝ) := by
      by_contra! already
      have nextPassed : following points left ∈ passed := Finset.mem_filter.mpr ⟨next.2.1, already⟩
      exact (not_lt_of_ge (Finset.le_max' _ _ nextPassed)) next.1
    exact ⟨left, Finset.mem_filter.mpr ⟨original, (present_iff spans left).mpr
      ⟨span, listed, pastStart, beforeFinish⟩⟩, leftPassed, beforeNext⟩
  · rintro ⟨left, occupied, begins, notFinished⟩
    obtain ⟨span, listed, pastStart, beforeFinish⟩ :=
      (present_iff spans left).mp (Finset.mem_filter.mp occupied).2
    have next := following_spec (includes (finish_mem_endpoints listed)) beforeFinish
    exact ⟨span, listed, (Rat.cast_le.mpr pastStart).trans begins,
      notFinished.trans_le (Rat.cast_le.mpr next.2.2)⟩

theorem cells_are_pairwise_disjoint (points : Finset ℚ) :
    Set.PairwiseDisjoint (points : Set ℚ) (cell points) := by
  intro first firstMem second secondMem distinct
  rcases lt_or_gt_of_ne distinct with ordered | ordered
  · apply Set.disjoint_left.mpr
    intro time inFirst inSecond
    exact (not_lt_of_ge inSecond.1)
      (inFirst.2.trans_le (Rat.cast_le.mpr (following_spec secondMem ordered).2.2))
  · apply Set.disjoint_left.mpr
    intro time inFirst inSecond
    exact (not_lt_of_ge inFirst.1)
      (inSecond.2.trans_le (Rat.cast_le.mpr (following_spec firstMem ordered).2.2))

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.Intervals
