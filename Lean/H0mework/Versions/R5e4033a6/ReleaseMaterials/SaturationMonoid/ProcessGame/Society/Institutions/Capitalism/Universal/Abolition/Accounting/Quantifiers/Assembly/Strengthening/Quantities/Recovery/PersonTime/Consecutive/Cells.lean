import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.Intervals.Cells
import Mathlib.Data.Finset.Prod

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.Consecutive

open Intervals

def OccupiedBetween (spans : List Span) (start finish : ℚ) : Prop :=
  ∀ left ∈ endpoints spans, start ≤ left → left < finish → present spans left = true

instance (spans : List Span) (start finish : ℚ) : Decidable (OccupiedBetween spans start finish) := by
  unfold OccupiedBetween
  infer_instance

/-- An interval with original endpoints is occupied throughout exactly
when every original cell starting inside it is occupied. -/
theorem all_original_cells_occupied_iff (spans : List Span) {start finish : ℚ}
    (originalStart : start ∈ endpoints spans) (originalFinish : finish ∈ endpoints spans) :
    OccupiedBetween spans start finish ↔ Set.Ico (start : ℝ) (finish : ℝ) ⊆ cover spans := by
  classical
  constructor
  · intro all time timeIn
    let passed := (endpoints spans).filter fun (point : ℚ) => (point : ℝ) ≤ time
    have startPassed : start ∈ passed := Finset.mem_filter.mpr ⟨originalStart, timeIn.1⟩
    let nonempty : passed.Nonempty := ⟨start, startPassed⟩
    let left := passed.max' nonempty
    obtain ⟨leftOriginal, leftPassed⟩ := Finset.mem_filter.mp (Finset.max'_mem passed nonempty)
    have begin : start ≤ left := Finset.le_max' passed start startPassed
    have finishBefore : left < finish := Rat.cast_lt.mp (leftPassed.trans_lt timeIn.2)
    have next := following_spec originalFinish finishBefore
    have timeBeforeNext : time < (following (endpoints spans) left : ℝ) := by
      by_contra! already
      have nextPassed : following (endpoints spans) left ∈ passed :=
        Finset.mem_filter.mpr ⟨next.2.1, already⟩
      exact (not_lt_of_ge (Finset.le_max' passed _ nextPassed)) next.1
    rw [cover_is_exactly_the_occupied_cells spans (endpoints spans) (fun _ present => present)]
    refine Set.mem_iUnion.mpr ⟨left, Set.mem_iUnion.mpr ⟨?_, leftPassed, timeBeforeNext⟩⟩
    exact Finset.mem_filter.mpr ⟨leftOriginal, all left leftOriginal begin finishBefore⟩
  · intro all left _ after before
    obtain ⟨span, listed, startInside, finishInside⟩ :=
      all (show (left : ℝ) ∈ Set.Ico (start : ℝ) (finish : ℝ) from ⟨Rat.cast_le.mpr after, Rat.cast_lt.mpr before⟩)
    exact (present_iff spans left).mpr ⟨span, listed, Rat.cast_le.mp startInside, Rat.cast_lt.mp finishInside⟩

/-- Candidate widths are original endpoint differences whose entire
half-open interval is occupied. The empty clock has width zero. -/
def widths (spans : List Span) : Finset ℚ :=
  insert 0 ((((endpoints spans).product (endpoints spans)).filter fun pair =>
    pair.1 ≤ pair.2 ∧ OccupiedBetween spans pair.1 pair.2).image fun pair => pair.2 - pair.1)

def longest (spans : List Span) : ℚ := (widths spans).max' ⟨0, Finset.mem_insert_self _ _⟩

theorem longest_nonnegative (spans : List Span) : 0 ≤ longest spans :=
  Finset.le_max' _ _ (Finset.mem_insert_self _ _)

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.Consecutive
