import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.Intervals.Cells
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.Intervals

open scoped BigOperators
open MeasureTheory

theorem volume_of_original_cover (spans : List Span) (points : Finset ℚ)
    (includes : endpoints spans ⊆ points) :
    volume (cover spans) = ENNReal.ofReal (lengthOn points spans : ℝ) := by
  have disjoint : Set.PairwiseDisjoint (active points spans : Set ℚ) (cell points) := by
    intro first firstMem second secondMem different
    exact cells_are_pairwise_disjoint points (Finset.mem_filter.mp firstMem).1
      (Finset.mem_filter.mp secondMem).1 different
  rw [cover_is_exactly_the_occupied_cells spans points includes,
    measure_biUnion_finset disjoint (fun _ _ => measurableSet_Ico)]
  unfold lengthOn
  rw [Rat.cast_sum, ENNReal.ofReal_sum_of_nonneg]
  · apply Finset.sum_congr rfl
    intro left _
    rw [cell, Real.volume_Ico, Rat.cast_sub]
  · intro left _
    exact Rat.cast_nonneg.mpr (sub_nonneg.mpr (following_ge points left))

theorem volume_of_cover (spans : List Span) :
    volume (cover spans) = ENNReal.ofReal (length spans : ℝ) :=
  volume_of_original_cover spans _ (fun _ member => member)

theorem length_eq_measure (spans : List Span) :
    (length spans : ℝ) = (volume (cover spans)).toReal := by
  rw [volume_of_cover, ENNReal.toReal_ofReal (Rat.cast_nonneg.mpr (length_nonnegative spans))]

/-- Inserting other people's boundaries in the same clock does not alter
the measure of a person's original occupation. -/
theorem length_is_independent_of_additional_endpoints (spans : List Span) (points : Finset ℚ)
    (includes : endpoints spans ⊆ points) : lengthOn points spans = length spans := by
  have observed := congrArg ENNReal.toReal
    ((volume_of_original_cover spans points includes).symm.trans (volume_of_cover spans))
  rw [ENNReal.toReal_ofReal (Rat.cast_nonneg.mpr (lengthOn_nonnegative points spans)),
    ENNReal.toReal_ofReal (Rat.cast_nonneg.mpr (length_nonnegative spans))] at observed
  exact_mod_cast observed

theorem length_eq_of_same_cover {first second : List Span} (same : cover first = cover second) :
    length first = length second := by
  have equal : (length first : ℝ) = (length second : ℝ) := by
    rw [length_eq_measure, length_eq_measure, same]
  exact_mod_cast equal

theorem length_mono {first second : List Span} (inside : cover first ⊆ cover second) :
    length first ≤ length second := by
  have observed := measure_mono (μ := volume) inside
  rw [volume_of_cover, volume_of_cover] at observed
  have bound := ENNReal.toReal_mono ENNReal.ofReal_ne_top observed
  rw [ENNReal.toReal_ofReal (Rat.cast_nonneg.mpr (length_nonnegative first)),
    ENNReal.toReal_ofReal (Rat.cast_nonneg.mpr (length_nonnegative second))] at bound
  exact_mod_cast bound

theorem length_one (span : Span) : length [span] = span.finish - span.start := by
  have single : cover [span] = span.cover := by
    ext time
    simp [cover]
  have exactLength := length_eq_measure [span]
  rw [single, Span.cover, Real.volume_Ico, ENNReal.toReal_ofReal (by
    exact_mod_cast (sub_nonneg.mpr span.ordered : (0 : ℚ) ≤ span.finish - span.start))] at exactLength
  exact_mod_cast exactLength

theorem cover_append (first second : List Span) : cover (first ++ second) = cover first ∪ cover second := by
  ext time
  change (∃ span ∈ first ++ second, time ∈ span.cover) ↔
    (∃ span ∈ first, time ∈ span.cover) ∨ (∃ span ∈ second, time ∈ span.cover)
  constructor
  · rintro ⟨span, listed, inside⟩
    rcases List.mem_append.mp listed with left | right
    · exact Or.inl ⟨span, left, inside⟩
    · exact Or.inr ⟨span, right, inside⟩
  · rintro (⟨span, left, inside⟩ | ⟨span, right, inside⟩)
    · exact ⟨span, List.mem_append.mpr (Or.inl left), inside⟩
    · exact ⟨span, List.mem_append.mpr (Or.inr right), inside⟩

theorem duplicate_occupations_leave_the_same_length (spans : List Span) :
    length (spans ++ spans) = length spans :=
  length_eq_of_same_cover (by rw [cover_append, Set.union_self])

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.Intervals
