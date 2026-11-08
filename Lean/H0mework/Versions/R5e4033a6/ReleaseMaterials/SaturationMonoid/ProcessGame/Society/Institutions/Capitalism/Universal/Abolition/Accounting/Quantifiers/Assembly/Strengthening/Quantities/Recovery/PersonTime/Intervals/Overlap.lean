import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.Intervals.Measure

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.Intervals

open MeasureTheory

/-- Empty intersections remain zero-width clock intervals. -/
def Span.overlap (first second : Span) : Span :=
  let start := max first.start second.start
  ⟨start, max start (min first.finish second.finish), le_max_left _ _⟩

theorem Span.overlap_cover (first second : Span) :
    (first.overlap second).cover = first.cover ∩ second.cover := by
  ext time
  simp only [Set.mem_inter_iff, Span.cover, Span.overlap, Rat.cast_max, Rat.cast_min,
    Set.mem_Ico, max_le_iff, lt_min_iff, lt_max_iff]
  constructor
  · rintro ⟨⟨startFirst, startSecond⟩, (tooEarly | ⟨finishFirst, finishSecond⟩)⟩
    · rcases tooEarly with tooEarly | tooEarly
      · exact ((not_lt_of_ge startFirst) tooEarly).elim
      · exact ((not_lt_of_ge startSecond) tooEarly).elim
    · exact ⟨⟨startFirst, finishFirst⟩, startSecond, finishSecond⟩
  · rintro ⟨⟨startFirst, finishFirst⟩, startSecond, finishSecond⟩
    exact ⟨⟨startFirst, startSecond⟩, Or.inr ⟨finishFirst, finishSecond⟩⟩

def overlaps (first second : List Span) : List Span :=
  first.flatMap fun left => second.map (left.overlap)

theorem cover_overlaps (first second : List Span) :
    cover (overlaps first second) = cover first ∩ cover second := by
  ext time
  change (∃ span ∈ overlaps first second, time ∈ span.cover) ↔
    (∃ span ∈ first, time ∈ span.cover) ∧ (∃ span ∈ second, time ∈ span.cover)
  constructor
  · rintro ⟨span, listed, inside⟩
    obtain ⟨left, leftListed, overlapsListed⟩ := List.mem_flatMap.mp listed
    obtain ⟨right, rightListed, rfl⟩ := List.mem_map.mp overlapsListed
    rw [Span.overlap_cover] at inside
    exact ⟨⟨left, leftListed, inside.1⟩, right, rightListed, inside.2⟩
  · rintro ⟨⟨left, leftListed, leftInside⟩, right, rightListed, rightInside⟩
    refine ⟨left.overlap right, List.mem_flatMap.mpr
      ⟨left, leftListed, List.mem_map.mpr ⟨right, rightListed, rfl⟩⟩, ?_⟩
    rw [Span.overlap_cover]
    exact ⟨leftInside, rightInside⟩

theorem measurable_cover (spans : List Span) : MeasurableSet (cover spans) := by
  rw [cover_is_exactly_the_occupied_cells spans (endpoints spans) (fun _ listed => listed)]
  exact Finset.measurableSet_biUnion _ (fun _ _ => measurableSet_Ico)

/-- Shared personal intervals consume clock time once, with the precise
overlap retained in the accounting equality. -/
theorem length_union_add_overlap (first second : List Span) :
    length (first ++ second) + length (overlaps first second) = length first + length second := by
  have together := measure_union_add_inter (μ := volume) (cover first) (measurable_cover second)
  rw [← cover_append, ← cover_overlaps, volume_of_cover, volume_of_cover,
    volume_of_cover, volume_of_cover] at together
  have measured := congrArg ENNReal.toReal together
  simp only [ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (Rat.cast_nonneg.mpr (length_nonnegative _))] at measured
  exact_mod_cast measured

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.Intervals
