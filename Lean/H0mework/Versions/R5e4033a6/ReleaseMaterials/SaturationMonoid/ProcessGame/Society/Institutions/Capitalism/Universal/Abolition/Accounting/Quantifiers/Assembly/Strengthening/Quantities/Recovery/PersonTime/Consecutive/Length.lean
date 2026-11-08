import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.Consecutive.Cells

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.Consecutive

open Intervals

private theorem extends_to_original_endpoints (spans : List Span) (trial : Span)
    (positive : trial.start < trial.finish) (inside : trial.cover ⊆ cover spans) :
    ∃ first ∈ endpoints spans, ∃ last ∈ endpoints spans,
      first ≤ trial.start ∧ trial.finish ≤ last ∧ Set.Ico (first : ℝ) (last : ℝ) ⊆ cover spans := by
  have begin : (trial.start : ℝ) ∈ trial.cover := ⟨le_rfl, Rat.cast_lt.mpr positive⟩
  obtain ⟨initial, initialListed, initialOpens, initialCloses⟩ := inside begin
  have starts : initial.start ≤ trial.start := Rat.cast_le.mp initialOpens
  let earlier := (endpoints spans).filter fun point => point < trial.finish
  have earlierNonempty : earlier.Nonempty :=
    ⟨initial.start, Finset.mem_filter.mpr ⟨start_mem_endpoints initialListed, starts.trans_lt positive⟩⟩
  let lastEarlier := earlier.max' earlierNonempty
  have earlier_lt : lastEarlier < trial.finish :=
    (Finset.mem_filter.mp (Finset.max'_mem earlier earlierNonempty)).2
  let probe := max trial.start lastEarlier
  have probe_lt : probe < trial.finish := max_lt positive earlier_lt
  have probeInside : (probe : ℝ) ∈ trial.cover :=
    ⟨Rat.cast_le.mpr (le_max_left _ _), Rat.cast_lt.mpr probe_lt⟩
  obtain ⟨terminal, terminalListed, terminalOpens, terminalCloses⟩ := inside probeInside
  have lasts : trial.finish ≤ terminal.finish := by
    by_contra! early
    have listed : terminal.finish ∈ earlier :=
      Finset.mem_filter.mpr ⟨finish_mem_endpoints terminalListed, early⟩
    have bounded := (Finset.le_max' earlier terminal.finish listed).trans (le_max_right trial.start lastEarlier)
    exact (not_lt_of_ge bounded) (Rat.cast_lt.mp terminalCloses)
  refine ⟨initial.start, start_mem_endpoints initialListed, terminal.finish, finish_mem_endpoints terminalListed,
    starts, lasts, ?_⟩
  intro time bounds
  by_cases beforeStart : time < (trial.start : ℝ)
  · exact ⟨initial, initialListed, bounds.1, beforeStart.trans initialCloses⟩
  by_cases beforeFinish : time < (trial.finish : ℝ)
  · exact inside ⟨le_of_not_gt beforeStart, beforeFinish⟩
  · exact ⟨terminal, terminalListed,
      terminalOpens.trans ((Rat.cast_lt.mpr probe_lt).le.trans (le_of_not_gt beforeFinish)), bounds.2⟩

theorem every_continuously_occupied_interval_is_bounded
    (spans : List Span) (trial : Span) (inside : trial.cover ⊆ cover spans) :
    trial.finish - trial.start ≤ longest spans := by
  by_cases positive : trial.start < trial.finish
  · obtain ⟨first, firstMem, last, lastMem, starts, lasts, continuous⟩ :=
      extends_to_original_endpoints spans trial positive inside
    have ordered := starts.trans (trial.ordered.trans lasts)
    have valid := (all_original_cells_occupied_iff spans firstMem lastMem).mpr continuous
    have width : last - first ∈ widths spans :=
      Finset.mem_insert_of_mem (Finset.mem_image.mpr
        ⟨(first, last), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨firstMem, lastMem⟩, ordered, valid⟩, rfl⟩)
    exact (sub_le_sub lasts starts).trans (Finset.le_max' _ _ width)
  · exact (sub_nonpos.mpr (le_of_not_gt positive)).trans (longest_nonnegative spans)

theorem positive_longest_is_attained_between_original_endpoints
    (spans : List Span) (positive : 0 < longest spans) :
    ∃ run : Span, run.start ∈ endpoints spans ∧ run.finish ∈ endpoints spans ∧
      run.cover ⊆ cover spans ∧ run.finish - run.start = longest spans := by
  have attained : longest spans ∈ widths spans := Finset.max'_mem _ _
  rcases Finset.mem_insert.mp attained with zero | actual
  · exact (positive.ne' zero).elim
  · obtain ⟨⟨first, last⟩, included, width⟩ := Finset.mem_image.mp actual
    obtain ⟨original, ordered, occupied⟩ := Finset.mem_filter.mp included
    obtain ⟨firstMem, lastMem⟩ := Finset.mem_product.mp original
    exact ⟨⟨first, last, ordered⟩, firstMem, lastMem,
      (all_original_cells_occupied_iff spans firstMem lastMem).mp occupied, width⟩

theorem same_occupied_times_have_the_same_longest_run {first second : List Span}
    (same : cover first = cover second) : longest first = longest second := by
  have preserves : ∀ {left right : List Span}, cover left = cover right → longest left ≤ longest right := by
    intro left right covers
    by_cases positive : 0 < longest left
    · obtain ⟨run, _, _, occupied, exactWidth⟩ :=
        positive_longest_is_attained_between_original_endpoints left positive
      rw [← exactWidth]
      exact every_continuously_occupied_interval_is_bounded right run (covers ▸ occupied)
    · exact (le_of_not_gt positive).trans (longest_nonnegative right)
  exact le_antisymm (preserves same) (preserves same.symm)

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.Consecutive
