import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Runtime.CursorRead
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.ExecutedHistory
import Mathlib.Data.Nat.Find
import Mathlib.Order.Monotone.Basic

/-! Each current word has a finite original inventory.  Its size may vary
without bound across cycles; the existing cursor nevertheless processes
every later physical occurrence.  No new scheduler or future word is stored. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Runtime

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth : Nat)

theorem cursorAt_accounting (count : Nat) :
    (cursorAt input depth count).phase = .accounting := by
  cases count <;> rfl

theorem cursorAt_position_bounded (count : Nat) :
    (cursorAt input depth count).position ≤ Cursor.capacity input (cursorAt input depth count) := by
  induction count with
  | zero => exact Nat.zero_le _
  | succ count prior => exact Cursor.next_position_bounded input _ prior

theorem cursor_cycle_monotone : Monotone (fun count => (cursorAt input depth count).cycle) := by
  apply monotone_nat_of_le_succ
  intro count
  change (cursorAt input depth count).cycle ≤ (Cursor.next input (cursorAt input depth count)).cycle
  simp only [Cursor.next, cursorAt_accounting]
  split <;> omega

private theorem same_cycle_same_capacity (first second : Nat)
    (same : (cursorAt input depth first).cycle = (cursorAt input depth second).cycle) :
    Cursor.capacity input (cursorAt input depth first) = Cursor.capacity input (cursorAt input depth second) := by
  unfold Cursor.capacity Cursor.originalVisit
  rw [same]

private theorem position_on_unchanged_cycle (start offset : Nat)
    (same : (cursorAt input depth (start + offset)).cycle = (cursorAt input depth start).cycle) :
    (cursorAt input depth (start + offset)).position = (cursorAt input depth start).position + offset := by
  induction offset with
  | zero => simp
  | succ offset prior =>
      have between : (cursorAt input depth (start + offset)).cycle = (cursorAt input depth start).cycle := by
        have lower : (cursorAt input depth start).cycle ≤ (cursorAt input depth (start + offset)).cycle :=
          cursor_cycle_monotone input depth (show start ≤ start + offset by omega)
        have upper : (cursorAt input depth (start + offset)).cycle ≤
            (cursorAt input depth (start + (offset + 1))).cycle :=
          cursor_cycle_monotone input depth (show start + offset ≤ start + (offset + 1) by omega)
        omega
      have oldPosition := prior between
      have available : (cursorAt input depth (start + offset)).position <
          Cursor.capacity input (cursorAt input depth (start + offset)) := by
        by_contra exhausted
        have advanced : (cursorAt input depth (start + (offset + 1))).cycle =
            (cursorAt input depth (start + offset)).cycle + 1 := by
          change (Cursor.next input (cursorAt input depth (start + offset))).cycle = _
          simp only [Cursor.next, cursorAt_accounting, if_neg exhausted]
        omega
      have nextPosition : (cursorAt input depth (start + (offset + 1))).position =
          (cursorAt input depth (start + offset)).position + 1 := by
        change (Cursor.next input (cursorAt input depth (start + offset))).position = _
        simp only [Cursor.next, cursorAt_accounting, if_pos available]
      rw [nextPosition, oldPosition]
      omega

/-- The bound is the actual finite inventory at this cycle, not a uniform
cap on future words.  Even an ever longer sequence of words cannot stall it. -/
theorem current_cycle_finishes_within_its_inventory (start : Nat) :
    (cursorAt input depth start).cycle <
      (cursorAt input depth
        (start + (Cursor.capacity input (cursorAt input depth start) + 1))).cycle := by
  let finish := start + (Cursor.capacity input (cursorAt input depth start) + 1)
  have nondecreasing : (cursorAt input depth start).cycle ≤ (cursorAt input depth finish).cycle :=
    cursor_cycle_monotone input depth (show start ≤ finish by dsimp [finish]; omega)
  by_contra stopped
  change ¬ (cursorAt input depth start).cycle < (cursorAt input depth finish).cycle at stopped
  have same : (cursorAt input depth finish).cycle = (cursorAt input depth start).cycle := by omega
  have position := position_on_unchanged_cycle input depth start
    (Cursor.capacity input (cursorAt input depth start) + 1) same
  have bounded := cursorAt_position_bounded input depth finish
  rw [same_cycle_same_capacity input depth finish start same] at bounded
  change (cursorAt input depth finish).position = _ at position
  omega

theorem cursor_cycles_are_cofinal (cutoff level : Nat) :
    ∃ count ≥ cutoff, level ≤ (cursorAt input depth count).cycle := by
  induction level with
  | zero => exact ⟨cutoff, le_refl _, Nat.zero_le _⟩
  | succ level prior =>
      obtain ⟨count, after, reached⟩ := prior
      refine ⟨count + (Cursor.capacity input (cursorAt input depth count) + 1), by omega, ?_⟩
      have advanced := current_cycle_finishes_within_its_inventory input depth count
      omega

theorem canonical_physical_indices_are_cofinal (cutoff physical : Nat) :
    ∃ count ≥ cutoff, physical ≤ Cursor.physicalVisitIndex input (cursorAt input depth count) := by
  obtain ⟨count, after, reached⟩ := cursor_cycles_are_cofinal input depth cutoff physical
  refine ⟨count, after, ?_⟩
  unfold Cursor.physicalVisitIndex
  omega

theorem canonical_physical_indices_monotone :
    Monotone (fun count => Cursor.physicalVisitIndex input (cursorAt input depth count)) := by
  apply monotone_nat_of_le_succ
  intro count
  exact Cursor.physical_index_monotone input (cursorAt input depth count)

theorem physical_step_is_zero_or_one (count : Nat) :
    Cursor.physicalVisitIndex input (cursorAt input depth (count + 1)) =
        Cursor.physicalVisitIndex input (cursorAt input depth count) ∨
      Cursor.physicalVisitIndex input (cursorAt input depth (count + 1)) =
        Cursor.physicalVisitIndex input (cursorAt input depth count) + 1 := by
  by_cases fresh : Cursor.FreshBody input (cursorAt input depth count)
  · exact Or.inr (Cursor.fresh_physical_index input _ fresh)
  · exact Or.inl (Cursor.bookkeeping_physical_index input _ fresh)

/-- Cofinality is strengthened to an actual fresh tick at every subsequent
source index.  A bookkeeping repetition cannot witness this conclusion. -/
theorem every_later_physical_word_has_a_fresh_tick (index : Nat)
    (later : Cursor.physicalVisitIndex input (cursorAt input depth 0) ≤ index) :
    ∃ count,
      Cursor.physicalVisitIndex input (cursorAt input depth count) = index ∧
      Cursor.FreshBody input (cursorAt input depth count) := by
  classical
  have exceeds : ∃ count, index < Cursor.physicalVisitIndex input (cursorAt input depth count) := by
    obtain ⟨count, _after, reached⟩ := canonical_physical_indices_are_cofinal input depth 0 (index + 1)
    exact ⟨count, by omega⟩
  let first := Nat.find exceeds
  have above := Nat.find_spec exceeds
  have positive : 0 < first := by
    by_contra zero
    have same : first = 0 := by omega
    change index < Cursor.physicalVisitIndex input (cursorAt input depth first) at above
    rw [same] at above
    omega
  obtain ⟨count, selected⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
  have before : Cursor.physicalVisitIndex input (cursorAt input depth count) ≤ index := by
    exact Nat.le_of_not_gt (Nat.find_min exceeds (show count < Nat.find exceeds by
      change count < first
      omega))
  change index < Cursor.physicalVisitIndex input (cursorAt input depth first) at above
  rw [selected] at above
  change index < Cursor.physicalVisitIndex input (cursorAt input depth (count + 1)) at above
  have exactIndex : Cursor.physicalVisitIndex input (cursorAt input depth count) = index := by
    rcases physical_step_is_zero_or_one input depth count with same | advanced <;> omega
  refine ⟨count, exactIndex, ?_⟩
  by_contra old
  have unchanged := Cursor.bookkeeping_physical_index input (cursorAt input depth count) old
  change Cursor.physicalVisitIndex input (cursorAt input depth (count + 1)) =
    Cursor.physicalVisitIndex input (cursorAt input depth count) at unchanged
  omega

theorem frames_physical_indices_are_cofinal (cutoff physical : Nat) :
    ∃ count ≥ cutoff,
      physical ≤ Cursor.physicalVisitIndex input ((frames input depth count).cursor input) := by
  simpa only [frames_cursor] using canonical_physical_indices_are_cofinal input depth cutoff physical

theorem every_source_word_after_cutoff_has_a_fresh_tick (cutoff index : Nat)
    (later : Cursor.physicalVisitIndex input (cursorAt input depth cutoff) ≤ index) :
    ∃ count ≥ cutoff,
      Cursor.physicalVisitIndex input (cursorAt input depth count) = index ∧
      Cursor.FreshBody input (cursorAt input depth count) := by
  have initial := canonical_physical_indices_monotone input depth (Nat.zero_le cutoff)
  obtain ⟨count, exactIndex, fresh⟩ := every_later_physical_word_has_a_fresh_tick input depth index
    (initial.trans later)
  refine ⟨count, ?_, exactIndex, fresh⟩
  by_contra early
  have before : Cursor.physicalVisitIndex input (cursorAt input depth (count + 1)) ≤
      Cursor.physicalVisitIndex input (cursorAt input depth cutoff) :=
    canonical_physical_indices_monotone input depth (show count + 1 ≤ cutoff by omega)
  have advanced := Cursor.fresh_physical_index input (cursorAt input depth count) fresh
  change Cursor.physicalVisitIndex input (cursorAt input depth (count + 1)) =
    Cursor.physicalVisitIndex input (cursorAt input depth count) + 1 at advanced
  omega

/-- Every source-tail statement receives one shared runtime cutoff.  The
extra completed index prevents bookkeeping from rereading a pre-cut word. -/
theorem completed_history_has_common_tail_cut (sourceCut : Nat) :
    ∃ cutoff, ∀ count ≥ cutoff,
      sourceCut ≤ Cursor.lastExecutedIndex input (cursorAt input depth count) := by
  obtain ⟨cutoff, _after, reached⟩ := canonical_physical_indices_are_cofinal input depth 0 (sourceCut + 1)
  refine ⟨cutoff, ?_⟩
  intro count after
  have later : Cursor.physicalVisitIndex input (cursorAt input depth cutoff) ≤
      Cursor.physicalVisitIndex input (cursorAt input depth count) :=
    canonical_physical_indices_monotone input depth after
  have next := Cursor.physical_index_monotone input (cursorAt input depth count)
  unfold Cursor.lastExecutedIndex
  omega

theorem every_later_physical_word_occurs_on_original_frame (index : Nat)
    (later : Cursor.physicalVisitIndex input ((frames input depth 0).cursor input) ≤ index) :
    ∃ count,
      Cursor.physicalVisitIndex input ((frames input depth count).cursor input) = index ∧
      Cursor.currentExecutedBody? input ((frames input depth count).cursor input) =
        some (ProgrammeHistory.visitAt input index) := by
  rw [frames_cursor] at later
  obtain ⟨count, exactIndex, fresh⟩ := every_later_physical_word_has_a_fresh_tick input depth index later
  refine ⟨count, ?_, ?_⟩
  · simpa only [frames_cursor] using exactIndex
  · rw [frames_cursor, (Cursor.fresh_reads_this_actual_body input _ fresh).1]
    exact congrArg some (congrArg (ProgrammeHistory.visitAt input) exactIndex)

#print axioms canonical_physical_indices_are_cofinal
#print axioms every_later_physical_word_occurs_on_original_frame
#print axioms completed_history_has_common_tail_cut

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Runtime
