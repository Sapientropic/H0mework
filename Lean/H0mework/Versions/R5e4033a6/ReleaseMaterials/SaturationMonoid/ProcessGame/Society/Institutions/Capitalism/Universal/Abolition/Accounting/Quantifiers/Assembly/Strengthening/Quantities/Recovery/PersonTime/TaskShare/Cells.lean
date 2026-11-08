import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.Intervals.Measure
import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Capacity.QuantityFlow.Profiles

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.TaskShare

open Intervals
open SaturationMonoid.ProcessGame.Society.Capacity.QuantityFlow
open scoped BigOperators

variable {Task : Type*} [DecidableEq Task]

abbrev Log (Task : Type*) := List (Task × Span)

def allSpans (log : Log Task) : List Span := log.map Prod.snd

def taskSpans (log : Log Task) (task : Task) : List Span :=
  (log.filter fun entry => decide (entry.1 = task)).map Prod.snd

abbrev points (log : Log Task) := endpoints (allSpans log)
abbrev activeCells (log : Log Task) := active (points log) (allSpans log)
abbrev Cell (log : Log Task) := {left : ℚ // left ∈ activeCells log}

def width (log : Log Task) (cell : Cell log) : ℚ := following (points log) cell.val - cell.val

omit [DecidableEq Task] in
theorem width_nonnegative (log : Log Task) (cell : Cell log) : 0 ≤ width log cell :=
  sub_nonneg.mpr (following_ge _ _)

def allows (log : Log Task) (task : Task) (cell : Cell log) : Bool :=
  present (taskSpans log task) cell.val

private theorem task_span_is_personal {log : Log Task} {task : Task} {span : Span}
    (inside : span ∈ taskSpans log task) : span ∈ allSpans log := by
  obtain ⟨entry, selected, rfl⟩ := List.mem_map.mp inside
  exact List.mem_map.mpr ⟨entry, (List.mem_filter.mp selected).1, rfl⟩

theorem some_original_task_occupies_each_cell (log : Log Task) (cell : Cell log) :
    ∃ task, allows log task cell = true := by
  obtain ⟨span, listed, covered⟩ := (present_iff (allSpans log) cell.val).mp
    (Finset.mem_filter.mp cell.property).2
  obtain ⟨entry, recorded, rfl⟩ := List.mem_map.mp listed
  exact ⟨entry.1, (present_iff _ _).mpr
    ⟨entry.2, List.mem_map.mpr ⟨entry, List.mem_filter.mpr ⟨recorded, by simp⟩, rfl⟩, covered⟩⟩

def full (log : Log Task) (task : Task) : ℚ :=
  ∑ cell : Cell log, if allows log task cell then width log cell else 0

omit [DecidableEq Task] in
theorem all_cell_widths_equal_the_personal_union (log : Log Task) :
    (∑ cell : Cell log, width log cell) = length (allSpans log) := by
  exact (Finset.sum_subtype (activeCells log) (fun _ => Iff.rfl)
    (fun left => following (points log) left - left)).symm

theorem full_is_the_tasks_own_occupied_union (log : Log Task) (task : Task) :
    full log task = length (taskSpans log task) := by
  let reading := fun left => if present (taskSpans log task) left then following (points log) left - left else 0
  have sumCells : full log task = ∑ left ∈ activeCells log, reading left :=
    (Finset.sum_subtype (activeCells log) (fun _ => Iff.rfl) reading).symm
  have activeTask : (activeCells log).filter (fun left => present (taskSpans log task) left = true) =
      active (points log) (taskSpans log task) := by
    ext left
    simp only [active, Finset.mem_filter, and_assoc, and_congr_right_iff]
    intro endpoint
    constructor
    · exact And.right
    · intro occupied
      obtain ⟨span, listed, within⟩ := (present_iff _ _).mp occupied
      exact ⟨(present_iff _ _).mpr ⟨span, task_span_is_personal listed, within⟩, occupied⟩
  have refined : endpoints (taskSpans log task) ⊆ points log := by
    intro point belongs
    obtain ⟨span, listed, endAt⟩ := List.mem_flatMap.mp (List.mem_toFinset.mp belongs)
    exact List.mem_toFinset.mpr (List.mem_flatMap.mpr ⟨span, task_span_is_personal listed, endAt⟩)
  rw [sumCells, ← length_is_independent_of_additional_endpoints _ _ refined]
  unfold lengthOn
  rw [← activeTask, Finset.sum_filter]

def network (log : Log Task) : Network Task (Cell log) where
  need := full log
  capacity := width log
  allows := allows log
  need_nonnegative := fun task => by
    rw [full_is_the_tasks_own_occupied_union]
    exact length_nonnegative _
  capacity_nonnegative := width_nonnegative log

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.TaskShare
