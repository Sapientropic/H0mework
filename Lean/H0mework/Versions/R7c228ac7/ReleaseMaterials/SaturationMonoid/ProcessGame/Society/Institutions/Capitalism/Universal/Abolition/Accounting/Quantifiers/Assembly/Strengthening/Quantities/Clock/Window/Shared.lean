import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Window.Dual
import Mathlib.Data.Finset.Sigma

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Window.Shared

open Source.Program Abolition.Root Abolition.Root.Registered PublicFunction
open _root_.SaturationMonoid.ProcessGame.Society.UBI.Capacity

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {TaskId : Type*}

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))
local notation "Task" => PublicTaskSpec Party Good

/-- The left addresses retain their original task and slot. All the
windows share the one set of actual committing debit ordinals. -/
def geometry (source : C) (ids : Finset TaskId) (task : TaskId → Task) (script : Script) :
    CanonicalBipartiteFeasibility (Σ id, Fin (task id).slots.length)
      (Fin (Execution.inventory source script).length) where
  leftCarrier := ids.sigma fun id => (Window.geometry source (task id) script).leftCarrier
  rightCarrier := Finset.univ
  Feasible := fun slot item => (Window.geometry source (task slot.1) script).Feasible slot.2 item
  feasibleDecidable := fun slot item => (Window.geometry source (task slot.1) script).feasibleDecidable slot.2 item

theorem an_edge_is_an_original_task_and_its_own_timed_service
    (source : C) (ids : Finset TaskId) (task : TaskId → Task) (script : Script)
    (slot : Σ id, Fin (task id).slots.length) (item : Fin (Execution.inventory source script).length) :
    (slot, item) ∈ (geometry source ids task script).edgeCarrier ↔
      slot.1 ∈ ids ∧ (slot.2, item) ∈ (Window.geometry source (task slot.1) script).edgeCarrier := by
  rw [(geometry source ids task script).mem_edgeCarrier_iff,
    (Window.geometry source (task slot.1) script).mem_edgeCarrier_iff]
  have right : item ∈ (Window.geometry source (task slot.1) script).rightCarrier :=
    Finset.mem_univ _
  simp only [geometry, Finset.mem_sigma, Finset.mem_univ, right, true_and]
  change (slot.1 ∈ ids ∧ slot.2 ∈ (Window.geometry source (task slot.1) script).leftCarrier) ∧ _ ↔
    slot.1 ∈ ids ∧ slot.2 ∈ (Window.geometry source (task slot.1) script).leftCarrier ∧ _
  exact and_assoc

abbrev Assigned (source : C) (ids : Finset TaskId) (task : TaskId → Task) (script : Script) : Prop :=
  ∃ matching : Finset ((Σ id, Fin (task id).slots.length) × Fin (Execution.inventory source script).length),
    matching ∈ (geometry source ids task script).matchings ∧
    matching.card = (geometry source ids task script).leftCarrier.card

/-- The original task family has an allocation iff every group of original
slots has enough compatible receipts. No debit can be counted in two tasks. -/
theorem joint_payment_iff_all_original_task_groups_have_enough_capacity
    (source : C) (ids : Finset TaskId) (task : TaskId → Task) (script : Script) :
    Assigned source ids task script ↔
      ∀ group ⊆ (geometry source ids task script).leftCarrier,
        group.card ≤ (neighbours (geometry source ids task script) group).card :=
  (full_capacity_iff_there_is_a_complete_matching _).symm.trans
    (full_payment_iff_every_original_group_has_enough_neighbours _)

structure Deficiency (source : C) (ids : Finset TaskId) (task : TaskId → Task) (script : Script) where
  group : Finset (Σ id, Fin (task id).slots.length)
  original : group ⊆ (geometry source ids task script).leftCarrier
  short : (neighbours (geometry source ids task script) group).card < group.card
  exactAmount : (geometry source ids task script).maximumMatchingCapacity +
    deficit (geometry source ids task script) group = (geometry source ids task script).leftCarrier.card

theorem Deficiency.refutes {source : C} {ids : Finset TaskId} {task : TaskId → Task} {script : Script}
    (missing : Deficiency source ids task script) :
    ¬ Assigned source ids task script :=
  fun paid => (not_le_of_gt missing.short)
    ((joint_payment_iff_all_original_task_groups_have_enough_capacity _ _ _ _).mp paid missing.group missing.original)

def inspect (source : C) (ids : Finset TaskId) (task : TaskId → Task) (script : Script) :
    Option (Deficiency source ids task script) := by
  classical
  let actual := geometry source ids task script
  if short : actual.maximumMatchingCapacity < actual.leftCarrier.card then
    let largest := the_largest_deficit_is_attained_at_an_original_group actual
    let group := Classical.choose largest
    have witness := Classical.choose_spec largest
    have exactAmount := actual_capacity_plus_the_largest_original_deficit_is_the_full_need actual
    rw [← witness.2] at exactAmount
    have amount : actual.maximumMatchingCapacity + deficit actual group = actual.leftCarrier.card := exactAmount
    have positive : 0 < deficit actual group := by omega
    exact some ⟨group, witness.1, Nat.sub_pos_iff_lt.mp positive, amount⟩
  else
    exact none

theorem inspect_clears_exactly_the_jointly_payable_task_family
    (source : C) (ids : Finset TaskId) (task : TaskId → Task) (script : Script) :
    inspect source ids task script = none ↔ Assigned source ids task script := by
  classical
  unfold inspect
  dsimp only
  split
  · rename_i short
    simp only [reduceCtorEq, false_iff]
    intro paid
    exact short.ne ((full_capacity_iff_there_is_a_complete_matching _).mpr paid)
  · rename_i noShort
    simp only [iff_true_left]
    exact (full_capacity_iff_there_is_a_complete_matching _).mp
      (le_antisymm (geometry source ids task script).maximumMatchingCapacity_le_left (le_of_not_gt noShort))

/-- The shared test keeps each candidate on the original root, including the
whole ledger and the actual continuation when a group is short. -/
theorem actual_joint_service_has_a_paid_matching_or_an_exact_original_group
    (source : C) (ids : Finset TaskId) (task : TaskId → Task) (script : Script) :
    Recorded source script ∧
      (Assigned source ids task script ∨ Nonempty (Deficiency source ids task script)) := by
  refine ⟨record source script, ?_⟩
  cases found : inspect source ids task script with
  | none => exact .inl ((inspect_clears_exactly_the_jointly_payable_task_family _ _ _ _).mp found)
  | some issue => exact .inr ⟨issue⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Window.Shared
