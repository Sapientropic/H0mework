import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Mixed
import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Mixed.Assignments

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Mixed

open Source.Program Abolition.Root Abolition.Root.Registered PublicFunction
open _root_.SaturationMonoid.ProcessGame.Society.UBI.Capacity

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {TaskId : Type*} [DecidableEq TaskId]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))
local notation "Task" => PublicTaskSpec Party Good

abbrev WholeSlot (task : TaskId → Task) := Σ id, Fin (task id).slots.length

def atomicSlots (source : C) (script : Script) (atomic : Finset TaskId) (task : TaskId → Task)
    (ordered : List TaskId) (same : ordered.toFinset = atomic) : List (WholeSlot task) :=
  (((slotList atomic task ordered same).filter fun slot =>
    decide (slot.2 ∈ (Clock.Window.geometry source (task slot.1.val) script).leftCarrier)).map
    fun slot => (⟨slot.1.val, slot.2⟩ : WholeSlot task)).dedup

theorem atomicSlots_are_the_original_nonempty_slots (source : C) (script : Script) (atomic : Finset TaskId)
    (task : TaskId → Task) (ordered : List TaskId) (same : ordered.toFinset = atomic) :
    (atomicSlots source script atomic task ordered same).toFinset =
      (Clock.Window.Shared.geometry source atomic task script).leftCarrier := by
  ext slot
  rw [List.mem_toFinset]
  unfold atomicSlots
  rw [List.mem_dedup]
  change _ ↔ slot ∈ atomic.sigma (fun id => (Clock.Window.geometry source (task id) script).leftCarrier)
  rw [Finset.mem_sigma]
  constructor
  · intro found
    obtain ⟨original, listed, rfl⟩ := List.mem_map.mp found
    exact ⟨original.1.property, of_decide_eq_true (List.mem_filter.mp listed).2⟩
  · intro present
    let original : Slot atomic task := ⟨⟨slot.1, present.1⟩, slot.2⟩
    refine List.mem_map.mpr ⟨original, List.mem_filter.mpr ⟨slotList_covers _ _ _ same original, ?_⟩, rfl⟩
    exact decide_eq_true present.2

private def candidates (source : C) (script : Script) (atomic : Finset TaskId) (task : TaskId → Task)
    (ordered : List TaskId) (same : ordered.toFinset = atomic) :
    List (Finset (WholeSlot task × Ordinal source script)) :=
  assignments (eligibility (Clock.Window.Shared.geometry source atomic task script))
    (atomicSlots source script atomic task ordered same) (List.finRange (Execution.inventory source script).length)

private theorem exact_candidates (source : C) (script : Script) (atomic : Finset TaskId) (task : TaskId → Task)
    (ordered : List TaskId) (same : ordered.toFinset = atomic)
    (matching : Finset (WholeSlot task × Ordinal source script)) :
    matching ∈ candidates source script atomic task ordered same ↔
      matching ∈ (Clock.Window.Shared.geometry source atomic task script).matchings ∧
      matching.card = (Clock.Window.Shared.geometry source atomic task script).leftCarrier.card := by
  let geom := Clock.Window.Shared.geometry source atomic task script
  let slots := atomicSlots source script atomic task ordered same
  let items := List.finRange (Execution.inventory source script).length
  have right : items.toFinset = geom.rightCarrier := by
    ext item
    change item ∈ (List.finRange (Execution.inventory source script).length).toFinset ↔ item ∈ Finset.univ
    simp
  have distinct : slots.Nodup := List.nodup_dedup _
  exact (assignments_are_exact (eligibility geom) slots items distinct matching).trans
    (original_and_full_iff_assignment geom slots items (atomicSlots_are_the_original_nonempty_slots _ _ _ _ _ _) right matching).symm

def wholeChoices (source : C) (script : Script) (atomic : Finset TaskId) (task : TaskId → Task)
    (ordered : List TaskId) (same : ordered.toFinset = atomic) : List (WholeChoice source script atomic task) :=
  (candidates source script atomic task ordered same).attach.map fun candidate =>
    let original := (exact_candidates source script atomic task ordered same candidate.val).mp candidate.property
    ⟨candidate.val, original.1, original.2⟩

theorem wholeChoices_contains_every_original_assignment (source : C) (script : Script)
    (atomic : Finset TaskId) (task : TaskId → Task) (ordered : List TaskId) (same : ordered.toFinset = atomic)
    (choice : WholeChoice source script atomic task) : choice ∈ wholeChoices source script atomic task ordered same := by
  let entry : { candidate // candidate ∈ candidates source script atomic task ordered same } :=
    ⟨choice.matching, (exact_candidates _ _ _ _ _ _ _).mpr ⟨choice.original, choice.full⟩⟩
  exact List.mem_map.mpr ⟨entry, List.mem_attach _ _, by cases choice; rfl⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Mixed
