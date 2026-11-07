import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Service
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.TimedInventory

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Window

open Source.Program Abolition.Root Abolition.Root.Registered PublicFunction
open _root_.SaturationMonoid.ProcessGame.Society.UBI.Capacity

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))

/-- The observed service begins in its original window and must commit
before its installed deadline. The clock is attached to the same ordinal. -/
def geometry (source : C) (task : PublicTaskSpec Party Good) (script : Script) :
    CanonicalBipartiteFeasibility (Fin task.slots.length) (Fin (Execution.inventory source script).length) :=
  qualifiedGeometry (Clock.geometry source task script)
    (fun _ ordinal => (Execution.timedAt source script ordinal).2 ≤ task.deadline)
    (fun _ _ => inferInstance)

def FullyServed (source : C) (task : PublicTaskSpec Party Good) (script : Script) : Prop :=
  let actual := geometry source task script
  ∃ matching ∈ actual.matchings, matching.card = actual.leftCarrier.card

structure Shortage (source : C) (task : PublicTaskSpec Party Good) (script : Script) : Type where
  short : (geometry source task script).maximumMatchingCapacity < (geometry source task script).leftCarrier.card

theorem Shortage.refutes {source : C} {task : PublicTaskSpec Party Good} {script : Script}
    (issue : Shortage source task script) : ¬ FullyServed source task script :=
  fun paid => issue.short.ne ((full_capacity_iff_there_is_a_complete_matching _).mpr paid)

theorem Shortage.unpaid_original_slot {source : C} {task : PublicTaskSpec Party Good} {script : Script}
    (issue : Shortage source task script)
    (matching : Finset (Fin task.slots.length × Fin (Execution.inventory source script).length))
    (listed : matching ∈ (geometry source task script).matchings) :
    ∃ slot ∈ (geometry source task script).leftCarrier, ∀ edge ∈ matching, edge.1 ≠ slot :=
  a_short_matching_leaves_an_original_slot _ issue.short matching listed

def inspect (source : C) (task : PublicTaskSpec Party Good) (script : Script) : Option (Shortage source task script) :=
  if short : (geometry source task script).maximumMatchingCapacity < (geometry source task script).leftCarrier.card
  then some ⟨short⟩ else none

theorem passes_iff_every_original_service_commits_in_time
    (source : C) (task : PublicTaskSpec Party Good) (script : Script) :
    inspect source task script = none ↔ FullyServed source task script := by
  unfold inspect
  split
  · rename_i short
    simp only [reduceCtorEq, false_iff]
    exact (Shortage.mk short).refutes
  · rename_i full
    exact ⟨fun _ => (full_capacity_iff_there_is_a_complete_matching _).mp
      (le_antisymm (geometry source task script).maximumMatchingCapacity_le_left (le_of_not_gt full)),
      fun _ => rfl⟩

theorem a_fully_paid_script_ending_in_time_serves_every_original_window
    (source : C) (task : PublicTaskSpec Party Good) (script : Script)
    (paid : Clock.FullyServed source task script) (timely : (Execution.endAt source script).raw.clock ≤ task.deadline) :
    FullyServed source task script := by
  obtain ⟨matching, original, full⟩ := paid
  refine ⟨matching, each_existing_matching_is_retained_when_its_original_edges_pass _ _ _ _ original ?_, full⟩
  intro edge _
  exact (Execution.an_ordinal_uses_its_actual_committing_clock source script edge.2).2.trans timely

def material_committed_after_the_deadline_leaves_the_original_service_unpaid
    (source : C) (task : PublicTaskSpec Party Good) (script : Script)
    (late : ∀ ordinal, task.deadline < (Execution.timedAt source script ordinal).2) :
    Shortage source task script := by
  classical
  refine ⟨?_⟩
  let actual := geometry source task script
  have empty : actual.edgeCarrier = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro edge present
    have timely : (Execution.timedAt source script edge.2).2 ≤ task.deadline :=
      ((actual.mem_edgeCarrier_iff edge).mp present).2.2.2
    exact (not_le_of_gt (late edge.2)) timely
  obtain ⟨service, expected, lot, used, _⟩ := task.demand
  obtain ⟨slot, exactSlot⟩ := List.mem_iff_get.mp expected
  have original : slot ∈ actual.leftCarrier := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, exactSlot.symm ▸ List.ne_nil_of_mem used⟩
  exact (actual.edgeCarrier_empty_generates_zero_capacity empty).symm ▸
    Finset.card_pos.mpr ⟨slot, original⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Window
