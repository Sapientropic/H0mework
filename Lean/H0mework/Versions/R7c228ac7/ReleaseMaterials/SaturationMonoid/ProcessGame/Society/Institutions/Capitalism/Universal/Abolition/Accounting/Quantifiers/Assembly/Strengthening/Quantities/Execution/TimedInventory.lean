import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Root.Settlement

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution

open Source.Program Abolition.Root Abolition.Root.Registered

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))
local notation "Item" => ExecutionItem Party Good Port Technology Instrument

/-- Completion time is read at the actual committing query. Every original
material item keeps its ordinal, including items of one atomic period. -/
def timedInventory : C → Script → List (Item × ℚ)
  | _, [] => []
  | source, proposal :: rest =>
    let target := next source proposal
    ((Optimality.Programme.Epoch.materialItems (query source proposal)).map fun item =>
      (item, target.raw.clock)) ++ timedInventory target rest

theorem timedInventory_is_the_original_inventory (source : C) (script : Script) :
    (timedInventory source script).map Prod.fst = inventory source script := by
  induction script generalizing source with
  | nil => rfl
  | cons proposal tail previous =>
    simp only [timedInventory, inventory, List.map_append, List.map_map, Function.comp_def, previous]
    change (Optimality.Programme.Epoch.materialItems (query source proposal)).map id ++ _ = _
    rw [List.map_id]

theorem timedInventory_append (source : C) (first second : Script) :
    timedInventory source (first ++ second) =
      timedInventory source first ++ timedInventory (endAt source first) second := by
  induction first generalizing source with
  | nil => rfl
  | cons proposal tail previous =>
    simp only [List.cons_append, timedInventory, endAt, previous, List.append_assoc]

def timedAt (source : C) (script : Script) (ordinal : Fin (inventory source script).length) : Item × ℚ :=
  (timedInventory source script).get ⟨ordinal.val, by
    rw [← List.length_map Prod.fst, timedInventory_is_the_original_inventory]
    exact ordinal.isLt⟩

theorem timedAt_is_the_same_original_item (source : C) (script : Script)
    (ordinal : Fin (inventory source script).length) :
    (timedAt source script ordinal).1 = (inventory source script).get ordinal := by
  have actual := congrArg (fun items : List Item => items[ordinal.val]?)
    (timedInventory_is_the_original_inventory source script)
  let inside : Fin (timedInventory source script).length := ⟨ordinal.val, by
    rw [← List.length_map Prod.fst, timedInventory_is_the_original_inventory]
    exact ordinal.isLt⟩
  have bounded : ordinal.val < (timedInventory source script).length := inside.isLt
  rw [List.getElem?_map, List.getElem?_eq_getElem bounded, List.getElem?_eq_getElem ordinal.isLt] at actual
  exact Option.some.inj actual

theorem the_actual_script_never_runs_the_clock_backwards (source : C) (script : Script) :
    source.raw.clock ≤ (endAt source script).raw.clock := by
  have time := Optimality.Programme.programme_clock_never_runs_backwards source.native.input
    (Evolving.Epoch.Source.originalState source.native) (programme source script)
  rw [physical_is_the_folded_actual_end] at time
  exact time

theorem every_original_service_commits_between_source_and_terminal_clock (source : C) (script : Script) :
    ∀ receipt ∈ timedInventory source script,
      source.raw.clock ≤ receipt.2 ∧ receipt.2 ≤ (endAt source script).raw.clock := by
  induction script generalizing source with
  | nil => simp [timedInventory]
  | cons proposal tail previous =>
    intro receipt original
    let target := next source proposal
    have grows : source.raw.clock ≤ target.raw.clock :=
      the_actual_script_never_runs_the_clock_backwards source [proposal]
    rcases List.mem_append.mp original with first | later
    · obtain ⟨item, _, rfl⟩ := List.mem_map.mp first
      exact ⟨grows, the_actual_script_never_runs_the_clock_backwards target tail⟩
    · obtain ⟨lower, upper⟩ := previous target receipt later
      exact ⟨grows.trans lower, upper⟩

theorem an_ordinal_uses_its_actual_committing_clock (source : C) (script : Script)
    (ordinal : Fin (inventory source script).length) :
    source.raw.clock ≤ (timedAt source script ordinal).2 ∧
      (timedAt source script ordinal).2 ≤ (endAt source script).raw.clock :=
  every_original_service_commits_between_source_and_terminal_clock source script _ (List.get_mem _ _)

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution
