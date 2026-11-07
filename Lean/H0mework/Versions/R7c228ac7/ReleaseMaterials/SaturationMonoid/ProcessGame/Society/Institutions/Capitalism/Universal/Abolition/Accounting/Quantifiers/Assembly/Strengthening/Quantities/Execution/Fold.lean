import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.Step

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution

open Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))

def endAt : C → Script → C
  | source, [] => source
  | source, proposal :: rest => endAt (next source proposal) rest

/-- The original queries consumed at each cut, including native work,
lawful presentation and refusal. -/
def queries : C → Script → List C
  | _, [] => []
  | source, proposal :: rest => query source proposal :: queries (next source proposal) rest

def programme : C → Script → List (Compile.RawInput Party Good Port Technology Instrument)
  | _, [] => []
  | source, proposal :: rest =>
      Optimality.Programme.Epoch.effective (query source proposal) ++ programme (next source proposal) rest

def inventory : C → Script → List (ExecutionItem Party Good Port Technology Instrument)
  | _, [] => []
  | source, proposal :: rest =>
      Optimality.Programme.Epoch.materialItems (query source proposal) ++ inventory (next source proposal) rest

theorem every_query_has_its_original_root_write (source : C) (script : Script) :
    ∀ cut ∈ queries source script, Evolving.Epoch.Current.ClosedAt cut := by
  induction script generalizing source with
  | nil => simp [queries]
  | cons proposal tail ih =>
      intro cut member
      rcases List.mem_cons.mp member with first | later
      · subst cut
        exact actual_step source proposal
      · exact ih (next source proposal) cut later

theorem endAt_input (source : C) (script : Script) :
    (endAt source script).native.input = source.native.input := by
  induction script generalizing source with
  | nil => rfl
  | cons proposal tail ih => exact (ih (next source proposal)).trans (next_input source proposal)

theorem physical_is_the_folded_actual_end (source : C) (script : Script) :
    Optimality.Programme.run source.native.input (Evolving.Epoch.Source.originalState source.native)
      (programme source script) =
    Evolving.Epoch.Source.originalState (endAt source script).native := by
  induction script generalizing source with
  | nil => rfl
  | cons proposal tail ih =>
      rw [programme, Optimality.Programme.run_append, effective_step, ← next_input source proposal]
      exact ih (next source proposal)

theorem material_is_the_folded_actual_inventory (source : C) (script : Script) :
    Optimality.Programme.items source.native.input (Evolving.Epoch.Source.originalState source.native)
      (programme source script) = inventory source script := by
  induction script generalizing source with
  | nil => rfl
  | cons proposal tail ih =>
      rw [programme, Optimality.Programme.items_append, effective_step,
        effective_inventory, ← next_input source proposal, ih, inventory]

theorem endAt_append (source : C) (first second : Script) :
    endAt source (first ++ second) = endAt (endAt source first) second := by
  induction first generalizing source with
  | nil => rfl
  | cons proposal tail ih => exact ih (next source proposal)

theorem inventory_append (source : C) (first second : Script) :
    inventory source (first ++ second) =
      inventory source first ++ inventory (endAt source first) second := by
  induction first generalizing source with
  | nil => rfl
  | cons proposal tail ih =>
    simp only [List.cons_append, inventory, endAt, ih, List.append_assoc]

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution
