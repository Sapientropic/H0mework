import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Programme.Epoch.Step

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Programme.Epoch
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro Evolution
noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (source : Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

/-- A readout of the already generated finite source history. Neither its
future proposals nor its effective syntax is supplied by the caller. -/
def programme : Nat → Submission (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)
  | 0 => []
  | n+1 => programme n ++ effective (Evolving.Epoch.History.currentAt source n)

def inventory : Nat → List (ExecutionItem Party Good Port Technology Instrument)
  | 0 => []
  | n+1 => inventory n ++ materialItems (Evolving.Epoch.History.currentAt source n)

/-- The full original node keeps its actual control face, native account,
root authority and whole-ledger write. This is a finite observed past. -/
def observations (n : Nat) := (List.range (n+1)).map (Evolving.Epoch.History.currentAt source)

def nativeAccountAt (n : Nat) := (Evolving.Epoch.History.currentAt source n).native.actual.actual.account

theorem the_compiled_history_is_the_literal_actual_epoch_physical_current (n : Nat) :
    run source.native.input (Evolving.Epoch.Source.originalState source.native) (programme source n) =
      Evolving.Epoch.Source.originalState (Evolving.Epoch.History.currentAt source n).native := by
  induction n with
  | zero => rfl
  | succ n prior =>
      rw [programme,run_append,prior]
      rw [← (Evolving.Epoch.History.parameters source n).1]
      exact the_effective_step_is_the_literal_actual_physical_successor _

theorem the_compiled_history_is_the_same_actual_report_inventory (n : Nat) :
    items source.native.input (Evolving.Epoch.Source.originalState source.native) (programme source n) = inventory source n := by
  induction n with
  | zero => rfl
  | succ n prior =>
      rw [programme,items_append,the_compiled_history_is_the_literal_actual_epoch_physical_current,prior,inventory]
      rw [← (Evolving.Epoch.History.parameters source n).1,the_effective_step_has_exactly_the_reported_material_inventory]

theorem every_observed_node_is_the_original_root_and_complete_account (n : Nat)
    (node : Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument)) (listed : node ∈ observations source n) :
    ∃ index ≤ n, node = Evolving.Epoch.History.currentAt source index ∧
      Evolving.Epoch.Current.ClosedAt node := by
  obtain ⟨index,inside,same⟩ := List.mem_map.mp listed
  refine ⟨index,Nat.le_of_lt_succ (List.mem_range.mp inside),same.symm,?_⟩
  exact node.the_source_generates_its_whole_ledger_actual_epoch

theorem the_cost_clock_is_the_actual_epoch_clock_difference (n : Nat) :
    clockCost source.native.input (Evolving.Epoch.Source.originalState source.native) (programme source n) =
      (Evolving.Epoch.History.currentAt source n).raw.clock - source.raw.clock := by
  unfold clockCost
  rw [the_compiled_history_is_the_literal_actual_epoch_physical_current]
  rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Programme.Epoch
