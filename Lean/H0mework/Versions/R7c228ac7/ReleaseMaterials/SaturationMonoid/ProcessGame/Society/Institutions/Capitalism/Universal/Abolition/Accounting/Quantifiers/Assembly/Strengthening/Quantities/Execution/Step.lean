import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Programme.Epoch.Step
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Complete
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.AfterNative.Reader

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Proposal" => Compile.RawInput Party Good Port Technology Instrument

/-- A source tick can keep its installed reader or receive an original raw input.
Pending native work still has priority in the original dispatcher. -/
def query (source : C) : Option Proposal → C
  | none => source
  | some raw => source.requery (fun _ _ => raw)

def next (source : C) (proposal : Option Proposal) : C :=
  (query source proposal).advance

theorem query_input (source : C) (proposal : Option Proposal) :
    (query source proposal).native.input = source.native.input := by
  cases proposal <;> rfl

theorem query_physical (source : C) (proposal : Option Proposal) :
    Evolving.Epoch.Source.originalState (query source proposal).native =
      Evolving.Epoch.Source.originalState source.native := by
  cases proposal <;> rfl

theorem submitted_is_original (source : C) (raw : Proposal) :
    (query source (some raw)).proposal = raw := rfl

theorem next_input (source : C) (proposal : Option Proposal) :
    (next source proposal).native.input = source.native.input :=
  (query source proposal).advance_parameters.1.trans (query_input source proposal)

theorem actual_step (source : C) (proposal : Option Proposal) :
    Evolving.Epoch.Current.ClosedAt (query source proposal) :=
  (query source proposal).the_source_generates_its_whole_ledger_actual_epoch

theorem effective_step (source : C) (proposal : Option Proposal) :
    Optimality.Programme.run source.native.input (Evolving.Epoch.Source.originalState source.native)
      (Optimality.Programme.Epoch.effective (query source proposal)) =
    Evolving.Epoch.Source.originalState (next source proposal).native := by
  rw [← query_input source proposal, ← query_physical source proposal]
  exact Optimality.Programme.Epoch.the_effective_step_is_the_literal_actual_physical_successor _

theorem effective_inventory (source : C) (proposal : Option Proposal) :
    Optimality.Programme.items source.native.input (Evolving.Epoch.Source.originalState source.native)
      (Optimality.Programme.Epoch.effective (query source proposal)) =
    Optimality.Programme.Epoch.materialItems (query source proposal) := by
  rw [← query_input source proposal, ← query_physical source proposal]
  exact Optimality.Programme.Epoch.the_effective_step_has_exactly_the_reported_material_inventory _

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution
