import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Demand.Feasible

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities

open Source.Program
open Abolition.Root Abolition.Root.Registered

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))

/-- The terminal cut and its next inquiry are determined by the original
execution. The claim and row maps are its composed native writes. -/
structure Recorded (source : C) (script : Script) : Prop where
  sameInput : (Execution.endAt source script).native.input = source.native.input
  actualWrites : ∀ cut ∈ Execution.queries source script, Evolving.Epoch.Current.ClosedAt cut
  claims : Function.Injective (Execution.claimAt source script)
  rows : ∀ row : Execution.RowAt source,
    (Execution.rowAt source script row).claim = Execution.claimAt source script row.claim ∧
    (Execution.rowAt source script row).progressBudget ≤ row.progressBudget
  actualBalance : ∀ bearer good,
    (Execution.endAt source script).raw.stock bearer good +
      source.native.handlerFace.rootRead.totalDebit (Execution.inventory source script) bearer good =
    source.raw.stock bearer good +
      source.native.handlerFace.rootRead.totalCredit (Execution.inventory source script) bearer good
  next : Evolving.Epoch.Current.ClosedAt (Execution.endAt source script)

theorem record (source : C) (script : Script) : Recorded source script where
  sameInput := Execution.endAt_input source script
  actualWrites := Execution.every_query_has_its_original_root_write source script
  claims := Execution.claimAt_injective source script
  rows := Execution.rowAt_exact source script
  actualBalance := all_capacity_is_paid_from_the_original_stock_and_actual_credits source script
  next := (Execution.endAt source script).the_source_generates_its_whole_ledger_actual_epoch

structure Settled (source : C) (script : Script) : Prop
    extends Feasible source script, Recorded source script

theorem settle (source : C) (script : Script) (paid : Feasible source script) :
    Settled source script :=
  ⟨paid, record source script⟩

theorem actual_settlement_iff_feasible (source : C) (script : Script) :
    Settled source script ↔ Feasible source script :=
  ⟨Settled.toFeasible, settle source script⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities
