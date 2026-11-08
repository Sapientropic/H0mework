import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Mixed.Deadline.Failure

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Mixed

open Source.Program Abolition.Root Abolition.Root.Registered PublicFunction
open _root_.SaturationMonoid.ProcessGame.Society.Capacity.QuantityFlow

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {TaskId : Type*} [DecidableEq TaskId]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))

abbrev terminalTime (source : C) (script : Script) := (Execution.endAt source script).raw.clock

structure TerminalAllocation (agenda : Agenda Party Good TaskId) (source : C) (script : Script)
    (additional : Party × Good → ℚ) where
  whole : ChoiceAt agenda source script (terminalTime source script)
  certificate : (networkAt agenda source script (terminalTime source script) whole).Certificate
  complete : (networkAt agenda source script (terminalTime source script) whole).Complete certificate.allocation
  reserve : ∀ key ∈ watchedAddresses agenda source script, (stockProfile agenda source script).rollingReserveThrough
    (Liquidity.beforeStock source script) (terminalTime source script) key ≤ additional key

theorem TerminalAllocation.jointlyFits
    {agenda : Agenda Party Good TaskId} {source : C} {script : Script} {additional : Party × Good → ℚ}
    (allocation : TerminalAllocation agenda source script additional) :
    JointThrough agenda source script additional (terminalTime source script) := by
  apply (the_mixed_service_and_stock_conditions_share_one_original_execution _ _ _ _ _).mpr
  exact ⟨⟨allocation.whole,
    ((base agenda source script allocation.whole.reserved).restriction_is_exact_for_the_original_due_rows
      (keepAt agenda (terminalTime source script))).mp ⟨allocation.certificate.allocation, allocation.complete⟩⟩, allocation.reserve⟩

inductive TerminalResult (agenda : Agenda Party Good TaskId) (source : C) (script : Script)
    (additional : Party × Good → ℚ)
  | overdue (failure : JointFailure agenda source script additional)
      (reached : failure.cause.time ≤ terminalTime source script)
  | nativeBlocked (allocation : TerminalAllocation agenda source script additional) (issue : Obstruction source script)
  | settled (allocation : TerminalAllocation agenda source script additional) (paid : Settled source script)

/-- The earlier cut determines admissibility. The final action consumes its
selected assignment through the same native root and whole-ledger successor. -/
def settleTerminal (agenda : Agenda Party Good TaskId) (source : C) (script : Script)
    (additional : Party × Good → ℚ) : TerminalResult agenda source script additional :=
  let time := terminalTime source script
  if safe : (time : WithTop ℚ) < jointRenewalBoundary agenda source script additional then
    let started := Execution.the_actual_script_never_runs_the_clock_backwards source script
    let jointly := (the_mixed_renewal_boundary_is_the_exact_joint_original_cut
      agenda source script additional time started).mpr safe
    let fits := (the_mixed_service_and_stock_conditions_share_one_original_execution
      agenda source script additional time).mp jointly
    let selected := inspectAt agenda source script time
    have available : selected.hasAllocation = true :=
      (inspectAt_pays_exactly_the_original_due_prefix agenda source script time).mpr fits.1
    match selected, available with
    | .noWhole .., contradicted => (Bool.noConfusion contradicted : False).elim
    | .short .., contradicted => (Bool.noConfusion contradicted : False).elim
    | .available whole receipt complete, _ =>
      let allocation : TerminalAllocation agenda source script additional := ⟨whole, receipt, complete, fits.2⟩
      match decideAt source script with
      | .blocked issue => .nativeBlocked allocation issue
      | .feasible paid => .settled allocation (settle source script paid)
  else
    let failure := nameJointFailure agenda source script additional time (le_of_not_gt safe)
    .overdue failure (WithTop.coe_le_coe.mp (failure.exactClock.symm ▸ le_of_not_gt safe))

def TerminalResult.paid {agenda : Agenda Party Good TaskId} {source : C} {script : Script}
    {additional : Party × Good → ℚ} : TerminalResult agenda source script additional → Bool
  | .settled .. => true
  | _ => false

theorem terminal_payment_is_exact
    {agenda : Agenda Party Good TaskId} {source : C} {script : Script} {additional : Party × Good → ℚ}
    (result : TerminalResult agenda source script additional) :
    result.paid = true ↔ JointThrough agenda source script additional (terminalTime source script) ∧ Feasible source script := by
  cases result with
  | overdue failure reached =>
    refine ⟨fun impossible => Bool.noConfusion impossible, fun paid => ?_⟩
    have tight := (the_mixed_renewal_boundary_is_the_exact_joint_original_cut agenda source script additional
      (terminalTime source script) (Execution.the_actual_script_never_runs_the_clock_backwards source script)).mp paid.1
    rw [← failure.exactClock] at tight
    exact ((not_lt_of_ge reached) (WithTop.coe_lt_coe.mp tight)).elim
  | nativeBlocked _ issue => exact ⟨fun impossible => Bool.noConfusion impossible, fun paid => (issue.refutes paid.2).elim⟩
  | settled allocation paid => exact ⟨fun _ => ⟨allocation.jointlyFits, paid.toFeasible⟩, fun _ => rfl⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Mixed
