import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.WorkHours

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.Robust

open Abolition.Root Abolition.Root.Registered

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))

structure BranchPaid (origin : C) (exposure repair : Script) : Prop where
  duration : 0 < elapsed origin exposure
  paid : Settled (Execution.endAt origin exposure) repair
  restored : Restored origin exposure repair
  original : Recorded origin (exposure ++ repair)

inductive BranchIssue (origin : C) (exposure repair : Script)
  | clock (zero : elapsed origin exposure = 0)
  | account (issue : Obstruction (Execution.endAt origin exposure) repair)
  | material (loss : Loss origin exposure repair)

theorem BranchIssue.refutes {origin : C} {exposure repair : Script}
    (issue : BranchIssue origin exposure repair) : ¬ BranchPaid origin exposure repair := by
  intro paid
  cases issue with
  | clock zero => exact paid.duration.ne' zero
  | account issue => exact issue.refutes paid.paid.toFeasible
  | material loss => exact (not_le_of_gt loss.unpaid) (paid.restored loss.address.1 loss.address.2)

inductive BranchDecision (origin : C) (exposure repair : Script)
  | paid (paid : BranchPaid origin exposure repair)
  | blocked (issue : BranchIssue origin exposure repair)

def inspectBranch (origin : C) (exposure repair : Script) : BranchDecision origin exposure repair :=
  if positive : 0 < elapsed origin exposure then
    match decideAt (Execution.endAt origin exposure) repair with
    | .blocked issue => .blocked (.account issue)
    | .feasible paid =>
        match observed : inspect origin exposure repair with
        | some loss => .blocked (.material loss)
        | none =>
            .paid ⟨positive, settle _ _ paid,
              (cleared_exactly_when_no_original_actor_loses_stock _ _ _).mp observed, record origin _⟩
  else .blocked (.clock (le_antisymm (le_of_not_gt positive) (elapsed_nonnegative origin exposure)))

theorem failed_branch_has_original_issue (origin : C) (exposure repair : Script)
    (failed : ¬ BranchPaid origin exposure repair) : Nonempty (BranchIssue origin exposure repair) := by
  cases inspectBranch origin exposure repair with
  | paid paid => exact (failed paid).elim
  | blocked issue => exact ⟨issue⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.Robust
