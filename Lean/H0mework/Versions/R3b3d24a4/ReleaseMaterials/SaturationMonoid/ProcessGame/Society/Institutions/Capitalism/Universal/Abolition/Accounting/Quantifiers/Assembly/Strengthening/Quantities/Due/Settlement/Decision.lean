import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Settlement.Problem
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Settlement.Conservation

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Settlement

open Abolition.Root Abolition.Root.Registered PublicFunction
open _root_.SaturationMonoid.ProcessGame.Society.Capacity.QuantityFlow

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {TaskId : Type*} [DecidableEq TaskId]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))
local notation "Task" => PublicTaskSpec Party Good

def finish (source : C) (script : Script) : ℚ := (Execution.endAt source script).raw.clock

def allocateAtFinish (source : C) (script : Script) (ordered : List TaskId) (task : TaskId → Task)
    (reserved : Finset (Service.Ordinal source script)) :=
  Deadline.atCut (Service.network source script ordered.toFinset task reserved) deadline
    (Service.needList ordered.toFinset task ordered rfl)
    (Service.supplyList source script ordered.toFinset task ordered rfl)
    (Service.needList_covers _ _ _ rfl) (Service.supplyList_covers _ _ _ _ _ rfl)
    (finish source script)

structure PaidAt (source : C) (script : Script) (ordered : List TaskId) (task : TaskId → Task)
    (reserved : Finset (Service.Ordinal source script)) where
  originalDemands : Service.OriginalDemands ordered.toFinset task
  settlement : Settled source script
  capacity :
    let network := Service.network source script ordered.toFinset task reserved
    (network.restrict (Deadline.dueBy deadline (finish source script))).Complete
      (allocateAtFinish source script ordered task reserved).allocation
  originalUnits :
    (profile source script ordered.toFinset task reserved
      (allocateAtFinish source script ordered task reserved).allocation).Conservative
  safe : JointThrough source script ordered.toFinset task reserved (watched source script ordered task)
    (fun _ => 0) (finish source script)

inductive Decision (source : C) (script : Script) (ordered : List TaskId) (task : TaskId → Task)
    (reserved : Finset (Service.Ordinal source script))
  | paid (actual : PaidAt source script ordered task reserved)
  | malformed (bad : ¬ Service.OriginalDemands ordered.toFinset task)
  | native (issue : Obstruction source script)
  | overdue (problem : Problem source script ordered task reserved (fun _ => 0))
      (first : firstProblem source script ordered task reserved (fun _ => 0) = some problem)
      (reached : problemTime problem ≤ finish source script)

/-- A successful settlement uses only the stock that the original root
already has and the debits its native execution actually paid. -/
def inspect (source : C) (script : Script) (ordered : List TaskId) (task : TaskId → Task)
    (reserved : Finset (Service.Ordinal source script)) :
    Decision source script ordered task reserved := by
  let clock := finish source script
  let net := Service.network source script ordered.toFinset task reserved
  let chosen := allocateAtFinish source script ordered task reserved
  if original : Service.OriginalDemands ordered.toFinset task then
    if timely : (clock : WithTop ℚ) < renewalBoundary source script ordered task reserved (fun _ => 0) then
      match decideAt source script with
      | .blocked issue => exact .native issue
      | .feasible settled =>
        have started : source.raw.clock ≤ clock := Execution.the_actual_script_never_runs_the_clock_backwards source script
        have ready := (the_latest_safe_renewal_cut_is_tight_for_the_joint_original_agenda
          source script ordered task reserved (fun _ => 0) clock started).mpr timely
        have demandPaid := (the_joint_due_domain_is_exactly_the_original_service_and_stock_domain
          source script ordered.toFinset task reserved (watched source script ordered task) (fun _ => 0) clock).mp ready |>.1
        have paidAll := chosen.complete_or_original_shortage.resolve_right (fun short => by
          exact ((net.restricted_certificate_reports_exact_original_failure _ chosen).mp (sub_pos.mpr short)) demandPaid)
        have legal := net.restricted_allocation_is_admitted_on_original_rows (Deadline.dueBy deadline clock) chosen.admitted
        exact .paid ⟨original, settle source script settled, paidAll,
          allocation_is_conservative_at_every_original_timed_debit legal, ready⟩
    else
      have exactBoundary := first_problem_is_the_exact_original_renewal_boundary source script ordered task reserved (fun _ => 0)
      match observed : firstProblem source script ordered task reserved (fun _ => 0) with
      | none =>
        rw [observed] at exactBoundary
        have top : renewalBoundary source script ordered task reserved (fun _ => 0) = ⊤ := exactBoundary.symm
        exact (timely (by simp [top])).elim
      | some problem =>
        rw [observed] at exactBoundary
        have crossed : renewalBoundary source script ordered task reserved (fun _ => 0) ≤ (clock : WithTop ℚ) :=
          le_of_not_gt timely
        rw [← exactBoundary] at crossed
        exact .overdue problem observed (WithTop.coe_le_coe.mp crossed)
  else
    exact .malformed original

theorem PaidAt.the_original_root_pays_and_generates_the_same_next {source : C} {script : Script}
    {ordered : List TaskId} {task : TaskId → Task} {reserved : Finset (Service.Ordinal source script)}
    (paid : PaidAt source script ordered task reserved) :
    Recorded source script ∧ Evolving.Epoch.Current.ClosedAt (Execution.endAt source script) :=
  ⟨paid.settlement.toRecorded, paid.settlement.next⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Settlement
