import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Settlement.Decision

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Settlement

open Abolition.Root Abolition.Root.Registered PublicFunction

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {TaskId : Type*} [DecidableEq TaskId]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))
local notation "Task" => PublicTaskSpec Party Good

theorem named_first_problem_refutes_the_joint_original_cut
    (source : C) (script : Script) (ordered : List TaskId) (task : TaskId → Task)
    (reserved : Finset (Service.Ordinal source script))
    (problem : Problem source script ordered task reserved (fun _ => 0))
    (first : firstProblem source script ordered task reserved (fun _ => 0) = some problem)
    (reached : problemTime problem ≤ finish source script) :
    ¬ JointThrough source script ordered.toFinset task reserved (watched source script ordered task)
      (fun _ => 0) (finish source script) := by
  intro paid
  have timely := (the_latest_safe_renewal_cut_is_tight_for_the_joint_original_agenda
    source script ordered task reserved (fun _ => 0) (finish source script)
    (Execution.the_actual_script_never_runs_the_clock_backwards source script)).mp paid
  have exactCut := first_problem_is_the_exact_original_renewal_boundary source script ordered task reserved (fun _ => 0)
  rw [first] at exactCut
  rw [← exactCut] at timely
  exact (not_lt_of_ge reached) (WithTop.coe_lt_coe.mp timely)

theorem the_native_due_decision_accepts_exactly_the_joint_paid_executions
    (source : C) (script : Script) (ordered : List TaskId) (task : TaskId → Task)
    (reserved : Finset (Service.Ordinal source script)) :
    (∃ paid, inspect source script ordered task reserved = .paid paid) ↔
      Service.OriginalDemands ordered.toFinset task ∧ Settled source script ∧
        JointThrough source script ordered.toFinset task reserved (watched source script ordered task)
          (fun _ => 0) (finish source script) := by
  constructor
  · rintro ⟨paid, _⟩
    exact ⟨paid.originalDemands, paid.settlement, paid.safe⟩
  · rintro ⟨original, paid, ready⟩
    cases decided : inspect source script ordered task reserved with
    | paid result => exact ⟨result, rfl⟩
    | malformed bad => exact (bad original).elim
    | native issue => exact (issue.refutes paid.toFeasible).elim
    | overdue problem first reached =>
      exact (named_first_problem_refutes_the_joint_original_cut _ _ _ _ _ problem first reached ready).elim

theorem a_missed_joint_due_cut_returns_its_first_original_problem_and_keeps_the_whole_ledger
    (source : C) (script : Script) (ordered : List TaskId) (task : TaskId → Task)
    (reserved : Finset (Service.Ordinal source script))
    (original : Service.OriginalDemands ordered.toFinset task) (paid : Settled source script)
    (failed : ¬ JointThrough source script ordered.toFinset task reserved (watched source script ordered task)
      (fun _ => 0) (finish source script)) :
    ∃ problem first reached,
      inspect source script ordered task reserved = .overdue problem first reached ∧
        Recorded source script ∧
        Recorded source (Liquidity.committedPrefix (problemTime problem) source script) := by
  cases decided : inspect source script ordered task reserved with
  | paid result => exact (failed result.safe).elim
  | malformed bad => exact (bad original).elim
  | native issue => exact (issue.refutes paid.toFeasible).elim
  | overdue problem first reached =>
    exact ⟨problem, first, reached, rfl, paid.toRecorded, record _ _⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Settlement
