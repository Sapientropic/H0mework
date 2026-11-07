import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant.Capture.Material
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.Reader

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant.Capture

open Source.Program Abolition.Root Abolition.Root.Registered PublicFunction PublicFunction.Repayment

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Plan" => Proposal Party Good Port Technology Instrument
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))

/-- Each exposure input comes from the reader installed before the grant.
It reads the newest actual current and account at that original address. -/
def exposureScript (source : C) (position : Position Party Instrument) (plan : Plan) (count : Nat) : Script :=
  Execution.originalResponses source
    (plan.preparation ++ grantScript (funded source plan) position plan.quantity) count

def exposed (source : C) (position : Position Party Instrument) (plan : Plan) (count : Nat) : C :=
  Execution.endAt (redeemed source position plan) (exposureScript source position plan count)

def expand (source : C) (position : Position Party Instrument) (count : Nat) (plan : Plan) : Plan :=
  {plan with continuation := exposureScript source position plan count ++ plan.continuation}

theorem the_exit_runs_at_the_actual_after_charge_cut (source : C) (position : Position Party Instrument)
    (plan : Plan) (count : Nat) :
    Execution.endAt source (compile source position (expand source position count plan)) =
      Execution.endAt (exposed source position plan count) plan.continuation := by
  rw [the_grant_and_its_continuation_share_the_actual_next]
  exact Execution.endAt_append (redeemed source position plan)
    (exposureScript source position plan count) plan.continuation

inductive ExitIssue (source : C) (position : Position Party Instrument)
    (task : PublicTaskSpec Party Good) (count : Nat) (plan : Plan)
  | grant (original : Issue source position [] task (expand source position count plan))
  | capacity (unpaid : Clock.Window.Shortage (exposed source position plan count) task plan.continuation)

def inspectExit (source : C) (position : Position Party Instrument)
    (task : PublicTaskSpec Party Good) (count : Nat) (plan : Plan) :
    Option (ExitIssue source position task count plan) :=
  match inspectPlan source position [] task (expand source position count plan) with
  | some issue => some (.grant issue)
  | none => (Clock.Window.inspect (exposed source position plan count) task plan.continuation).map .capacity

theorem the_exit_check_is_exactly_paid_and_service_survives_the_original_charges
    (source : C) (position : Position Party Instrument) (task : PublicTaskSpec Party Good)
    (count : Nat) (plan : Plan) :
    inspectExit source position task count plan = none ↔
      Eligible source position [] task (expand source position count plan) ∧
        Clock.Window.FullyServed (exposed source position plan count) task plan.continuation := by
  unfold inspectExit
  rw [← inspect_passes_iff_funded_and_independently_served,
    ← Clock.Window.passes_iff_every_original_service_commits_in_time]
  cases inspectPlan source position [] task (expand source position count plan) <;>
    cases Clock.Window.inspect (exposed source position plan count) task plan.continuation <;> simp

theorem exact_exit_amounts_after_the_original_exposure
    (source : C) (position : Position Party Instrument) (task : PublicTaskSpec Party Good)
    (count : Nat) (amount : EReal) :
    amount ∈ Bounds.Compiled.values source (fun plan => compile source position (expand source position count plan))
      (inspectExit source position task count) principal ↔
      ∃ plan, Completed source position [] task (expand source position count plan) ∧
        Clock.Window.FullyServed (exposed source position plan count) task plan.continuation ∧
        principal plan = amount := by
  constructor
  · rintro ⟨plan, paid, inspected, rfl⟩
    obtain ⟨eligible, served⟩ :=
      (the_exit_check_is_exactly_paid_and_service_survives_the_original_charges _ _ _ _ _).mp inspected
    refine ⟨plan, ?_, served, rfl⟩
    exact (complete_iff_original_paid_and_eligible _ _ _ _ _).mpr
      ⟨paid, (inspect_passes_iff_funded_and_independently_served _ _ _ _ _).mpr eligible⟩
  · rintro ⟨plan, paid, served, rfl⟩
    exact ⟨plan, paid.root,
      (the_exit_check_is_exactly_paid_and_service_survives_the_original_charges _ _ _ _ _).mpr
        ⟨paid.eligible, served⟩, rfl⟩

theorem the_original_root_resolves_exit_amounts_after_its_actual_exposure
    (source : C) (position : Position Party Instrument) (task : PublicTaskSpec Party Good) (count : Nat) :
    Bounds.Compiled.Minimum source (fun plan => compile source position (expand source position count plan))
      (inspectExit source position task count) principal :=
  Bounds.Compiled.resolve _ _ _ _

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant.Capture
