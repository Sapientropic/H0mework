import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Emergency.Horizon

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Emergency

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open PublicFunction.Mandate

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]

local notation "C" => Root.Cut Party Good Port (State Party Technology) Instrument
local notation "Word" => RawEvent Party Good Port (State Party Technology) Instrument
local notation "Base" => RawLaw Party Good Port Technology Instrument
local notation "J" => Scope (Party := Party) (Good := Good) (Port := Port)
local notation "Proposal" => Compile.RawInput Party Good Port (State Party Technology) Instrument

abbrev policyCut (source : C) (policy : Nat → C → Option Proposal) (index : Nat) : C :=
  Quantities.Execution.endAt source (Quantities.Execution.observedScript policy index source)

omit [DecidableEq Technology] in
theorem policy_clock_monotone (source : C) (policy : Nat → C → Option Proposal) :
    Monotone (fun index => (policyCut source policy index).raw.clock) := by
  apply monotone_nat_of_le_succ
  intro index
  change (policyCut source policy index).raw.clock ≤ (policyCut source policy (index + 1)).raw.clock
  unfold policyCut at *
  rw [Quantities.Execution.observed_policy_next]
  exact Quantities.Execution.the_actual_script_never_runs_the_clock_backwards
    (policyCut source policy index) [policy index (policyCut source policy index)]

/-- Repeated crisis proposals have the original first expired cut whenever
the actual clock crosses. A stalled clock is returned as an actual time
obstruction, so merely counting attempted emergencies does not start time. -/
theorem first_expiry_on_an_actual_crisis_policy {source : C} {base : Base} {scope : J}
    (original : Installed source base scope) (policy : Nat → C → Option Proposal) :
    (∃ index, (∀ earlier < index, (policyCut source policy earlier).raw.clock ≤ scope.task.deadline) ∧
      ∀ later ≥ index, let cut := policyCut source policy later
        Quantities.Recorded source (Quantities.Execution.observedScript policy later source) ∧
        Installed cut base scope ∧ scope.task.deadline < cut.raw.clock ∧
        ∀ word : Word, ∀ event : ActualCommand base scope cut.raw word,
          event.command ≠ .accept ∧ event.command ≠ .renew ∧ ∀ candidate, event.command ≠ .propose candidate) ∨
      ∀ index, (policyCut source policy index).raw.clock ≤ scope.task.deadline := by
  classical
  by_cases crossed : ∃ index, scope.task.deadline < (policyCut source policy index).raw.clock
  · refine .inl ⟨Nat.find crossed, fun _ earlier => le_of_not_gt (Nat.find_min crossed earlier), ?_⟩
    intro later after
    have late := (Nat.find_spec crossed).trans_le (policy_clock_monotone source policy after)
    exact ⟨Quantities.record source _, original.along _, late,
      fun word event => late_command_is_not_a_grant base scope (policyCut source policy later).raw word event late⟩
  · exact .inr fun index => le_of_not_gt fun late => crossed ⟨index, late⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Emergency
