import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.Fold
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Programme.Epoch.History
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime.Runner

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution

open Source.Program Abolition.Root Abolition.Root.Registered

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Proposal" => Compile.RawInput Party Good Port Technology Instrument
local notation "Script" => List (Option Proposal)

theorem installed_history (source : C) (ticks : Nat) :
    endAt source (List.replicate ticks (none : Option Proposal)) =
      Evolving.Epoch.History.currentAt source ticks := by
  induction ticks with
  | zero => rfl
  | succ ticks ih =>
      rw [show List.replicate (ticks + 1) (none : Option Proposal) =
        List.replicate ticks none ++ [none] from List.replicate_succ', endAt_append, ih]
      rfl

/-- One raw instruction is followed by its existing native-consumption
step. The encoding leaves the original reader installed for that step. -/
def primitiveScript : RawEvent Party Good Port Technology Instrument → Script
  | [] => []
  | request :: tail => some (.primitive request) :: none :: primitiveScript tail

theorem original_primitive_trace {source target : C}
    {word : RawEvent Party Good Port Technology Instrument}
    (actual : Innovation.Contribution.Pricing.Root.Runtime.Trace source word target) :
    endAt source (primitiveScript word) = target := by
  induction actual with
  | nil => rfl
  | cons source request tail target ready review noConsents valid later ih => exact ih

theorem original_blocked_primitive_trace {source : C}
    {word : RawEvent Party Good Port Technology Instrument}
    (outcome : Innovation.Contribution.Pricing.Root.Runtime.Outcome source word) :
    ∃ script : Script, endAt source script = outcome.current := by
  cases outcome with
  | completed target actual =>
      exact ⟨primitiveScript word, original_primitive_trace actual⟩
  | blocked front stopped request remaining split actual issue =>
      refine ⟨primitiveScript front ++ [some (.primitive request)], ?_⟩
      rw [endAt_append, original_primitive_trace actual]
      rfl

/-- Finite prefixes of arbitrary source-local policies. The policy observes
the current written by the previous tick, with no look-ahead state. -/
def observedScript (policy : Nat → C → Option Proposal) : Nat → C → Script
  | 0, _ => []
  | ticks + 1, source =>
      let front := observedScript policy ticks source
      front ++ [policy ticks (endAt source front)]

theorem observed_policy_next (policy : Nat → C → Option Proposal) (ticks : Nat) (source : C) :
    endAt source (observedScript policy (ticks + 1) source) =
      let current := endAt source (observedScript policy ticks source)
      next current (policy ticks current) := by
  rw [observedScript, endAt_append]
  rfl

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution
