import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Root.History
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Choice.Robust

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Root

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {World Observation : Type*}

local notation "C" => Cut Party Good Port Technology Instrument
local notation "Word" => RawEvent Party Good Port Technology Instrument
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))

abbrev branchCut (source : C) (branches : World → Script) (world : World) : C :=
  Quantities.Execution.endAt source (branches world)

def branchObservation (source : C) (branches : World → Script) (observe : C → Observation) :
    World → Observation :=
  observe ∘ branchCut source branches

/-- An action is the same original signed word across indistinguishable
branches. The source, its ready boundary and its paid successor are reread. -/
def sourcePolicyMenu (source : C) (branches : World → Script) (observe : C → Observation)
    (classifies : C → Word → Prop) (read : C → ℝ) :
    Choice.Menu (Choice.Policy (branchObservation source branches observe) Word × ℝ) :=
  Choice.policyMenu (branchObservation source branches observe)
    (fun world word =>
      let cut := branchCut source branches world
      classifies cut word ∧ Paid cut word)
    (fun world word => read (terminal (branchCut source branches world) word))

theorem a_supported_prior_policy_pays_on_each_original_branch
    (source : C) (branches : World → Script) (observe : C → Observation)
    (classifies : C → Word → Prop) (read : C → ℝ)
    {trial : Choice.Policy (branchObservation source branches observe) Word × ℝ}
    (supported : trial ∈ (sourcePolicyMenu source branches observe classifies read).executable)
    (world : World) :
    let cut := branchCut source branches world
    let selected := trial.1 (Set.rangeFactorization (branchObservation source branches observe) world)
    Quantities.Recorded source (branches world) ∧ classifies cut selected ∧
      Paid cut selected ∧ trial.2 ≤ read (terminal cut selected) := by
  have ⟨⟨classified, paid⟩, floor⟩ := supported world
  exact ⟨Quantities.record source _, classified, paid, floor⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Root
