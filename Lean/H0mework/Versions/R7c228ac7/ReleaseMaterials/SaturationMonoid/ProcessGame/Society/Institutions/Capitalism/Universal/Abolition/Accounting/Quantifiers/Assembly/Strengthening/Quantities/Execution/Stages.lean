import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Root.Settlement
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Root.Profile

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution

open Abolition.Root Abolition.Root.Registered

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))
local notation "Policy" => Nat → C → Script

/-- Requery only the actual current after the previous stage. A stage may
be an arbitrarily long original local programme. -/
def stageScript (source : C) (policy : Policy) : Nat → Script
  | 0 => []
  | stage + 1 =>
    let front := stageScript source policy stage
    front ++ policy stage (endAt source front)

def stageAt (source : C) (policy : Policy) (stage : Nat) : C :=
  endAt source (stageScript source policy stage)

def stageBody (source : C) (policy : Policy) (stage : Nat) : Script :=
  policy stage (stageAt source policy stage)

theorem next_stage_is_the_literal_original_next (source : C) (policy : Policy) (stage : Nat) :
    stageAt source policy (stage + 1) = endAt (stageAt source policy stage) (stageBody source policy stage) :=
  endAt_append _ _ _

theorem every_stage_retains_all_original_claims_and_generates_its_next
    (source : C) (policy : Policy) (stage : Nat) :
    Recorded source (stageScript source policy stage) ∧
      Recorded (stageAt source policy stage) (stageBody source policy stage) :=
  ⟨record source _, record _ _⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution
