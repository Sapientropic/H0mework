import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.TightBound

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.Cohort

open Abolition.Root Abolition.Root.Registered

noncomputable section

universe u

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))

/-- Every person has an hours coordinate. A ratio coordinate is present
when that person's original exposure has positive measured length. -/
inductive Address (origin : C) (meter : Meter.{u} origin) (exposure : Script)
  | hours (person : Party)
  | ratio (person : Party) (positive : 0 < originalExposure origin meter exposure person)

def amount (origin : C) (meter : Meter.{u} origin) (exposure repair : Script) :
    Address origin meter exposure → ℚ
  | .hours person => hoursThroughRepair origin meter exposure repair person
  | .ratio person _ =>
    hoursThroughRepair origin meter exposure repair person / originalExposure origin meter exposure person

def profile (origin : C) (meter : Meter.{u} origin) (exposure repair : Script)
    (address : Address origin meter exposure) : EReal :=
  ((amount origin meter exposure repair address : ℝ) : EReal)

theorem ratio_coordinate_is_the_original_individual_read
    (origin : C) (meter : Meter.{u} origin) (exposure repair : Script) (person : Party)
    (positive : 0 < originalExposure origin meter exposure person) :
    profile origin meter exposure repair (.ratio person positive) =
      readRatio origin meter exposure person repair := rfl

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.Cohort
