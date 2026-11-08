import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.Consecutive.Frontier

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.Consecutive

open Abolition.Root Abolition.Root.Registered

universe u v

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))

/-- Physiological admissibility requires independent source evidence for
this person and exposure. Occupation and stock restoration supply the
clock and material coordinates of that judgement. -/
structure BodyEvidence (origin : C) (meter : Meter.{u} origin) where
  Admits : (exposure : Script) → Party → Type v

structure RecoveryBackedAdmission (origin : C) (meter : Meter.{u} origin) (body : BodyEvidence.{u,v} origin meter)
    (exposure repair : Script) (person : Party) where
  observed : body.Admits exposure person
  recovery : PaidRecovery origin exposure repair

private def compareBody (origin : C) (meter : Meter.{u} origin) (tolerance : ℚ) : BodyEvidence.{u,0} origin meter where
  Admits exposure person := PLift (originalLongest origin meter exposure person ≤ tolerance)

/-- The same original metered occurrence admits two observationally
indistinguishable extensions with opposite body verdicts. This checks
which field is needed before asserting physiological safety. -/
theorem a_positive_original_run_does_not_identify_its_body_admission
    (origin : C) (meter : Meter.{u} origin) (exposure : Script) (person : Party)
    (positive : 0 < originalLongest origin meter exposure person) :
    ∃ accepts rejects : BodyEvidence.{u,0} origin meter,
      Nonempty (accepts.Admits exposure person) ∧ IsEmpty (rejects.Admits exposure person) := by
  let run := originalLongest origin meter exposure person
  refine ⟨compareBody origin meter run, compareBody origin meter (run / 2),
    ⟨⟨le_rfl⟩⟩, ⟨fun rejected => ?_⟩⟩
  have admissible : run ≤ run / 2 := rejected.down
  linarith only [positive, admissible]

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.Consecutive
