import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Repair.Continuation

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Actual

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count : Nat)

abbrev N := Migration.N input depth count
abbrev Raw := RawCurrent Party Good Technology Instrument
abbrev Code := RawEvent Party Good Port Technology Instrument
abbrev origin := Migration.origin input depth count
abbrev members := Migration.cohort input depth count

inductive Phase (Party Good Port Technology Instrument : Type)
  | seeking
  | renewal (word : RawEvent Party Good Port Technology Instrument)

/-- A current stores one finite continuation programme and the unconsumed
requests of this attempt. Neither field contains successful future states. -/
structure Current where
  raw : Raw (Party := Party) (Good := Good) (Technology := Technology) (Instrument := Instrument)
  phase : Phase Party Good Port Technology Instrument
  remaining : Code (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)

noncomputable def initial : Current (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) :=
  ⟨origin input depth count, .seeking, Repair.alphabet input (origin input depth count)⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Actual
