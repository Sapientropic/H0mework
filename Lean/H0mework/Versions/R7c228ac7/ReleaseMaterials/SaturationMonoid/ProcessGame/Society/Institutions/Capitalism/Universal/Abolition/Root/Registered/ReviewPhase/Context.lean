import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.ReviewPhase.Source

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.ReviewPhase

open PublicFunction
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

/-- The registered review code fixes its original source and physical cut.
It contains neither a paid result nor a selected migration. -/
structure ContextAt (input : ProgrammeSource.Input Party Good Port Technology Instrument) where
  private mk ::
  source : OutstandingSource Party Good Port Technology Instrument
  source_eq : source.input = input
  epoch : Physical.Cursor Party Good Port Technology Instrument
  fee : Admission.FeeCode (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)

def register (source : OutstandingSource Party Good Port Technology Instrument)
    (epoch : Physical.Cursor Party Good Port Technology Instrument)
    (fee : Admission.FeeCode (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument)) : ContextAt source.input :=
  ⟨source, rfl, epoch, fee⟩

omit [DecidableEq Port] in
theorem registration_keeps_the_original_source_and_cut
    (source : OutstandingSource Party Good Port Technology Instrument)
    (epoch : Physical.Cursor Party Good Port Technology Instrument)
    (fee : Admission.FeeCode (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument)) :
    (register source epoch fee).source = source ∧
    (register source epoch fee).epoch = epoch ∧
    (register source epoch fee).fee = fee := ⟨rfl, rfl, rfl⟩

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.ReviewPhase
