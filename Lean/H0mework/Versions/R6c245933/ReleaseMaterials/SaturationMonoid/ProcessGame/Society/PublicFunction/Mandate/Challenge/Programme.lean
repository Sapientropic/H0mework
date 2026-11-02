import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.History.Runtime

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Challenge

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]

/-- Indexing identifies actual programmes; extension laws belong to the emitting source. -/
structure ProgrammeFamily (base : RawLaw Party Good Port Technology Instrument)
    (scope : Scope (Party := Party) (Good := Good) (Port := Port)) (Index : Type) where
  inputAt : Index → ProgrammeSource.Input Party Good Port (State Party Technology) Instrument
  law_exact : ∀ index, (inputAt index).law = law base scope

def fromHistory {base : RawLaw Party Good Port Technology Instrument}
    {scope : Scope (Party := Party) (Good := Good) (Port := Port)} (bound : BoundSource base scope) :
    ProgrammeFamily base scope (List (RawEvent Party Good Port (State Party Technology) Instrument)) where
  inputAt := OutstandingSource.History.input bound.source
  law_exact := fun _ => bound.law_exact

instance {base : RawLaw Party Good Port Technology Instrument}
    {scope : Scope (Party := Party) (Good := Good) (Port := Port)} :
    CoeOut (BoundSource base scope)
      (ProgrammeFamily base scope (List (RawEvent Party Good Port (State Party Technology) Instrument))) :=
  ⟨fromHistory⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Challenge
