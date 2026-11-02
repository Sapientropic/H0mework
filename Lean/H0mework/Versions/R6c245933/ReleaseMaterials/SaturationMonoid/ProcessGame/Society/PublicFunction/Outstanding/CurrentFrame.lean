import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.OutstandingExecution

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.OutstandingSource
open Institutions.Capitalism.Universal.Source.Program

/-- Read the raw current from the same complete source frame. -/
def frameCurrentAt {Party Good Port Technology Instrument : Type}
    [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
    (source : OutstandingSource Party Good Port Technology Instrument) (ordinal : Nat) :
    RawCurrent Party Good Technology Instrument :=
  (source.frameAt ordinal).raw

@[csimp] theorem currentAt_eq_frame : @currentAt = @frameCurrentAt := by
  funext Party Good Port Technology Instrument decParty decGood decInstrument source ordinal
  exact (source.canonical_frame ordinal).1

end SaturationMonoid.ProcessGame.Society.PublicFunction.OutstandingSource
