import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Global.Seed
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Entitlement.Duty.Law
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Background

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint

open Source.Program Innovation
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))

def window : Entitlement.Source.Window (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument) := ⟨seed.input,seed.depth,seed.count⟩

def productiveState := Abolition.Accounting.Root.Reentry.Frame.state seed.claim seed.current

def actualLaw := seed.current.actualLaw

def currentRaw := (productiveState seed).raw

def backgroundAccount := Evolution.Ingress.Joint.Background.account seed

def pending := Evolution.Ingress.Joint.Background.pending seed

theorem live_raw_is_the_original_registered_current : currentRaw seed =
    (Abolition.Accounting.Root.Reentry.Frame.state seed.claim seed.current).raw := rfl

theorem gross_and_productive_have_the_same_original_execution :
    (Control.responseExecution mechanism past nature response).items =
      seed.input.law.rawItems (window seed).before (window seed).word :=
  Abolition.Accounting.Root.Source.the_assessed_inventory_is_the_literal_original_execution
    seed.input (Evolution.Ingress.Joint.Background.original seed).native
    ((Evolution.Ingress.Joint.Background.original seed).temporal seed.input) seed.claim seed.origin

theorem original_cause_is_accounted : (window seed).Accounted := seed.origin.accounted

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint
