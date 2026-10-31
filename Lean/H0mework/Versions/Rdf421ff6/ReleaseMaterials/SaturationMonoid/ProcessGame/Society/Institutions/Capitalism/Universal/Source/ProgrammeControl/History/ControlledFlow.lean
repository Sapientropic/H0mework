import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.History.Flow
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.ActualSurplus.Path

/-! Different goods may be linked only by an actual production leg under
this same original control port.  Moving goods does not generate title. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.History

open Program
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : Root.ProgrammeSource.Input Party Good Port Technology Instrument)
  (endpoint : Visit input) (port : Port) (recipient : Party)

def controlAlong : Party × Good → List (RouteLeg input endpoint) → Prop
  | _, [] => True
  | origin, leg :: tail =>
      Kernel.ActualSurplus.flowLegAllowed input.law (leg.item.raw input) port recipient origin leg.destination ∧
      controlAlong leg.destination tail

instance (origin : Party × Good) (route : List (RouteLeg input endpoint)) :
    Decidable (controlAlong input endpoint port recipient origin route) := by
  induction route generalizing origin with
  | nil => unfold controlAlong; infer_instance
  | cons head tail ih =>
      unfold controlAlong
      letI := ih head.destination
      infer_instance

private def controlledExtend (item : Entry input endpoint) (routes : Routes input endpoint) : Routes input endpoint :=
  routes.foldl (fun found prior =>
    (input.law.actualCredit (item.raw input).before (item.raw input).request).foldl (fun result lot =>
      if Kernel.ActualSurplus.flowLegAllowed input.law (item.raw input) port recipient prior.1 lot.1 then
        insertRoute input endpoint result lot.1 (prior.2 ++ [⟨item, lot.1⟩])
      else result) found) routes

def controlledRouteBetween (origin destination : Party × Good) (lower upper : Nat) :
    Option (List (RouteLeg input endpoint)) :=
  findRoute input endpoint
    ((entries input endpoint).foldl (fun routes item =>
      if lower ≤ item.position input ∧ item.position input < upper then
        controlledExtend input endpoint port recipient item routes else routes)
      [(origin, [])]) destination

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.History
