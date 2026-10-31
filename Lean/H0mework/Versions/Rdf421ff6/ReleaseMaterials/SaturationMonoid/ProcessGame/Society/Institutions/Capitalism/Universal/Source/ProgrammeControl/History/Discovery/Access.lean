import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.History.Core

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.History.Discovery

open Program
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : Root.ProgrammeSource.Input Party Good Port Technology Instrument)
  (endpoint : Visit input)

def accessesTo (need : Entry input endpoint) (recipient : Party) (good : Good) :
    List (Access input endpoint) :=
  (entries input endpoint).flatMap (fun access =>
    (input.law.requiredPorts (access.raw input).before (access.raw input).request).flatMap (fun port =>
      if PrivatePhase input.law (access.raw input).before port recipient then
        (input.law.actualCredit (access.raw input).before (access.raw input).request).filterMap (fun lot =>
          if 0 < lot.2 then
            (routeBetween input endpoint lot.1 (recipient, good)
              ((access.position input) + 1) (need.position input)).map (fun route =>
                ⟨access, need, .acquired, lot.1.1, recipient, port, lot.1.2, good, route⟩)
          else none)
      else [])) ++
  (input.law.requiredPorts (need.raw input).before (need.raw input).request).filterMap (fun port =>
    if PrivatePhase input.law (need.raw input).before port recipient then
      some ⟨need, need, .used, recipient, recipient, port, good, good, []⟩ else none)

def accesses : List (Access input endpoint) :=
  (entries input endpoint).flatMap (fun need =>
    match (need.raw input).request.operation with
    | .use recipient goods kind =>
        if kind = .necessity ∨ kind = .maintenance then
          goods.flatMap (fun lot =>
            if 0 < lot.2 then accessesTo input endpoint need recipient lot.1 else [])
        else []
    | _ => [])

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.History.Discovery
