import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.History.Core

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.History.Discovery

open Program
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : Root.ProgrammeSource.Input Party Good Port Technology Instrument)
  (endpoint : Visit input) (access : Access input endpoint)

def evidences : List (Evidence input endpoint access) :=
  ([Evidence.retention] ++ (input.localAttempts (access.access.raw input).before).attach.map (fun quote => (Evidence.title quote : Evidence input endpoint access)) ++
    (entries input endpoint).flatMap (fun (position : Entry input endpoint) =>
      (materialGoods input endpoint).flatMap (fun good =>
        match controlledRouteBetween input endpoint access.port access.recipient (access.accessHolder, access.accessGood)
          (input.law.controller (position.raw input).before.technology access.port, good)
          (access.access.position input + 1) (position.position input) with
        | none => []
        | some route =>
            Evidence.consumption position good route ::
              (materialGoods input endpoint).map (fun growthGood =>
                Evidence.investment position good growthGood route)))).filter
                  (fun evidence => decide (evidence.Checks input endpoint access))

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.History.Discovery
