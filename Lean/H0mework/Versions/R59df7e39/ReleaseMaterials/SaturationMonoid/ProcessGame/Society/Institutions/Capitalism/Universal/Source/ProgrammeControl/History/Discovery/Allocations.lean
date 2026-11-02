import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.History.Core

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.History.Discovery

open Program
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : Root.ProgrammeSource.Input Party Good Port Technology Instrument)
  (endpoint : Visit input)

abbrev AllocationRoutes := List (Party × List (Entry input endpoint))

def insertAllocation (routes : AllocationRoutes input endpoint) (holder : Party)
    (route : List (Entry input endpoint)) : AllocationRoutes input endpoint :=
  if routes.any (fun previous => decide (previous.1 = holder)) then routes else routes ++ [(holder, route)]

def allocationRoutes (access : Access input endpoint) (upper : Nat) :
    AllocationRoutes input endpoint :=
  (entries input endpoint).foldl (fun routes item =>
    if (item.position input) < upper then
      routes.foldl (fun result prior =>
        if Disposal.AuthorizedAllocation input endpoint prior.1 item then
          insertAllocation input endpoint result
            (Disposal.allocationRecipient input endpoint prior.1 item)
            (prior.2 ++ [item])
        else result) routes
    else routes) [(access.controller input endpoint, [])]

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.History.Discovery
