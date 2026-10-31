import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.Discovery.Routes

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.Discovery

open Program
universe u
variable {Party Good Port Technology Instrument : Type u}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (law : RawLaw Party Good Port Technology Instrument)
  (current : RawCurrent Party Good Technology Instrument)
  (word : RawEvent Party Good Port Technology Instrument)

abbrev AllocationRoutes := List (Party × List (OriginalItem law current word))

def insertAllocation (routes : AllocationRoutes law current word) (holder : Party)
    (route : List (OriginalItem law current word)) : AllocationRoutes law current word :=
  if routes.any (fun previous => decide (previous.1 = holder)) then routes else routes ++ [(holder, route)]

def allocationRoutes (access : AccessProposal law current word) (upper : Nat) :
    AllocationRoutes law current word :=
  (law.rawItems current word).attach.foldl (fun routes item =>
    if item.val.index < upper then
      routes.foldl (fun result prior =>
        if DisposalProposal.AuthorizedAllocation law current word prior.1 item then
          insertAllocation law current word result
            (DisposalProposal.allocationRecipient law current word prior.1 item)
            (prior.2 ++ [item])
        else result) routes
    else routes) [(access.controller law current word, [])]

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.Discovery
