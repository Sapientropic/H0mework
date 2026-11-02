import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.History.Core
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.History.Discovery.Allocations

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.History.Discovery

open Program
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : Root.ProgrammeSource.Input Party Good Port Technology Instrument)
  (endpoint : Visit input)
  (access : Access input endpoint)

def claimKeys : List (Instrument × Party) :=
  (entries input endpoint).filterMap (fun item => match (item.raw input).request.operation with
    | .issue instrument debtor _ _ | .assign instrument debtor _ _ _ |
        .settle instrument debtor _ _ => some (instrument, debtor)
    | _ => none)

def physicalDisposalsAt (position : Entry input endpoint)
    (holder : Party) (allocations : List (Entry input endpoint)) :
    List (Disposal input endpoint) :=
  (materialCells input endpoint).flatMap (fun cell =>
    let quantity := min 1 ((position.raw input).before.stock cell.1 cell.2)
    if 0 < quantity then
      [⟨position, ⟨holder, [], access.port, [], .use holder [(cell.2, quantity)] .external⟩, cell.2, allocations⟩,
       ⟨position, ⟨holder, [], access.port, [], .use holder [(cell.2, quantity)] .investment⟩, cell.2, allocations⟩,
       ⟨position, ⟨holder, [], access.port, [], .transfer cell.1 holder [(cell.2, quantity)]⟩, cell.2, allocations⟩]
    else [])

def financialDisposalsAt (position : Entry input endpoint)
    (holder : Party) (allocations : List (Entry input endpoint)) :
    List (Disposal input endpoint) :=
  (claimKeys input endpoint).flatMap (fun key =>
    let quantity := min 1 ((position.raw input).before.claims key.1 key.2 holder)
    if 0 < quantity then
      (parties input endpoint).filterMap (fun recipient =>
        if recipient ≠ holder then
          some ⟨position, ⟨holder, [], access.port, [], .assign key.1 key.2 holder recipient quantity⟩,
            input.law.settlementUnit key.1, allocations⟩
        else none)
    else [])

def disposals : List (Disposal input endpoint) :=
  ((entries input endpoint).flatMap (fun position =>
    (materialGoods input endpoint).map (fun good =>
      (⟨position, (position.raw input).request, good, []⟩ : Disposal input endpoint)) ++
    ((input.law.controller (position.raw input).before.technology access.port, []) ::
      allocationRoutes input endpoint access (position.position input)).flatMap (fun title =>
        physicalDisposalsAt input endpoint access position title.1 title.2 ++
        financialDisposalsAt input endpoint access position title.1 title.2))).filter
      (fun proposal => decide (proposal.Checks input endpoint access))

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.History.Discovery
