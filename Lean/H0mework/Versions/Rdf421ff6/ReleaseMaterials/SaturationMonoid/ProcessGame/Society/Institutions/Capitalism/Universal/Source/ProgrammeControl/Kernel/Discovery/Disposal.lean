import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.Discovery.Allocations
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeFace.Trace

/-! Candidate abilities are finite source commands using available physical
stock or an existing financial balance.  Failing to find one proves no
negative assertion; the original control remains unclassified. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.Discovery

open Program
universe u
variable {Party Good Port Technology Instrument : Type u}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (law : RawLaw Party Good Port Technology Instrument)
  (current : RawCurrent Party Good Technology Instrument)
  (word : RawEvent Party Good Port Technology Instrument)
  (access : AccessProposal law current word)

def claimKeys : List (Instrument × Party) :=
  (law.rawItems current word).filterMap (fun item => match item.request.operation with
    | .issue instrument debtor _ _ | .assign instrument debtor _ _ _ |
        .settle instrument debtor _ _ => some (instrument, debtor)
    | _ => none)

def physicalDisposalsAt (position : OriginalItem law current word)
    (holder : Party) (allocations : List (OriginalItem law current word)) :
    List (DisposalProposal law current word) :=
  (materialCells law current word).flatMap (fun cell =>
    let quantity := min 1 (position.val.before.stock cell.1 cell.2)
    if 0 < quantity then
      [⟨position, ⟨holder, [], access.port, [], .use holder [(cell.2, quantity)] .external⟩, cell.2, allocations⟩,
       ⟨position, ⟨holder, [], access.port, [], .use holder [(cell.2, quantity)] .investment⟩, cell.2, allocations⟩,
       ⟨position, ⟨holder, [], access.port, [], .transfer cell.1 holder [(cell.2, quantity)]⟩, cell.2, allocations⟩]
    else [])

def financialDisposalsAt (position : OriginalItem law current word)
    (holder : Party) (allocations : List (OriginalItem law current word)) :
    List (DisposalProposal law current word) :=
  (claimKeys law current word).flatMap (fun key =>
    let quantity := min 1 (position.val.before.claims key.1 key.2 holder)
    if 0 < quantity then
      (ProgrammeFace.parties law (current, word)).filterMap (fun recipient =>
        if recipient ≠ holder then
          some ⟨position, ⟨holder, [], access.port, [], .assign key.1 key.2 holder recipient quantity⟩,
            law.settlementUnit key.1, allocations⟩
        else none)
    else [])

def disposals : List (DisposalProposal law current word) :=
  ((law.rawItems current word).attach.flatMap (fun position =>
    (materialGoods law current word).map (fun good =>
      (⟨position, position.val.request, good, []⟩ : DisposalProposal law current word)) ++
    ((law.controller position.val.before.technology access.port, []) ::
      allocationRoutes law current word access position.val.index).flatMap (fun title =>
        physicalDisposalsAt law current word access position title.1 title.2 ++
        financialDisposalsAt law current word access position title.1 title.2))).filter
      (fun proposal => decide (proposal.Checks law current word access))

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.Discovery
