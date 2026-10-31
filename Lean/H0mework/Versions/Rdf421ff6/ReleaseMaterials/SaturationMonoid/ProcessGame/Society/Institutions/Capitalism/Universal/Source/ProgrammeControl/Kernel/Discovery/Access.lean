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

def accessesTo (need : OriginalItem law current word) (recipient : Party) (good : Good) :
    List (AccessProposal law current word) :=
  (law.rawItems current word).attach.flatMap (fun access =>
    (law.requiredPorts access.val.before access.val.request).flatMap (fun port =>
      if PrivatePhase law access.val.before port recipient then
        (law.actualCredit access.val.before access.val.request).filterMap (fun lot =>
          if 0 < lot.2 then
            (routeBetween law current word lot.1 (recipient, good)
              (access.val.index + 1) need.val.index).map (fun route =>
                ⟨access, need, .acquired, lot.1.1, recipient, port, lot.1.2, good, route⟩)
          else none)
      else [])) ++
  (law.requiredPorts need.val.before need.val.request).filterMap (fun port =>
    if PrivatePhase law need.val.before port recipient then
      some ⟨need, need, .used, recipient, recipient, port, good, good, []⟩ else none)

def accesses : List (AccessProposal law current word) :=
  (law.rawItems current word).attach.flatMap (fun need =>
    match need.val.request.operation with
    | .use recipient goods kind =>
        if kind = .necessity ∨ kind = .maintenance then
          goods.flatMap (fun lot =>
            if 0 < lot.2 then accessesTo law current word need recipient lot.1 else [])
        else []
    | _ => [])

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.Discovery
