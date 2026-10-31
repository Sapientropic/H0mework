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
  (access : AccessProposal law current word)

def reciprocalClaims : List (ReciprocityProposal law current word) :=
  (law.rawItems current word).attach.filterMap (fun item =>
    let proposal := ReciprocityProposal.claim item
    if proposal.Checks law current word access then some proposal else none)

def productiveContributions : List (ReciprocityProposal law current word) :=
  (law.rawItems current word).attach.flatMap (fun producer =>
    match producer.val.request.operation with
    | .produce operator =>
        (materialGoods law current word).flatMap (fun fromGood =>
          (law.actualDebit producer.val.before producer.val.request).filterMap (fun used =>
            if used.1.1 = operator ∧ 0 < used.2 then
              (routeBetween law current word (access.recipient, fromGood) (operator, used.1.2)
                0 producer.val.index).bind (fun route =>
                  let proposal := ReciprocityProposal.productiveInput producer operator fromGood used.1.2 route
                  if proposal.Checks law current word access then some proposal else none)
            else none))
    | _ => [])

def returnedPayments : List (ReciprocityProposal law current word) :=
  (materialGoods law current word).flatMap (fun fromGood =>
    (materialGoods law current word).filterMap (fun returnGood =>
      (routeBetween law current word (access.recipient, fromGood)
        (access.controller law current word, returnGood) 0 word.length).bind (fun route =>
          let proposal := ReciprocityProposal.returnFlow fromGood returnGood route
          if proposal.Checks law current word access then some proposal else none)))

def reciprocities : List (ReciprocityProposal law current word) :=
  reciprocalClaims law current word access ++ productiveContributions law current word access ++
    returnedPayments law current word access

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.Discovery
