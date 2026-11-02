import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.History.Core

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.History.Discovery

open Program
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : Root.ProgrammeSource.Input Party Good Port Technology Instrument)
  (endpoint : Visit input)
  (access : Access input endpoint)

def reciprocalClaims : List (Reciprocity input endpoint) :=
  (entries input endpoint).filterMap (fun item =>
    let proposal := Reciprocity.claim item
    if proposal.Checks input endpoint access then some proposal else none)

def productiveContributions : List (Reciprocity input endpoint) :=
  (entries input endpoint).flatMap (fun producer =>
    match (producer.raw input).request.operation with
    | .produce operator =>
        (materialGoods input endpoint).flatMap (fun fromGood =>
          (input.law.actualDebit (producer.raw input).before (producer.raw input).request).filterMap (fun used =>
            if used.1.1 = operator ∧ 0 < used.2 then
              (routeBetween input endpoint (access.recipient, fromGood) (operator, used.1.2)
                0 (producer.position input)).bind (fun route =>
                  let proposal := Reciprocity.productiveInput producer operator fromGood used.1.2 route
                  if proposal.Checks input endpoint access then some proposal else none)
            else none))
    | _ => [])

def returnedPayments : List (Reciprocity input endpoint) :=
  (materialGoods input endpoint).flatMap (fun fromGood =>
    (materialGoods input endpoint).filterMap (fun returnGood =>
      (routeBetween input endpoint (access.recipient, fromGood)
        (access.controller input endpoint, returnGood) 0 (entries input endpoint).length).bind (fun route =>
          let proposal := Reciprocity.returnFlow fromGood returnGood route
          if proposal.Checks input endpoint access then some proposal else none)))

def reciprocities : List (Reciprocity input endpoint) :=
  reciprocalClaims input endpoint access ++ productiveContributions input endpoint access ++
    returnedPayments input endpoint access

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.History.Discovery
