import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.History.Access

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.History

open Program
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : Root.ProgrammeSource.Input Party Good Port Technology Instrument)
  (endpoint : Visit input)

inductive Reciprocity
  | productiveInput (producer : Entry input endpoint) (operator : Party)
      (fromGood inputGood : Good) (route : List (RouteLeg input endpoint))
  | returnFlow (fromGood returnGood : Good) (route : List (RouteLeg input endpoint))
  | claim (item : Entry input endpoint)

namespace Reciprocity
variable (access : Access input endpoint)

def ProducerMatches (producer : Entry input endpoint) (operator : Party) : Prop :=
  match (producer.raw input).request.operation with
  | .produce site => site = operator
  | _ => False

instance (producer : Entry input endpoint) (operator : Party) :
    Decidable (ProducerMatches input endpoint producer operator) := by
  unfold ProducerMatches
  cases (producer.raw input).request.operation <;> infer_instance

def ClaimMatches (item : Entry input endpoint) : Prop := match (item.raw input).request.operation with
  | .issue _ debtor beneficiary quantity => debtor = access.recipient ∧
      beneficiary = access.controller input endpoint ∧ 0 < quantity
  | .assign _ debtor sender beneficiary quantity => (debtor = access.recipient ∨ sender = access.recipient) ∧
      beneficiary = access.controller input endpoint ∧ 0 < quantity
  | _ => False

instance (item : Entry input endpoint) : Decidable (ClaimMatches input endpoint access item) := by
  unfold ClaimMatches
  cases (item.raw input).request.operation <;> infer_instance

def Checks : Reciprocity input endpoint → Prop
  | .productiveInput producer operator fromGood inputGood route =>
      ProducerMatches input endpoint producer operator ∧
      input.law.Valid (producer.raw input).before (producer.raw input).request ∧
      access.port ∈ input.law.requiredPorts (producer.raw input).before (producer.raw input).request ∧
      producer.position input ≤ access.access.position input ∧ route ≠ [] ∧
      Follows input endpoint (access.recipient, fromGood) 0 route (operator, inputGood) (producer.position input) ∧
      0 < flowAt (input.law.actualDebit (producer.raw input).before (producer.raw input).request) operator inputGood
  | .returnFlow fromGood returnGood route => route ≠ [] ∧
      Follows input endpoint (access.recipient, fromGood) 0 route (access.controller input endpoint, returnGood)
        (entries input endpoint).length
  | .claim item => input.law.Valid (item.raw input).before (item.raw input).request ∧ ClaimMatches input endpoint access item

instance (proposal : Reciprocity input endpoint) : Decidable (Checks input endpoint access proposal) := by
  cases proposal <;> unfold Checks <;> infer_instance

def financialOrigin : Reciprocity input endpoint → Option (Root.Financial.InstructionOrigin input)
  | .claim item => some (item.origin input)
  | _ => none

end Reciprocity

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.History
