import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.Access

/-! The reverse leg is actual productive contribution, actual payment or
an original financial right.  An unpaid claim can constitute the relation;
no profit, replenished reserve or future successful cycle is assumed. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel

open Program
universe u
variable {Party Good Port Technology Instrument : Type u}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (law : RawLaw Party Good Port Technology Instrument)
  (current : RawCurrent Party Good Technology Instrument)
  (word : RawEvent Party Good Port Technology Instrument)

inductive ReciprocityProposal
  | productiveInput (producer : OriginalItem law current word) (operator : Party)
      (fromGood inputGood : Good) (route : List (RouteLeg law current word))
  | returnFlow (fromGood returnGood : Good) (route : List (RouteLeg law current word))
  | claim (item : OriginalItem law current word)

namespace ReciprocityProposal
variable (access : AccessProposal law current word)

def ProducerMatches (producer : OriginalItem law current word) (operator : Party) : Prop :=
  match producer.val.request.operation with
  | .produce site => site = operator
  | _ => False

instance (producer : OriginalItem law current word) (operator : Party) :
    Decidable (ProducerMatches law current word producer operator) := by
  unfold ProducerMatches
  cases producer.val.request.operation <;> infer_instance

def ClaimMatches (item : OriginalItem law current word) : Prop :=
  match item.val.request.operation with
  | .issue _ debtor beneficiary quantity => debtor = access.recipient ∧
      beneficiary = access.controller law current word ∧ 0 < quantity
  | .assign _ debtor sender beneficiary quantity => (debtor = access.recipient ∨ sender = access.recipient) ∧
      beneficiary = access.controller law current word ∧ 0 < quantity
  | _ => False

instance (item : OriginalItem law current word) :
    Decidable (ClaimMatches law current word access item) := by
  unfold ClaimMatches
  cases item.val.request.operation <;> infer_instance

def Checks : ReciprocityProposal law current word → Prop
  | .productiveInput producer operator fromGood inputGood route =>
      ProducerMatches law current word producer operator ∧
      law.Valid producer.val.before producer.val.request ∧
      access.port ∈ law.requiredPorts producer.val.before producer.val.request ∧
      producer.val.index ≤ access.access.val.index ∧ route ≠ [] ∧
      Follows law current word (access.recipient, fromGood) 0 route
        (operator, inputGood) producer.val.index ∧
      0 < flowAt (law.actualDebit producer.val.before producer.val.request) operator inputGood
  | .returnFlow fromGood returnGood route =>
      route ≠ [] ∧ Follows law current word (access.recipient, fromGood) 0 route
        (access.controller law current word, returnGood) word.length
  | .claim item => law.Valid item.val.before item.val.request ∧ ClaimMatches law current word access item

instance (proposal : ReciprocityProposal law current word) :
    Decidable (Checks law current word access proposal) := by
  cases proposal <;> unfold Checks <;> infer_instance

/-- This is the existing financial instruction, not a new claim registry.
The root binding must consume its original native origin allocation. -/
def financialOrigin : ReciprocityProposal law current word → Option (OriginalItem law current word)
  | .claim item => some item
  | _ => none
end ReciprocityProposal

#print axioms ReciprocityProposal.instDecidableChecks

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel
