import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Review.Code.Independent

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Fees

open Source.Program

variable {Party Good Port Technology Instrument : Type}

/-- Review fees use the original positive single-cell fee grammar. This
parser does not judge the legality of other physical operations. -/
def scope? (request : Request Party Good Port Technology Instrument) : Option (Review.FeeScope request) :=
  match original : request.operation with
  | .use payer [(good, amount)] .external =>
      if positive : 0 < amount then some ⟨payer, good, amount, original, positive⟩ else none
  | _ => none

theorem every_positive_original_fee_is_recognized
    {request : Request Party Good Port Technology Instrument} (scope : Review.FeeScope request) :
    ∃ generated, scope? request = some generated := by
  rcases request with ⟨signer, consents, purpose, gates, operation⟩
  rcases scope with ⟨payer, good, amount, original, positive⟩
  change operation = .use payer [(good, amount)] .external at original
  subst operation
  refine ⟨⟨payer, good, amount, rfl, positive⟩, ?_⟩
  simp only [scope?, dif_pos positive]

inductive ParsedAt (request : Request Party Good Port Technology Instrument) : Type
  | accepted (scope : Review.FeeScope request) (generated : scope? request = some scope)
  | rejected (generated : scope? request = none) (noPositiveFeeScope : IsEmpty (Review.FeeScope request))

/-- Rejection keeps the full indexed original request and refutes only
its use as a positive review fee, never its material feasibility. -/
def parse (request : Request Party Good Port Technology Instrument) : ParsedAt request :=
  match produced : scope? request with
  | some scope => .accepted scope produced
  | none => .rejected produced ⟨fun scope => by
      obtain ⟨generated, selected⟩ := every_positive_original_fee_is_recognized scope
      cases produced.symm.trans selected⟩

def originalCode {request : Request Party Good Port Technology Instrument}
    (scope : Review.FeeScope request) : Admission.FeeCode
      (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) :=
  ⟨request, scope⟩

theorem the_parsed_fee_keeps_the_exact_source_request
    {request : Request Party Good Port Technology Instrument} (scope : Review.FeeScope request) :
    (originalCode scope).request = request := rfl

theorem its_independent_fee_keeps_operation_signer_and_positive_amount
    {request : Request Party Good Port Technology Instrument} (scope : Review.FeeScope request) :
    (originalCode scope).withoutConsents.request.operation = request.operation ∧
    (originalCode scope).withoutConsents.request.signer = request.signer ∧
    (originalCode scope).withoutConsents.request.consents = [] ∧
    (originalCode scope).withoutConsents.scope.amount = scope.amount ∧
    0 < (originalCode scope).withoutConsents.scope.amount :=
  ⟨rfl, rfl, rfl, rfl, scope.positive⟩

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Fees

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Fees.every_positive_original_fee_is_recognized
#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Fees.parse
