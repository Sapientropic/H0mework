import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Review.Code.Execution

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Admission.FeeCode

open Source.Program

variable {Party Good Port Technology Instrument : Type}
  (code : FeeCode (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))

def withoutConsents : FeeCode (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) where
  request := { code.request with consents := [] }
  scope := ⟨code.scope.payer, code.scope.good, code.scope.amount, code.scope.operation, code.scope.positive⟩

theorem the_original_fee_and_operation_are_kept :
    code.withoutConsents.scope.payer = code.scope.payer ∧
      code.withoutConsents.scope.good = code.scope.good ∧
      code.withoutConsents.scope.amount = code.scope.amount ∧
      code.withoutConsents.request.operation = code.request.operation ∧
      code.withoutConsents.request.signer = code.request.signer ∧
      code.withoutConsents.request.consents = [] := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

variable [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (law : RawLaw Party Good Port Technology Instrument)
  (current : RawCurrent Party Good Technology Instrument)

def independentAttempt := Review.attempt law code.withoutConsents.request code.withoutConsents.scope current

omit [DecidableEq Instrument] in
theorem an_independent_valid_fee_is_the_generated_payment
    (accepted : law.Valid current code.withoutConsents.request) :
    code.independentAttempt law current = .inl (⟨accepted⟩ : Review.PaymentAt law code.withoutConsents.request current) := by
  have permission := (Review.valid_iff_permission_and_stock law code.withoutConsents.request code.withoutConsents.scope current).mp accepted
  change Review.attempt law code.withoutConsents.request code.withoutConsents.scope current = _
  rw [Review.attempt, dif_pos permission.2, dif_pos permission.1]

omit [DecidableEq Instrument] in
theorem every_independently_paid_required_port_has_actual_permission
    (payment : Review.PaymentAt law code.withoutConsents.request current) :
    ∀ port ∈ law.requiredPorts current code.withoutConsents.request,
      law.allowed current.technology port code.request.signer = true := by
  have permission := ((Review.valid_iff_permission_and_stock law code.withoutConsents.request code.withoutConsents.scope current).mp
    payment.accepted).1.2
  intro port required
  rcases permission port required with allowed | consent
  · exact allowed
  · exact (List.not_mem_nil consent).elim

omit [DecidableEq Good] [DecidableEq Instrument] in
theorem independent_rejection_keeps_the_exact_original_cause
    (blocked : Review.Blockage law code.withoutConsents.request code.withoutConsents.scope current) :
    current.stock code.scope.payer code.scope.good < code.scope.amount ∨
      law.operationAllowed current code.withoutConsents.request ≠ true ∨
        ∃ port ∈ law.requiredPorts current code.withoutConsents.request,
          law.allowed current.technology port code.request.signer ≠ true := by
  rcases blocked.exact_cause with stock | operation | ⟨port, required, denied, _consent⟩
  · exact Or.inl stock
  · exact Or.inr (Or.inl operation)
  · exact Or.inr (Or.inr ⟨port, required, denied⟩)

#print axioms independentAttempt
#print axioms an_independent_valid_fee_is_the_generated_payment
#print axioms every_independently_paid_required_port_has_actual_permission
#print axioms independent_rejection_keeps_the_exact_original_cause

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Admission.FeeCode
