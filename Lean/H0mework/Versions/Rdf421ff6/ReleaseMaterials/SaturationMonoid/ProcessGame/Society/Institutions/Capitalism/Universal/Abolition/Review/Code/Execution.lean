import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Review.Code
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Review.MicroBudget

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Admission.FeeCode

open Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (code : FeeCode (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))
  (law : RawLaw Party Good Port Technology Instrument)
  (current : RawCurrent Party Good Technology Instrument)

theorem source_step_has_the_exact_original_debit (person : Party) (good : Good) :
    (law.step current code.request).stock person good = current.stock person good -
      if law.Valid current code.request ∧ (person, good) = (code.scope.payer, code.scope.good)
      then code.scope.amount else 0 := by
  by_cases accepted : law.Valid current code.request
  · simp [RawLaw.step, accepted, RawLaw.paidStep, RawLaw.debit, RawLaw.credit,
      code.scope.operation, locate, flowAt, amount, eq_comm]
  · simp [RawLaw.step, accepted]

theorem this_fee_step_cannot_mint_stock (person : Party) (good : Good) :
    (law.step current code.request).stock person good ≤ current.stock person good := by
  rw [code.source_step_has_the_exact_original_debit law current person good]
  split
  · exact sub_le_self _ code.scope.positive.le
  · simp

theorem source_step_preserves_claims_technology_and_period :
    (law.step current code.request).claims = current.claims ∧
      (law.step current code.request).technology = current.technology ∧
      (law.step current code.request).clock = current.clock ∧
      (law.step current code.request).round = current.round := by
  by_cases accepted : law.Valid current code.request
  · simp only [RawLaw.step, if_pos accepted, RawLaw.paidStep, RawLaw.nextClaims,
      code.scope.operation]
    simp
  · simp only [RawLaw.step, if_neg accepted]
    simp

/-- This case split is the existing source payment attempt. Permission
failure remains its exact cause; no independence or no-veto claim is added. -/
theorem the_source_attempt_pays_one_fee_or_keeps_its_exact_blocker :
    match Review.attempt law code.request code.scope current with
    | .inl payment =>
        law.step current code.request = payment.microNext ∧
        (law.step current code.request).stock code.scope.payer code.scope.good + code.scope.amount =
          current.stock code.scope.payer code.scope.good ∧
        Review.physicalBudget code.request code.scope current =
          Review.physicalBudget code.request code.scope (law.step current code.request) + 1
    | .inr _obstruction =>
        law.step current code.request = current ∧
        (current.stock code.scope.payer code.scope.good < code.scope.amount ∨
          law.operationAllowed current code.request ≠ true ∨
          ∃ port ∈ law.requiredPorts current code.request,
            law.allowed current.technology port code.request.signer ≠ true ∧
              law.controller current.technology port ∉ code.request.consents) := by
  cases produced : Review.attempt law code.request code.scope current with
  | inl payment => exact ⟨rfl, payment.micro_stock_balance code.scope, payment.micro_budget_debits_one code.scope⟩
  | inr obstruction => exact ⟨obstruction.actual_source_preserves_current, obstruction.exact_cause⟩

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Admission.FeeCode

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Admission.FeeCode.source_step_has_the_exact_original_debit
#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Admission.FeeCode.the_source_attempt_pays_one_fee_or_keeps_its_exact_blocker
