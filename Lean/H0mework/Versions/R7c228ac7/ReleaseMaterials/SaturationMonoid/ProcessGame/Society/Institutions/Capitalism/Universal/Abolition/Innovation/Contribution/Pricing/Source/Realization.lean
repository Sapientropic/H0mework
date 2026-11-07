import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Source.Authority

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Source

open Source.Program
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : Root.ProgrammeSource.Input Party Good Port Technology Instrument}
  {current : RawCurrent Party Good Technology Instrument} {members : List Party}
  {budget : Nat} {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  (schedule : Schedule input current members budget mechanism)
  (signal : Fin mechanism.code.signals) (plan : Quote (schedule.rows signal))
  (nature : schedule.programme.QuotedNature) (purpose : Port)

local notation "beforePayment" => schedule.programme.after nature.val
local notation "issue" => riskClaim schedule signal plan purpose
local notation "settle" => Settlement.settle input.law mechanism.terms.borrower mechanism.terms.lender
  mechanism.terms.instrument purpose plan.transfer
local notation "unit" => input.law.settlementUnit mechanism.terms.instrument

theorem actual_full_accounts_are_the_original_trial_plus_its_generated_payment
    (positive : 0 < input.law.settlementRate mechanism.terms.instrument)
    (different : mechanism.terms.borrower ≠ mechanism.terms.lender)
    (issued : input.law.Valid beforePayment issue)
    (settled : input.law.Valid
      (Settlement.afterIssue input.law mechanism.terms.borrower mechanism.terms.lender
        mechanism.terms.instrument purpose plan.transfer beforePayment) settle) :
    Arithmetic.completeIncome input.law
        (input.law.rawItems current (completedWord schedule signal plan nature.val purpose))
        mechanism.terms.lender unit = income schedule.programme nature mechanism.terms.lender unit + plan.transfer ∧
      Arithmetic.completeIncome input.law
        (input.law.rawItems current (completedWord schedule signal plan nature.val purpose))
        mechanism.terms.borrower unit = income schedule.programme nature mechanism.terms.borrower unit - plan.transfer := by
  have effects := Settlement.the_generated_price_enters_both_original_full_accounts input.law beforePayment
    mechanism.terms.borrower mechanism.terms.lender mechanism.terms.instrument purpose plan.transfer
    issued settled positive different
  have lenderEffect : Arithmetic.completeIncome input.law
      (input.law.rawItems beforePayment [issue,settle]) mechanism.terms.lender unit = plan.transfer := by
    rw [Arithmetic.complete_income_is_the_original_full_account]
    exact effects.1
  have payerEffect : Arithmetic.completeIncome input.law
      (input.law.rawItems beforePayment [issue,settle]) mechanism.terms.borrower unit = -plan.transfer := by
    rw [Arithmetic.complete_income_is_the_original_full_account]
    exact effects.2
  unfold completedWord
  rw [Arithmetic.completeIncome_word_append,Arithmetic.completeIncome_word_append]
  change income schedule.programme nature mechanism.terms.lender unit +
      Arithmetic.completeIncome input.law (input.law.rawItems beforePayment [issue,settle])
        mechanism.terms.lender unit = _ ∧
    income schedule.programme nature mechanism.terms.borrower unit +
      Arithmetic.completeIncome input.law (input.law.rawItems beforePayment [issue,settle])
        mechanism.terms.borrower unit = _
  rw [lenderEffect,payerEffect]
  exact ⟨rfl,(sub_eq_add_neg _ _).symm⟩

theorem actual_risk_settlement_reaches_both_source_generated_outside_options
    (observed : schedule.programme.paidSignal nature.val = some signal)
    (positive : 0 < input.law.settlementRate mechanism.terms.instrument)
    (different : mechanism.terms.borrower ≠ mechanism.terms.lender)
    (issued : input.law.Valid beforePayment issue)
    (settled : input.law.Valid
      (Settlement.afterIssue input.law mechanism.terms.borrower mechanism.terms.lender
        mechanism.terms.instrument purpose plan.transfer beforePayment) settle) :
    schedule.provider.amount ≤ Arithmetic.completeIncome input.law
        (input.law.rawItems current (completedWord schedule signal plan nature.val purpose))
        mechanism.terms.lender unit ∧
      schedule.payer.amount ≤ Arithmetic.completeIncome input.law
        (input.law.rawItems current (completedWord schedule signal plan nature.val purpose))
        mechanism.terms.borrower unit := by
  have safe := a_generated_price_preserves_every_matching_original_risk_branch schedule signal plan nature observed
  rw [(actual_full_accounts_are_the_original_trial_plus_its_generated_payment
    schedule signal plan nature purpose positive different issued settled).1,
    (actual_full_accounts_are_the_original_trial_plus_its_generated_payment
      schedule signal plan nature purpose positive different issued settled).2]
  exact safe

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Source
