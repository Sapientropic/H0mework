import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Source.Compiler
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Settlement.Accounting

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

inductive AmountDisposition (proposed : ℚ) where
  | compensation (exactAmount : proposed = plan.transfer)
  | surplus (safe : accountsSafe schedule.programme schedule.provider.amount schedule.payer.amount signal proposed)
      (more : |plan.transfer| < |proposed|)
  | providerShortfall (below : proposed < plan.bounds.1)
  | payerShortfall (above : plan.bounds.2 < proposed)

def classifyAmount (proposed : ℚ) : AmountDisposition schedule signal plan proposed :=
  if same : proposed = plan.transfer then .compensation same
  else if lower : plan.bounds.1 ≤ proposed then
    if upper : proposed ≤ plan.bounds.2 then
      let safe := (envelope_is_exact _ _ plan.computed proposed).mp ⟨lower,upper⟩
      .surplus ((the_original_branch_accounts_are_exactly_the_generated_intervals _ _ _ _ _).mpr safe)
        (plan.unique_least_payment proposed safe same)
    else .payerShortfall (lt_of_not_ge upper)
  else .providerShortfall (lt_of_not_ge lower)

/-- The required-risk channel writes only its computed amount. A larger
safe distribution has a different disposition and needs its own source. -/
def riskClaim (purpose : Port) : Request Party Good Port Technology Instrument :=
  Settlement.issue input.law mechanism.terms.borrower mechanism.terms.lender
    mechanism.terms.instrument purpose plan.transfer

theorem the_original_risk_claim_cannot_contain_an_independent_loading (purpose : Port) :
    (riskClaim schedule signal plan purpose).operation = .issue mechanism.terms.instrument
      (Settlement.debtor mechanism.terms.borrower mechanism.terms.lender plan.transfer)
      (Settlement.creditor mechanism.terms.borrower mechanism.terms.lender plan.transfer)
      (|plan.transfer| / input.law.settlementRate mechanism.terms.instrument) := rfl

theorem a_nonempty_risk_fibre_has_an_exact_feasibility_obstruction
    (issue : QuoteIssue (schedule.rows signal)) (nonempty : schedule.rows signal ≠ []) :
    ¬ ∃ transfer : ℚ,
      accountsSafe schedule.programme schedule.provider.amount schedule.payer.amount signal transfer := by
  rintro ⟨transfer,safe⟩
  exact issue.no_safe_contract nonempty ⟨transfer,
    (the_original_branch_accounts_are_exactly_the_generated_intervals _ _ _ _ _).mp safe⟩

def completedWord (nature : Request Party Good Port Technology Instrument) (purpose : Port) :=
  schedule.programme.word nature ++
    [Settlement.issue input.law mechanism.terms.borrower mechanism.terms.lender mechanism.terms.instrument purpose plan.transfer,
     Settlement.settle input.law mechanism.terms.borrower mechanism.terms.lender mechanism.terms.instrument purpose plan.transfer]

theorem sufficient_payment_has_no_hidden_financial_position
    (nature : Request Party Good Port Technology Instrument) (purpose : Port)
    (issued : input.law.Valid (schedule.programme.after nature)
      (riskClaim schedule signal plan purpose))
    (settled : input.law.Valid
      (Settlement.afterIssue input.law mechanism.terms.borrower mechanism.terms.lender
        mechanism.terms.instrument purpose plan.transfer (schedule.programme.after nature))
      (Settlement.settle input.law mechanism.terms.borrower mechanism.terms.lender
        mechanism.terms.instrument purpose plan.transfer)) :
    (input.law.execute current 0 (completedWord schedule signal plan nature purpose)).final.claims =
      (schedule.programme.after nature).claims := by
  unfold completedWord
  rw [Settlement.appended_price_uses_the_literal_original_body_endpoint]
  exact Settlement.actual_payment_retains_the_entire_original_claim_matrix _ _ _ _ _ _ _ issued settled

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Source
