import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Consumers.Scenario
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Control.Scenario.Capital
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Control.Consumers.Counterexamples

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Realized

open Source.Program
open Control.Scenario

def actualSuccess (opened : Bool) : Bool :=
  match (mechanism opened).paidSignal (discovery 2) with
  | some signal => Consumers.successSignal signal
  | none => false

def actualRow (opened : Bool) : RiskRow :=
  ⟨1 / 2, actualSuccess opened,
    max 0 (-Control.net (lawAt opened)
      ((lawAt opened).rawItems seed ((mechanism opened).deliveredFrame (discovery 2)).word) .material)⟩

/-- Only the two finite risk settlements enter this restriction of the
original inventory. Production, loan principal and rent are excluded. -/
def isRiskSettlement (action : RequestAt) : Bool :=
  match action.operation with
  | .settle _ debtor creditor units => decide
      ((debtor = 0 ∧ creditor = 1 ∧ units = premiumUnits) ∨
        (debtor = 1 ∧ creditor = 0 ∧ units = coverageUnits))
  | _ => false

def riskItems (opened : Bool) :=
  (execution opened (discovery 2) retaliation).items.filter fun item => isRiskSettlement item.request

def isRiskLiability (action : RequestAt) : Bool :=
  match action.operation with
  | .issue _ debtor creditor units => decide
      ((debtor = 0 ∧ creditor = 1 ∧ units = premiumUnits) ∨
        (debtor = 1 ∧ creditor = 0 ∧ units = coverageUnits))
  | _ => false

def liabilityItems (opened : Bool) :=
  (execution opened (discovery 2) retaliation).items.filter fun item => isRiskLiability item.request

def nativeSignature (action : RequestAt) :
    (Party × List Party) × (Bool × List Bool) × Option ((Bool × Party) × (Party × ℚ)) :=
  ((action.signer,action.consents), (action.purpose,action.gates),
    match action.operation with
    | .issue _ debtor creditor units => some ((true,debtor),(creditor,units))
    | .settle _ debtor creditor units => some ((false,debtor),(creditor,units))
    | _ => none)

def bankRiskCash (opened : Bool) : ℚ :=
  (lawAt opened).totalCredit (riskItems opened) 1 .material -
    (lawAt opened).totalDebit (riskItems opened) 1 .material

theorem loan_principal_production_and_rent_do_not_enter_risk_cash :
    isRiskSettlement repay = false ∧ isRiskSettlement rent = false ∧
      ∀ actor : Party, isRiskSettlement (production actor) = false := by decide +kernel

def actualLiabilityWord (opened : Bool) : RawEvent Party Good Bool Nat Unit :=
  match (mechanism opened).paidSignal (discovery 2) with
  | some signal => contributionLiabilityWord signal.val
  | none => []

def actualRiskPaymentWord (opened : Bool) : RawEvent Party Good Bool Nat Unit :=
  match (mechanism opened).paidSignal (discovery 2) with
  | some signal => if signal.val = 1 then [successPayment]
      else if signal.val = 0 then [failureCoverage] else []
  | none => []

theorem the_settlement_restriction_keeps_its_original_inventory (opened : Bool) :
    ∀ item ∈ riskItems opened,
      item ∈ (execution opened (discovery 2) retaliation).items ∧
        isRiskSettlement item.request = true := by
  intro item original
  exact List.mem_filter.mp original

theorem the_quote_is_the_source_reward_and_the_failure_is_a_real_loss :
    Consumers.reward = riskReward ∧ Consumers.reward = 3 ∧ exposure = 2 :=
  ⟨Consumers.the_compensation_is_the_source_derived_finite_reward.1,
    Consumers.the_compensation_is_the_source_derived_finite_reward.2,
    the_risk_reward_is_computed_from_the_experiment_loss.1⟩

set_option maxHeartbeats 1000000 in
theorem the_actual_paid_observations_generate_the_realized_rows :
    actualRow false = ⟨1 / 2, false, 2⟩ ∧
      actualRow true = ⟨1 / 2, true, 0⟩ := by decide +kernel

theorem the_unquoted_actual_results_match_the_original_forecast_fibers (opened : Bool) :
    actualRow opened ∈ Consumers.rows := by
  rw [Consumers.the_original_trials_generate_the_risk_rows]
  cases opened
  · rw [the_actual_paid_observations_generate_the_realized_rows.1]
    exact List.mem_cons_self
  · rw [the_actual_paid_observations_generate_the_realized_rows.2]
    exact List.mem_cons_of_mem _ List.mem_cons_self

set_option maxHeartbeats 1400000 in
set_option synthInstance.maxSize 1024 in
theorem paid_signals_generate_one_actual_native_liability_and_risk_payment (opened : Bool) :
    (riskItems opened).map (nativeSignature ∘ ExecutionItem.request) =
        (actualRiskPaymentWord opened).map nativeSignature ∧
      (liabilityItems opened).map (nativeSignature ∘ ExecutionItem.request) =
        (actualLiabilityWord opened).map nativeSignature ∧
      (riskItems opened).length = 1 ∧ (liabilityItems opened).length = 1 ∧
      (∀ item ∈ riskItems opened, (lawAt opened).Valid item.before item.request) ∧
      (∀ item ∈ liabilityItems opened, (lawAt opened).Valid item.before item.request) := by
  cases opened <;> refine ⟨?_,?_,?_,?_,?_,?_⟩ <;> decide +kernel

set_option maxHeartbeats 1400000 in
theorem the_original_risk_settlements_pay_exactly_the_finite_quote :
    bankRiskCash true = 3 ∧ bankRiskCash false = -2 := by decide +kernel

theorem actual_risk_cash_is_the_forecast_cash_change (opened : Bool) :
    bankRiskCash opened = cashChange (actualRow opened) Consumers.reward := by
  rw [the_quote_is_the_source_reward_and_the_failure_is_a_real_loss.2.1]
  cases opened
  · rw [the_original_risk_settlements_pay_exactly_the_finite_quote.2,
      the_actual_paid_observations_generate_the_realized_rows.1]
    rfl
  · rw [the_original_risk_settlements_pay_exactly_the_finite_quote.1,
      the_actual_paid_observations_generate_the_realized_rows.2]
    rfl

theorem the_realized_risk_flows_recover_the_declared_participation_value :
    (1 / 2 : ℚ) * bankRiskCash false + (1 / 2 : ℚ) * bankRiskCash true =
        expectedChange Consumers.rows Consumers.reward ∧
      (1 / 2 : ℚ) * bankRiskCash false + (1 / 2 : ℚ) * bankRiskCash true = 1 / 2 := by
  rw [the_original_risk_settlements_pay_exactly_the_finite_quote.1,
    the_original_risk_settlements_pay_exactly_the_finite_quote.2,
    Consumers.the_funder_selects_participation_before_any_actual_event.2]
  norm_num

theorem paid_contribution_preserves_old_debt_and_cannot_generate_permanent_control :
    (after true (discovery 2) retaliation).claims () 0 2 = 1 ∧
      (mechanism true).proposal (discovery 2) = commonWork ∧
      ∀ later, ¬ Nonempty (Source.ProgrammeControl.Kernel.CapitalRelationKernel openLaw
        (after true (discovery 2) retaliation) later) :=
  ⟨both_banks_receive_real_principal_and_contribution_is_finitely_paid.2.2.2.1,
    the_paid_contribution_does_not_become_a_permanent_payment_rule true,
    the_open_rule_cannot_generate_another_full_capital_relation _⟩

theorem a_real_cash_failure_keeps_the_original_risk_claim_and_old_owner :
    ¬ law.Valid (Control.Consumers.pendingContribution false) failureCoverage ∧
      (law.step (Control.Consumers.pendingContribution false) failureCoverage).claims () 1 0 = 1 ∧
      (law.step (Control.Consumers.pendingContribution false) failureCoverage).claims () 0 2 = 1 :=
  ⟨Control.Consumers.refused_success_and_failure_payments_leave_the_native_claims_visible.2.1,
    Control.Consumers.refused_success_and_failure_payments_leave_the_native_claims_visible.2.2.2.1,
    Control.Consumers.refused_success_and_failure_payments_leave_the_native_claims_visible.2.2.2.2.2⟩

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Realized
