import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Control.Scenario.Source

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Control.Scenario

open Source.Program

theorem the_risk_reward_is_computed_from_the_experiment_loss :
    exposure = 2 ∧ riskReward = 3 := by decide +kernel

theorem the_native_claim_sizes_use_the_original_settlement_rate :
    premiumUnits = 3 / 2 ∧ coverageUnits = 1 := by decide +kernel

theorem native_contribution_liabilities_are_admitted_before_any_payment
    (opened : Bool) (before : Current) :
    (lawAt opened).Valid before successLiability ∧
      (lawAt opened).Valid before failureLiability := by
  cases opened <;>
    norm_num [lawAt, openLaw, PublicFunction.physicalLaw, law, Trials.Example.law,
      successLiability, failureLiability, premiumUnits, coverageUnits, riskReward, exposure,
      trialInvestment, request, RawLaw.Valid, RawLaw.SignerMatches, RawLaw.operationAllowed,
      RawPolicy.eval, RawLaw.requiredPorts, RawLaw.debit, RawLaw.credit, RawLaw.ClaimGuard,
      NonnegativeBundle, amount] <;> decide +kernel

theorem native_contribution_issuance_extends_the_original_claims
    (opened : Bool) (before : Current) (instrument : Unit) (debtor creditor : Party) :
    ((lawAt opened).step before successLiability).claims instrument debtor creditor =
        before.claims instrument debtor creditor +
          (if (instrument,debtor,creditor) = ((),0,1) then premiumUnits else 0) ∧
      ((lawAt opened).step before failureLiability).claims instrument debtor creditor =
        before.claims instrument debtor creditor +
          (if (instrument,debtor,creditor) = ((),1,0) then coverageUnits else 0) := by
  have admitted := native_contribution_liabilities_are_admitted_before_any_payment opened before
  constructor
  · rw [RawLaw.step, if_pos admitted.1]
    rfl
  · rw [RawLaw.step, if_pos admitted.2]
    rfl

theorem the_native_action_separates_liability_from_material_performance (signal : Nat) :
    policyAction signal = contributionLiabilityWord signal ++ contributionPerformanceWord signal := rfl

theorem a_refused_payment_preserves_every_original_financial_address
    (opened : Bool) (before : Current) (payment : RequestAt)
    (refused : ¬ (lawAt opened).Valid before payment) :
    ((lawAt opened).step before payment).claims = before.claims := by
  rw [(lawAt opened).rejected_preserves_current before payment refused]

set_option maxHeartbeats 800000 in
theorem both_branches_really_fund_and_spend_the_original_investment :
    (mechanism false).funded = true ∧ (mechanism true).funded = true ∧
      (mechanism false).invested = true ∧ (mechanism true).invested = true := by decide +kernel

set_option maxHeartbeats 800000 in
theorem paid_local_observation_separates_the_two_actual_results :
    (mechanism false).paidSignal (discovery 2) = some 0 ∧
      (mechanism true).paidSignal (discovery 2) = some 1 := by decide +kernel

set_option maxHeartbeats 1200000 in
theorem both_banks_receive_real_principal_and_contribution_is_finitely_paid :
    (after false (discovery 2) retaliation).claims () 0 1 = 0 ∧
      (after true (discovery 2) retaliation).claims () 0 1 = 0 ∧
      (after false (discovery 2) retaliation).claims () 0 2 = 1 ∧
      (after true (discovery 2) retaliation).claims () 0 2 = 1 ∧
      (after true (discovery 2) retaliation).stock 1 .material = 21 := by decide +kernel

set_option maxHeartbeats 1200000 in
theorem the_actual_retaliation_has_a_real_bearer_and_cost :
    ((mechanism true).after (discovery 2)).stock 2 .result = 1 ∧
      (after true (discovery 2) retaliation).stock 2 .result = 0 ∧
      (after false (discovery 2) retaliation).stock 2 .result = 0 := by decide +kernel

set_option maxHeartbeats 1200000 in
theorem both_branches_preserve_all_members_life_and_maintenance :
    ∀ actor : Party,
      1 ≤ (after false (discovery 2) retaliation).stock actor .life ∧
      1 ≤ (after false (discovery 2) retaliation).stock actor .maintenance ∧
      1 ≤ (after true (discovery 2) retaliation).stock actor .life ∧
      1 ≤ (after true (discovery 2) retaliation).stock actor .maintenance := by decide +kernel

set_option maxHeartbeats 1200000 in
theorem both_actual_words_pay_life_and_maintenance_in_the_original_inventory (opened : Bool) :
    Exit.Necessity.AllNeedsPaid (lawAt opened) seed [0,1,2]
      (word opened (discovery 2) retaliation) := by
  cases opened <;> decide +kernel

set_option maxHeartbeats 1200000 in
theorem removal_has_strict_physical_gain_after_all_real_costs :
    controlLoss law openLaw (execution false (discovery 2) retaliation).items
        (execution true (discovery 2) retaliation).items .material = 18 ∧
      controlLoss law openLaw (execution false (discovery 2) retaliation).items
        (execution true (discovery 2) retaliation).items .message = 0 ∧
      controlLoss law openLaw (execution false (discovery 2) retaliation).items
        (execution true (discovery 2) retaliation).items .result = 3 := by decide +kernel

set_option maxHeartbeats 1200000 in
theorem every_old_financial_address_is_retained_after_real_repayment :
    (after false (discovery 2) retaliation).claims = seed.claims ∧
      (after true (discovery 2) retaliation).claims = seed.claims := by
  have all : ∀ debtor creditor : Party,
      (after false (discovery 2) retaliation).claims () debtor creditor = seed.claims () debtor creditor ∧
        (after true (discovery 2) retaliation).claims () debtor creditor = seed.claims () debtor creditor := by
    decide +kernel
  constructor <;> funext instrument debtor creditor <;> cases instrument
  · exact (all debtor creditor).1
  · exact (all debtor creditor).2

set_option maxHeartbeats 1600000 in
theorem no_original_member_loses_material_while_control_is_removed :
    ∀ actor : Party, ∀ good : Good,
      (after false (discovery 2) retaliation).stock actor good ≤
        (after true (discovery 2) retaliation).stock actor good := by
  intro actor good
  cases good <;> revert actor <;> decide +kernel

theorem the_paid_contribution_does_not_become_a_permanent_payment_rule (opened : Bool) :
    (mechanism opened).proposal (discovery 2) = commonWork := by
  have signal : ((mechanism opened).run (discovery 2)).inbox (mechanism opened).observer = 2 := by
    cases opened <;> decide +kernel
  unfold Trials.Mechanism.proposal
  rw [signal]
  rfl

set_option maxHeartbeats 1600000 in
theorem the_generated_public_continuation_pays_every_original_member :
    Trials.Mechanism.ContinuationChecks (mechanism true) (discovery 2) := by decide +kernel

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Control.Scenario
