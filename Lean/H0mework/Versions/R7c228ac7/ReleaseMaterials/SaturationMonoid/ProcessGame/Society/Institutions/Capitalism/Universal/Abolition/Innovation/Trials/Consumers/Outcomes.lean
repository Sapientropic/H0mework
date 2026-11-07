import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Trials.Consumers.Example
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Trials.Source.Admission
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Trials.Source.Pricing

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Trials.Example

open Source.Program

def productionAccepted : Bool := match (mechanism 12 1).generate success with
  | .accepted _ => true | .failed _ => false
def failureVisible : Bool := match (mechanism 12 1).generate failure with
  | .failed (.service _) => true | _ => false
def unfundedVisible : Bool := match (mechanism 0 1).generate noFunds with
  | .failed (.unfunded _) => true | _ => false
def unpaidObservationVisible : Bool := match (mechanism 12 0).generate noCommunication with
  | .failed (.observation _) => true | _ => false
def riskAdmitted : Bool := match (mechanism 12 1).admit with
  | .admitted _ => true | _ => false

theorem the_mechanism_is_admitted_before_either_unknown_event : riskAdmitted = true := by
  decide +kernel

theorem real_production_is_generated_after_the_paid_local_success_signal :
    productionAccepted = true ∧ (mechanism 12 1).paidSignal success = some 1 ∧
      (mechanism 12 1).proposal success = work := by
  decide +kernel

theorem failed_investment_remains_a_real_loss_with_an_exact_bearer :
    failureVisible = true ∧ (mechanism 12 1).observed failure = true ∧
      (mechanism 12 1).paidSignal failure = some 0 ∧
      (mechanism 12 1).investmentLoss 0 .material = 3 ∧
      (mechanism 12 1).investmentLoss 1 .material = 0 ∧
      ((mechanism 12 1).after failure).stock 0 .material = 3 := by
  decide +kernel

theorem the_original_claims_and_real_denominated_principal_survive_success_and_failure :
    (mechanism 12 1).code.initial.claims () 0 1 = 2 ∧
      ((mechanism 12 1).after success).claims () 0 1 = 5 ∧
      ((mechanism 12 1).after failure).claims () 0 1 = 5 ∧
      law.settlementUnit () = .material ∧ law.settlementRate () = 2 ∧
      (mechanism 12 1).fundingAfter.stock 0 .material = 6 ∧
      (mechanism 12 1).fundingAfter.stock 1 .material = 6 := by
  decide +kernel

theorem missing_material_does_not_turn_issuance_into_funding_or_a_trial :
    unfundedVisible = true ∧ (mechanism 0 1).fundingReceipt = none ∧
      (mechanism 0 1).invested = false ∧ (mechanism 0 1).paidSignal noFunds = none ∧
      ((mechanism 0 1).after noFunds).stock 0 .result = 0 ∧
      ((mechanism 0 1).after noFunds).stock 0 .material = 0 ∧
      ((mechanism 0 1).after noFunds).claims () 0 1 = 5 := by
  decide +kernel

theorem an_actual_hidden_success_is_not_unpaid_local_knowledge :
    unpaidObservationVisible = true ∧
      ((mechanism 12 0).after noCommunication).stock 0 .result = 1 ∧
      (mechanism 12 0).observed noCommunication = false ∧
      (mechanism 12 0).paidSignal noCommunication = none ∧
      (mechanism 12 0).proposal noCommunication = [] ∧
      ((mechanism 12 0).sentFrame noCommunication).sent = [] := by
  decide +kernel

abbrev zeroCostRead : Mechanism Party Good Bool Nat Unit :=
  { mechanism 12 1 with code := { code 12 1 with sendCost := fun _ _ => [] } }

def zeroCostRejected : Bool := match zeroCostRead.generate (shock 1) with
  | .failed (.observation _) => true | _ => false

theorem a_zero_cost_packet_cannot_be_a_paid_trial_signal :
    (zeroCostRead.sentFrame (shock 1)).sent.isEmpty = false ∧
      zeroCostRead.observed (shock 1) = false ∧ zeroCostRead.paidSignal (shock 1) = none ∧
      zeroCostRejected = true := by
  decide +kernel

theorem both_trial_outcomes_keep_each_intermediate_life_and_maintenance_reserve :
    Safety.Safe (mechanism 12 1) success ∧ Safety.Safe (mechanism 12 1) failure := by
  decide +kernel

theorem both_actual_outcomes_pay_every_original_persons_life_and_maintenance :
    Exit.Necessity.AllNeedsPaid law (mechanism 12 1).code.initial (mechanism 12 1).code.parties
        ((mechanism 12 1).word success) ∧
      Exit.Necessity.AllNeedsPaid law (mechanism 12 1).code.initial (mechanism 12 1).code.parties
        ((mechanism 12 1).word failure) := by
  decide +kernel

theorem failure_does_not_satisfy_the_continuation_success_contract :
    ¬ (mechanism 12 1).ContinuationChecks failure := by
  unfold Mechanism.ContinuationChecks
  decide +kernel

abbrev individualOnly : Mechanism Party Good Bool Nat Unit :=
  { mechanism 12 1 with policy := fun key _ => if key.2 = 1 then [produce, life 0, maintain 0] else [] }

def missingMemberVisible : Bool := match individualOnly.generate (shock 1) with
  | .failed (.unpaidNecessity person _ _) => decide (person = 1)
  | _ => false

theorem paying_only_the_task_borrower_cannot_masquerade_as_full_society_continuation :
    SaturationMonoid.ProcessGame.Society.PublicFunction.ServiceAdequate individualOnly.code.law
        (individualOnly.after (shock 1)) individualOnly.code.task (individualOnly.proposal (shock 1)) ∧
      individualOnly.Productive (shock 1) ∧ missingMemberVisible = true ∧
      ¬ individualOnly.ContinuationChecks (shock 1) := by
  unfold Mechanism.ContinuationChecks
  decide +kernel

#print axioms the_mechanism_is_admitted_before_either_unknown_event
#print axioms real_production_is_generated_after_the_paid_local_success_signal
#print axioms failed_investment_remains_a_real_loss_with_an_exact_bearer
#print axioms the_original_claims_and_real_denominated_principal_survive_success_and_failure
#print axioms missing_material_does_not_turn_issuance_into_funding_or_a_trial
#print axioms an_actual_hidden_success_is_not_unpaid_local_knowledge
#print axioms a_zero_cost_packet_cannot_be_a_paid_trial_signal
#print axioms both_trial_outcomes_keep_each_intermediate_life_and_maintenance_reserve
#print axioms both_actual_outcomes_pay_every_original_persons_life_and_maintenance
#print axioms failure_does_not_satisfy_the_continuation_success_contract
#print axioms paying_only_the_task_borrower_cannot_masquerade_as_full_society_continuation

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Trials.Example
