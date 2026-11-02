import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Trials.Source.Renewal
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Consumers.Scenario
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Control.Scenario.Capital

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Trials.Renewal

open Source.Program
open Control.Scenario

/-- Each prototype is actually consumed by testing; the next experiment
cannot read a retained successful prototype as its new result. -/
abbrev firstProgramme : Mechanism Party Good Bool Nat Unit :=
  { mechanism true with closing :=
      [request 0 (.use 0 [(.result,2)] .contribution),
       request 1 (.use 1 [(.result,1)] .contribution),
       request 2 (.use 2 [(.result,1)] .contribution), migrationFee] }

abbrev secondProgramme := firstProgramme.nextTrial (discovery 1)

def firstAccepted : Bool := match firstProgramme.generate (discovery 1) with
  | .accepted _ => true | _ => false
def secondAccepted : Bool := match secondProgramme.generate (discovery 2) with
  | .accepted _ => true | _ => false

set_option maxHeartbeats 1800000 in
theorem two_fresh_paid_trials_generate_successive_technologies :
    firstAccepted = true ∧ secondAccepted = true ∧
      (firstProgramme.after (discovery 1)).technology = 1 ∧
      (secondProgramme.after (discovery 2)).technology = 2 ∧
      firstProgramme.paidSignal (discovery 1) = some 1 ∧
      secondProgramme.paidSignal (discovery 2) = some ⟨1, by decide +kernel⟩ ∧
      secondProgramme.code.initial.stock 0 .result = 0 := by decide +kernel

theorem the_second_discovery_was_not_in_either_quoted_menu :
    SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Event.adversary (discovery 2) ∉
        firstProgramme.code.eventAlphabet ∧
      SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Event.adversary (discovery 2) ∉
        secondProgramme.code.eventAlphabet :=
  ⟨the_actual_new_technology_was_not_in_the_quoted_menu,
    the_actual_new_technology_was_not_in_the_quoted_menu⟩

set_option maxHeartbeats 1600000 in
theorem the_next_trial_carries_the_old_debt_and_pays_again :
    secondProgramme.code.initial.claims () 0 2 = 1 ∧
      (secondProgramme.after (discovery 2)).claims () 0 2 = 1 ∧
      firstProgramme.investmentLoss 0 .material = 3 ∧
      secondProgramme.investmentLoss 0 .material = 3 ∧
      seed.stock 0 .message - secondProgramme.code.initial.stock 0 .message = 3 ∧
      secondProgramme.code.initial.stock 0 .message -
        (secondProgramme.after (discovery 2)).stock 0 .message = 3 ∧
      secondProgramme.code.initial.clock = 3 ∧
      (secondProgramme.next (discovery 2)).clock = 4 := by decide +kernel

def renewedBelief (_ : secondProgramme.QuotedNature) : ℚ := 1 / 2
def renewedSignal (signal : Fin secondProgramme.code.signals) : Bool := decide (signal.val = 1)

set_option maxHeartbeats 1600000 in
theorem the_second_quote_is_recomputed_from_its_own_funded_and_paid_prefix :
    Contribution.forecastRows secondProgramme renewedBelief renewedSignal .material =
        [⟨1 / 2,false,2⟩,⟨1 / 2,true,0⟩] ∧
      Contribution.quotedReward secondProgramme renewedBelief renewedSignal .material 0 (1 / 2) = 3 := by
  decide +kernel

set_option maxHeartbeats 1800000 in
theorem both_trials_pay_every_original_person_and_keep_their_reserves :
    Safety.Safe firstProgramme (discovery 1) ∧ Safety.Safe secondProgramme (discovery 2) ∧
      Exit.Necessity.AllNeedsPaid firstProgramme.code.law firstProgramme.code.initial
        firstProgramme.code.parties (firstProgramme.word (discovery 1)) ∧
      Exit.Necessity.AllNeedsPaid secondProgramme.code.law secondProgramme.code.initial
        secondProgramme.code.parties (secondProgramme.word (discovery 2)) := by decide +kernel

abbrev noSecondFunding : Mechanism Party Good Bool Nat Unit :=
  { secondProgramme with funding := [] }
abbrev noSecondPaidRead : Mechanism Party Good Bool Nat Unit :=
  { secondProgramme with code := { secondProgramme.code with sendCost := fun _ _ => [] } }

def newFundingFailure : Bool := match noSecondFunding.generate (discovery 2) with
  | .failed (.unfunded _) => true | _ => false
def newReadingFailure : Bool := match noSecondPaidRead.generate (discovery 2) with
  | .failed (.observation _) => true | _ => false

set_option maxHeartbeats 1600000 in
theorem old_financing_and_old_knowledge_cannot_pay_for_the_next_trial :
    newFundingFailure = true ∧ noSecondFunding.invested = false ∧
      noSecondFunding.paidSignal (discovery 2) = none ∧
      newReadingFailure = true ∧ noSecondPaidRead.paidSignal (discovery 2) = none ∧
      (noSecondPaidRead.after (discovery 2)).technology = 2 := by decide +kernel

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Trials.Renewal
