import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Trials.Source.Decision
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Trials.Material.Observation

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Trials

open Source.Program
open SaturationMonoid.ProcessGame.Society.PublicFunction

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

namespace Mechanism

variable (mechanism : Mechanism Party Good Port Technology Instrument)

/-- A fresh trial starts at the original interpreter's actual next current.
Its finance, investment and local communication are executed again. -/
def nextTrial (first : mechanism.Nature) : Mechanism Party Good Port Technology Instrument :=
  { mechanism with code := { mechanism.code with initial := mechanism.next first } }

theorem renewal_keeps_the_entire_generated_current (first : mechanism.Nature) :
    (mechanism.nextTrial first).code.initial = mechanism.next first ∧
      (mechanism.nextTrial first).code.initial.stock = (mechanism.after first).stock ∧
      (mechanism.nextTrial first).code.initial.claims = (mechanism.after first).claims ∧
      (mechanism.nextTrial first).code.initial.technology = (mechanism.after first).technology ∧
      (mechanism.nextTrial first).code.initial.clock = mechanism.code.initial.clock +
        max 0 (mechanism.code.law.duration mechanism.code.initial) ∧
      (mechanism.nextTrial first).code.initial.round = mechanism.code.initial.round + 1 :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem renewal_keeps_the_original_law_people_and_programme (first : mechanism.Nature) :
    (mechanism.nextTrial first).code.law = mechanism.code.law ∧
      (mechanism.nextTrial first).code.parties = mechanism.code.parties ∧
      (mechanism.nextTrial first).terms = mechanism.terms ∧
      (mechanism.nextTrial first).funding = mechanism.funding ∧
      (mechanism.nextTrial first).investmentRequest = mechanism.investmentRequest ∧
      (mechanism.nextTrial first).code.eventAlphabet = mechanism.code.eventAlphabet ∧
      HEq (mechanism.nextTrial first).policy mechanism.policy :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,HEq.rfl⟩

theorem renewal_rereads_finance_from_the_actual_next_current (first : mechanism.Nature) :
    (mechanism.nextTrial first).fundingReceipt = Financing.readDisbursement?
      mechanism.code.law (mechanism.next first) mechanism.funding mechanism.terms ∧
      (mechanism.nextTrial first).fundingAfter =
        (mechanism.code.law.execute (mechanism.next first) 0 mechanism.funding).final := ⟨rfl,rfl⟩

theorem renewal_starts_with_no_old_packet_or_delivered_signal
    (first second : mechanism.Nature) :
    ((mechanism.nextTrial first).initialFrame second).sent = [] ∧
      ((mechanism.nextTrial first).initialFrame second).inbox = fun _ => mechanism.code.initialSignal :=
  ⟨rfl,rfl⟩

theorem renewed_investment_is_a_new_actual_source_debit (first : mechanism.Nature)
    (person : Party) (good : Good) :
    (mechanism.nextTrial first).investmentLoss person good =
      if (mechanism.nextTrial first).funded then flowAt
        (mechanism.code.law.actualDebit
          (mechanism.code.law.execute (mechanism.next first) 0 mechanism.funding).final
          mechanism.investmentRequest) person good else 0 := rfl

theorem every_renewed_attempt_uses_the_same_original_inventory
    (first second : mechanism.Nature) :
    (((mechanism.nextTrial first).execution second).items.map ExecutionItem.request) =
      (mechanism.nextTrial first).word second :=
  (mechanism.nextTrial first).the_emitted_word_is_the_complete_original_inventory second

theorem a_renewed_unpaid_observation_cannot_reuse_the_old_signal
    (first second : mechanism.Nature)
    (unpaid : (mechanism.nextTrial first).observed second = false) :
    (mechanism.nextTrial first).paidSignal second = none :=
  (mechanism.nextTrial first).unpaid_communication_creates_no_paid_signal second unpaid

theorem every_renewed_raw_attempt_generates_success_or_its_exact_original_failure
    (first second : mechanism.Nature) :
    match (mechanism.nextTrial first).generate second with
    | .accepted _ => ContinuationChecks (mechanism.nextTrial first) second ∧
        Safety.Safe (mechanism.nextTrial first) second
    | .failed _ => ¬ Ready (mechanism.nextTrial first) second := by
  cases (mechanism.nextTrial first).generate second with
  | accepted accepted => exact ⟨accepted.continuation,accepted.safe⟩
  | failed failure => exact failure.excludes_ready (mechanism.nextTrial first) second

end Mechanism
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Trials
