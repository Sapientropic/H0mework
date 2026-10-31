import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Trials.Source.Syntax

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Trials

open Source.Program
open SaturationMonoid.ProcessGame.Society.PublicFunction

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

namespace Mechanism

variable (mechanism : Mechanism Party Good Port Technology Instrument) (nature : mechanism.Nature)

def sentFrame : mechanism.code.Frame :=
  if mechanism.invested then mechanism.code.step mechanism.policy mechanism.code.initial
    (mechanism.initialFrame nature) (.send mechanism.observer mechanism.observer)
  else mechanism.initialFrame nature

def deliveredFrame : mechanism.code.Frame :=
  if mechanism.invested then mechanism.code.step mechanism.policy mechanism.code.initial
    (mechanism.sentFrame nature) (.deliver 0)
  else mechanism.sentFrame nature

def ReadingCostPaid : Prop :=
  ∃ item ∈ (mechanism.code.law.execute
    (mechanism.code.rawAt mechanism.code.initial (mechanism.initialFrame nature))
    (mechanism.trialPrefix nature).length
    (mechanism.code.sendCost mechanism.observer mechanism.observer)).items,
    ∃ entry ∈ mechanism.code.law.actualDebit item.before item.request, 0 < entry.2

instance : Decidable (ReadingCostPaid mechanism nature) := by
  unfold ReadingCostPaid
  infer_instance

def observed : Bool := mechanism.invested && !(mechanism.sentFrame nature).sent.isEmpty &&
  decide (∀ item ∈ mechanism.code.law.rawItems
    (mechanism.code.rawAt mechanism.code.initial (mechanism.sentFrame nature))
    (mechanism.code.deliveryCost mechanism.observer), mechanism.code.law.Valid item.before item.request) &&
  decide (ReadingCostPaid mechanism nature)

def activeFrame : mechanism.code.Frame :=
  if mechanism.observed nature then mechanism.code.step mechanism.policy mechanism.code.initial
    (mechanism.deliveredFrame nature) (.activate mechanism.observer)
  else mechanism.deliveredFrame nature

def run : mechanism.code.Frame :=
  { mechanism.activeFrame nature with word := (mechanism.activeFrame nature).word ++ mechanism.closing }

def word := (mechanism.run nature).word
def execution := mechanism.code.law.execute mechanism.code.initial 0 (mechanism.word nature)
def after := (mechanism.execution nature).final
def next := mechanism.code.law.next mechanism.code.initial (mechanism.word nature)

/-- This is a proposal, not an executed future. It reads only the same
source's actually acquired local record. -/
def proposal := mechanism.code.action mechanism.policy mechanism.observer
  ((mechanism.run nature).inbox mechanism.observer)

def paidSignal : Option (Fin mechanism.code.signals) :=
  if mechanism.observed nature then some ((mechanism.deliveredFrame nature).inbox mechanism.observer) else none

theorem the_emitted_word_is_the_complete_original_inventory :
    ((mechanism.execution nature).items.map ExecutionItem.request) = mechanism.word nature :=
  mechanism.code.law.inventory_requests_exact mechanism.code.initial 0 _

theorem actual_material_balance (person : Party) (good : Good) :
    (mechanism.after nature).stock person good +
      mechanism.code.law.totalDebit (mechanism.execution nature).items person good =
    mechanism.code.initial.stock person good +
      mechanism.code.law.totalCredit (mechanism.execution nature).items person good :=
  mechanism.code.law.execute_material_balance mechanism.code.initial 0 _ person good

theorem same_actual_local_record_same_proposal
    (other : mechanism.Nature)
    (same : (mechanism.run nature).inbox mechanism.observer =
      (mechanism.run other).inbox mechanism.observer) :
    mechanism.proposal nature = mechanism.proposal other :=
  mechanism.code.same_delivered_signal_same_action mechanism.policy mechanism.observer _ _ same

theorem an_unpaid_observation_cannot_activate_work
    (unpaid : mechanism.observed nature = false) :
    mechanism.activeFrame nature = mechanism.deliveredFrame nature := by
  simp only [activeFrame, unpaid, Bool.false_eq_true, if_false]

theorem unpaid_communication_creates_no_paid_signal
    (unpaid : mechanism.observed nature = false) : mechanism.paidSignal nature = none := by
  simp only [paidSignal, unpaid, Bool.false_eq_true, if_false]

end Mechanism
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Trials
