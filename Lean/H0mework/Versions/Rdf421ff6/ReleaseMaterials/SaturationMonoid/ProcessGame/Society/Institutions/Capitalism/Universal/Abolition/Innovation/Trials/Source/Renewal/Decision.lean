import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Trials.Source.Renewal

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Trials

open Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

namespace Mechanism

variable (mechanism : Mechanism Party Good Port Technology Instrument) (first : mechanism.Nature)

inductive RenewalDecision where
  | renewed (accepted : Accepted mechanism first)
      (paid : Exit.Necessity.AllNeedsPaid mechanism.code.law mechanism.code.initial mechanism.code.parties
        (mechanism.word first))
  | failed (failure : Failure mechanism first)
  | unpaidNecessity (person : Party) (original : person ∈ mechanism.code.parties)
      (unpaid : ¬ Exit.Necessity.BundlePaid mechanism.code.law mechanism.code.initial (mechanism.word first)
        person (mechanism.code.law.necessities mechanism.code.initial person) .necessity)
  | unpaidMaintenance (person : Party) (original : person ∈ mechanism.code.parties)
      (unpaid : ¬ Exit.Necessity.BundlePaid mechanism.code.law mechanism.code.initial (mechanism.word first)
        person (mechanism.code.law.mandatoryMaintenance mechanism.code.initial person) .maintenance)

/-- Raw next is a template. This source gate pays the actual first period
before releasing it as the next trial's input. -/
def prepareNextTrial : RenewalDecision mechanism first :=
  match mechanism.generate first with
  | .failed failure => .failed failure
  | .accepted accepted =>
      match Material.inspectList (fun person =>
          Exit.Necessity.BundlePaid mechanism.code.law mechanism.code.initial (mechanism.word first)
            person (mechanism.code.law.necessities mechanism.code.initial person) .necessity ∧
          Exit.Necessity.BundlePaid mechanism.code.law mechanism.code.initial (mechanism.word first)
            person (mechanism.code.law.mandatoryMaintenance mechanism.code.initial person) .maintenance)
          mechanism.code.parties with
      | .clear paid => .renewed accepted paid
      | .failure person original absent =>
          if need : Exit.Necessity.BundlePaid mechanism.code.law mechanism.code.initial (mechanism.word first)
              person (mechanism.code.law.necessities mechanism.code.initial person) .necessity then
            .unpaidMaintenance person original (fun maintained => absent ⟨need,maintained⟩)
          else .unpaidNecessity person original need

def RenewalDecision.next? : RenewalDecision mechanism first → Option (Mechanism Party Good Port Technology Instrument)
  | .renewed _ _ => some (mechanism.nextTrial first)
  | .failed _ | .unpaidNecessity .. | .unpaidMaintenance .. => none

def paidNextTrial? := (mechanism.prepareNextTrial first).next? mechanism first

theorem every_released_next_trial_has_paid_the_actual_first_period
    (next : Mechanism Party Good Port Technology Instrument)
    (released : mechanism.paidNextTrial? first = some next) :
    next = mechanism.nextTrial first ∧ Nonempty (Accepted mechanism first) ∧
      ∀ person, Exit.Necessity.BundlePaid mechanism.code.law mechanism.code.initial (mechanism.word first)
        person (mechanism.code.law.necessities mechanism.code.initial person) .necessity ∧
      Exit.Necessity.BundlePaid mechanism.code.law mechanism.code.initial (mechanism.word first)
        person (mechanism.code.law.mandatoryMaintenance mechanism.code.initial person) .maintenance := by
  unfold paidNextTrial? at released
  cases decision : mechanism.prepareNextTrial first with
  | renewed accepted paid =>
      simp only [decision, RenewalDecision.next?] at released
      exact ⟨(Option.some.inj released).symm, ⟨accepted⟩,
        fun person => paid person (mechanism.code.parties_cover person)⟩
  | failed failure => simp only [decision, RenewalDecision.next?] at released; cases released
  | unpaidNecessity person original unpaid => simp only [decision, RenewalDecision.next?] at released; cases released
  | unpaidMaintenance person original unpaid => simp only [decision, RenewalDecision.next?] at released; cases released

theorem a_failed_first_trial_cannot_be_reset_as_a_paid_next
    (failure : Failure mechanism first) (failed : mechanism.generate first = .failed failure) :
    mechanism.paidNextTrial? first = none := by
  simp only [paidNextTrial?, prepareNextTrial, failed, RenewalDecision.next?]

theorem a_missing_actual_first_payment_cannot_be_hidden_in_the_next_trial
    (unpaid : ¬ Exit.Necessity.AllNeedsPaid mechanism.code.law mechanism.code.initial mechanism.code.parties
      (mechanism.word first)) : mechanism.paidNextTrial? first = none := by
  cases choice : mechanism.paidNextTrial? first with
  | none => rfl
  | some next =>
      have paid := (mechanism.every_released_next_trial_has_paid_the_actual_first_period first next choice).2.2
      exact False.elim (unpaid (fun person _ => paid person))

end Mechanism
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Trials
