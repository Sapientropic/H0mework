import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Trials.Source.Decision
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Trials.Material.Observation

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Trials

open Source.Program
open SaturationMonoid.ProcessGame.Society.PublicFunction

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

namespace Mechanism

variable (mechanism : Mechanism Party Good Port Technology Instrument) (nature : mechanism.Nature)

theorem Accepted.ready (accepted : Accepted mechanism nature) : Ready mechanism nature := by
  refine ⟨?_, accepted.investmentPaid, accepted.observationPaid, accepted.safe, accepted.continuation⟩
  simp only [funded, accepted.financeRead, Option.isSome_some]

/-- Every person is covered by the original source inventory. The future
word is generated from the acquired record, not supplied as a paid plan. -/
theorem Accepted.full_scope_continuation (accepted : Accepted mechanism nature) :
    (∀ person, Exit.Necessity.BundlePaid mechanism.code.law (mechanism.after nature)
        (mechanism.proposal nature) person
        (mechanism.code.law.necessities (mechanism.after nature) person) .necessity ∧
      Exit.Necessity.BundlePaid mechanism.code.law (mechanism.after nature)
        (mechanism.proposal nature) person
        (mechanism.code.law.mandatoryMaintenance (mechanism.after nature) person) .maintenance) ∧
      (∀ item ∈ mechanism.code.law.rawItems (mechanism.after nature) (mechanism.proposal nature),
        mechanism.code.law.Valid item.before item.request) ∧ Productive mechanism nature := by
  exact ⟨fun person => accepted.continuation.2.2.1 person (mechanism.code.parties_cover person),
    accepted.continuation.1, accepted.continuation.2.2.2⟩

theorem the_source_generated_trial_returns_the_complete_original_disposition :
    match mechanism.generate nature with
    | .accepted accepted =>
        Ready mechanism nature ∧
        accepted.finance.issue ∈ (mechanism.execution nature).items ∧
        accepted.finance.payout ∈ (mechanism.execution nature).items ∧
        mechanism.paidSignal nature = some (mechanism.code.afterDelivery mechanism.observer mechanism.observer
          ((mechanism.sentFrame nature).inbox mechanism.observer)
          (mechanism.code.readLocal mechanism.observer (mechanism.code.snapshot mechanism.observer
            (mechanism.code.rawAt mechanism.code.initial (mechanism.initialFrame nature))))) ∧
        (∃ item ∈ (mechanism.execution nature).items,
          ∃ entry ∈ mechanism.code.law.actualDebit item.before item.request, 0 < entry.2) ∧
        ∀ person good, Safety.required mechanism person good ≤ (mechanism.after nature).stock person good
    | .failed _ => ¬ Ready mechanism nature := by
  cases mechanism.generate nature with
  | accepted accepted =>
      have original := mechanism.a_real_financing_receipt_uses_the_same_trial_items nature accepted.finance
      exact ⟨accepted.ready mechanism nature, original.1, original.2,
        mechanism.paid_signal_comes_from_the_original_local_read_and_own_memory nature accepted.observationPaid,
        mechanism.a_paid_signal_charges_an_original_item_in_the_same_whole_execution nature accepted.observationPaid,
        Safety.every_protected_person_keeps_the_original_life_and_maintenance_budget mechanism nature accepted.safe⟩
  | failed failure => exact failure.excludes_ready mechanism nature

end Mechanism
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Trials
