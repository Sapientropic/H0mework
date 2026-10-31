import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Trials.Material.Effects

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Trials

open Source.Program
open SaturationMonoid.ProcessGame.Society.PublicFunction

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

namespace Mechanism

variable (mechanism : Mechanism Party Good Port Technology Instrument) (nature : mechanism.Nature)

theorem acquired_packet_is_the_original_paid_local_read
    (observed : mechanism.observed nature = true) :
    (mechanism.sentFrame nature).sent =
      [⟨mechanism.observer, mechanism.observer,
        mechanism.code.readLocal mechanism.observer (mechanism.code.snapshot mechanism.observer
          (mechanism.code.rawAt mechanism.code.initial (mechanism.initialFrame nature))),
        (mechanism.trialPrefix nature).length⟩] := by
  have invested : mechanism.invested = true := by
    by_contra absent
    have no := Bool.eq_false_of_not_eq_true absent
    simp only [Mechanism.observed, no, Bool.false_and] at observed
    cases observed
  by_cases paid : ∀ item ∈ mechanism.code.law.rawItems
      (mechanism.code.rawAt mechanism.code.initial (mechanism.initialFrame nature))
      (mechanism.code.sendCost mechanism.observer mechanism.observer), mechanism.code.law.Valid item.before item.request
  · rw [sentFrame, if_pos invested]
    simpa only [initialFrame, Distributed.Code.start, List.nil_append] using
      mechanism.code.send_is_an_actual_local_reading mechanism.policy mechanism.code.initial
        (mechanism.initialFrame nature) mechanism.observer mechanism.observer paid
  · have noPacket : (mechanism.sentFrame nature).sent = [] := by
      rw [sentFrame, if_pos invested]
      change (if decide (∀ item ∈ mechanism.code.law.rawItems
          (mechanism.code.rawAt mechanism.code.initial (mechanism.initialFrame nature))
          (mechanism.code.sendCost mechanism.observer mechanism.observer),
          mechanism.code.law.Valid item.before item.request) then _ else _) = []
      rw [decide_eq_false paid]
      rfl
    simp only [Mechanism.observed, noPacket, List.isEmpty_nil, Bool.not_true, Bool.and_false] at observed
    cases observed

theorem paid_signal_is_the_actual_received_record
    (observed : mechanism.observed nature = true) :
    mechanism.paidSignal nature = some ((mechanism.deliveredFrame nature).inbox mechanism.observer) := by
  simp only [paidSignal, observed, if_true]

theorem paid_signal_comes_from_the_original_local_read_and_own_memory
    (paid : mechanism.observed nature = true) :
    mechanism.paidSignal nature = some (mechanism.code.afterDelivery mechanism.observer mechanism.observer
      ((mechanism.sentFrame nature).inbox mechanism.observer)
      (mechanism.code.readLocal mechanism.observer (mechanism.code.snapshot mechanism.observer
        (mechanism.code.rawAt mechanism.code.initial (mechanism.initialFrame nature))))) := by
  have components := Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp paid).1
  have invested : mechanism.invested = true := (Bool.and_eq_true_iff.mp components.1).1
  have deliveryPaid : ∀ item ∈ mechanism.code.law.rawItems
      (mechanism.code.rawAt mechanism.code.initial (mechanism.sentFrame nature))
      (mechanism.code.deliveryCost mechanism.observer), mechanism.code.law.Valid item.before item.request :=
    of_decide_eq_true components.2
  let packet : mechanism.code.Packet := ⟨mechanism.observer, mechanism.observer,
    mechanism.code.readLocal mechanism.observer (mechanism.code.snapshot mechanism.observer
      (mechanism.code.rawAt mechanism.code.initial (mechanism.initialFrame nature))),
    (mechanism.trialPrefix nature).length⟩
  have present : (mechanism.sentFrame nature).sent[0]? = some packet := by
    rw [mechanism.acquired_packet_is_the_original_paid_local_read nature paid]
    rfl
  have received := mechanism.code.delivery_reads_only_an_already_sent_packet mechanism.policy
    mechanism.code.initial (mechanism.sentFrame nature) 0 packet present deliveryPaid
  rw [mechanism.paid_signal_is_the_actual_received_record nature paid]
  congr 1
  rw [deliveredFrame, if_pos invested]
  exact received

theorem a_paid_signal_charges_an_original_item_in_the_same_whole_execution
    (paid : mechanism.observed nature = true) :
    ∃ item ∈ (mechanism.execution nature).items,
      ∃ entry ∈ mechanism.code.law.actualDebit item.before item.request, 0 < entry.2 := by
  have charged : ReadingCostPaid mechanism nature := of_decide_eq_true (Bool.and_eq_true_iff.mp paid).2
  have invested : mechanism.invested = true :=
    (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp paid).1).1).1
  obtain ⟨item, member, entry, debit, positive⟩ := charged
  obtain ⟨tail, exactWord⟩ := mechanism.the_sent_prefix_is_retained_in_the_whole_execution nature
  have sentWord : (mechanism.sentFrame nature).word = mechanism.trialPrefix nature ++
      mechanism.code.sendCost mechanism.observer mechanism.observer := by
    rw [sentFrame, if_pos invested]
    rfl
  refine ⟨item, ?_, entry, debit, positive⟩
  unfold execution
  rw [exactWord, RawLaw.execute_append, sentWord, RawLaw.execute_append]
  exact List.mem_append_left _ (List.mem_append_right _ (by
    simpa only [Nat.zero_add, Distributed.Code.rawAt, initialFrame] using member))

private theorem execute_keeps_the_micro_clock
    (law : RawLaw Party Good Port Technology Instrument)
    (initial : RawCurrent Party Good Technology Instrument) (index : Nat)
    (word : RawEvent Party Good Port Technology Instrument) :
    (law.execute initial index word).final.clock = initial.clock ∧
      (law.execute initial index word).final.round = initial.round := by
  induction word generalizing initial index with
  | nil => exact ⟨rfl, rfl⟩
  | cons request tail ih =>
      have later := ih (law.step initial request) (index + 1)
      have unchanged : (law.step initial request).clock = initial.clock ∧
          (law.step initial request).round = initial.round := by
        unfold RawLaw.step
        split <;> exact ⟨rfl, rfl⟩
      exact ⟨later.1.trans unchanged.1, later.2.trans unchanged.2⟩

theorem the_trial_microsteps_do_not_invent_extra_physical_periods :
    (mechanism.after nature).clock = mechanism.code.initial.clock ∧
      (mechanism.after nature).round = mechanism.code.initial.round :=
  execute_keeps_the_micro_clock _ _ _ _

end Mechanism
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Trials
