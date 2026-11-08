import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DutyConfirmation

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RetryProgress
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}
  (encoding : StageTransport.Encoding (code := code))

def ballots : Finset (StageBudget.Ballot (code := code)) :=
  ((List.finRange code.signals).filterMap encoding).toFinset
def directory : Finset (StageDuty.Content (code := code)) :=
  ballots encoding ×ˢ (Finset.univ : Finset (Fin code.sites))
def capacity := code.signals * code.sites

omit [DecidableEq Port] [DecidableEq Technology] in
theorem directory_has_a_source_interface_bound : (directory encoding).card ≤ capacity (code := code) := by
  have bounded : (ballots encoding).card ≤ code.signals :=
    (List.toFinset_card_le _).trans ((List.length_filterMap_le _ _).trans (by simp))
  unfold directory
  rw [Finset.card_product]
  simp only [Finset.card_univ, Fintype.card_fin, capacity]
  exact Nat.mul_le_mul_right _ bounded

variable (start : Cursor code)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) (law : StageReception.Law code)

theorem every_original_duty_has_a_real_encoded_content
    (emission : StageDuty.Emission start vocabulary encoding) :
    DutyConfirmation.key start vocabulary encoding emission ∈ directory encoding := by
  have authenticated : StageTransport.verify vocabulary encoding start emission.birthStages emission.wire = true := by
    apply decide_eq_true
    apply List.mem_filterMap.mpr
    exact ⟨emission.send, List.mem_range.mpr (by rw [emission.at_birth]; omega), emission.generated⟩
  obtain ⟨index, row, origin, packet, actual, prior, paid, ledger, cut, word,
      present, sender, recipient, signal, time, decoded, rest⟩ :=
    StageTransport.authenticated_wire_has_actual_send_and_paid_ballot vocabulary encoding start emission.birthStages emission.wire authenticated
  apply Finset.mem_product.mpr
  refine ⟨List.mem_toFinset.mpr (List.mem_filterMap.mpr ⟨emission.wire.signal, List.mem_finRange _, decoded⟩), Finset.mem_univ _⟩

theorem confirmed_contents_have_a_source_generated_budget
    (past : List (EventHistory.Stage (code := code))) :
    (DutyConfirmation.contents start vocabulary encoding law past).card ≤ capacity (code := code) := by
  have included : DutyConfirmation.contents start vocabulary encoding law past ⊆ directory encoding := by
    intro content inside
    obtain ⟨emission, _, _, rfl⟩ := (DutyConfirmation.mem_contents start vocabulary encoding law past content).mp inside
    exact every_original_duty_has_a_real_encoded_content encoding start vocabulary emission
  exact (Finset.card_le_card included).trans (directory_has_a_source_interface_bound encoding)

variable (past : List (EventHistory.Stage (code := code))) (answer : TimedRetry.Ready start past vocabulary encoding law)

theorem the_original_overdue_content_is_not_already_confirmed :
    DutyConfirmation.key start vocabulary encoding answer.overdue.emission ∉ DutyConfirmation.contents start vocabulary encoding law past := by
  intro member
  obtain ⟨emission, _, confirmed, same⟩ := (DutyConfirmation.mem_contents start vocabulary encoding law past _).mp member
  exact answer.overdue.unconfirmed ((DutyConfirmation.confirmation_depends_on_the_original_content
    start vocabulary encoding law past emission answer.overdue.emission same).mp confirmed)

theorem the_actual_retry_confirms_the_same_original_duty :
    TimedDuty.Confirmed start answer.stages vocabulary encoding law answer.overdue.emission := by
  obtain ⟨row, member, original, terminal⟩ := TimedRetry.new_actual_delivery_terminates_the_original_duty start past vocabulary encoding law answer
  have actual := (StageDuty.generated_row_terminal_iff_the_actual_receiver_confirms start vocabulary encoding law answer.stages row member).mp terminal
  change TimedDuty.Confirmed start answer.stages vocabulary encoding law row.1 at actual
  rw [original] at actual
  exact actual

theorem an_actual_retry_gains_a_previously_unconfirmed_original_content :
    DutyConfirmation.key start vocabulary encoding answer.overdue.emission ∈ DutyConfirmation.contents start vocabulary encoding law answer.stages := by
  have retained := DutyConfirmation.the_original_emission_survives_actual_extension start vocabulary encoding past
    (SilentWindow.stages (TimedRetry.waiting start past vocabulary encoding law answer.overdue) ++
      [(TimedRetry.sending answer.overdue.emission.wire.ballot.key answer.overdue.emission.wire.recipient answer.supported, SilentWindow.environment)] ++
      [(SilentWindow.quiet, TimedRetry.delivery answer.wire.serial answer.deliverable)]) answer.overdue.emission answer.overdue.actual
  apply (DutyConfirmation.mem_contents start vocabulary encoding law answer.stages _).mpr
  exact ⟨answer.overdue.emission, by simpa only [TimedRetry.Ready.stages, TimedRetry.completed, TimedRetry.sent, TimedRetry.aligned, List.append_assoc] using retained,
    the_actual_retry_confirms_the_same_original_duty encoding start vocabulary law past answer, rfl⟩

theorem every_actual_ready_retry_generates_strict_confirmation_progress :
    (DutyConfirmation.contents start vocabulary encoding law past).card + 1 ≤
      (DutyConfirmation.contents start vocabulary encoding law answer.stages).card := by
  have old := DutyConfirmation.confirmed_contents_survive_actual_extension start vocabulary encoding law past answer.stages
    (TimedRetry.the_original_history_is_preserved start past vocabulary encoding law answer)
  have gained := an_actual_retry_gains_a_previously_unconfirmed_original_content encoding start vocabulary law past answer
  have fresh := the_original_overdue_content_is_not_already_confirmed encoding start vocabulary law past answer
  have included := Finset.card_le_card (Finset.insert_subset_iff.mpr ⟨gained, old⟩)
  rw [Finset.card_insert_of_notMem fresh] at included
  exact included

theorem a_completed_retry_cannot_make_the_same_original_content_overdue_again
    (later : List (EventHistory.Stage (code := code))) (ordered : answer.stages <+: later)
    (overdue : TimedDuty.Overdue start later vocabulary encoding law)
    (same : DutyConfirmation.key start vocabulary encoding answer.overdue.emission =
      DutyConfirmation.key start vocabulary encoding overdue.emission) : False := by
  obtain ⟨more, rfl⟩ := ordered
  have confirmed := DutyConfirmation.the_actual_confirmation_survives_extension start vocabulary encoding law answer.stages more
    answer.overdue.emission (the_actual_retry_confirms_the_same_original_duty encoding start vocabulary law past answer)
  exact overdue.unconfirmed ((DutyConfirmation.confirmation_depends_on_the_original_content
    start vocabulary encoding law _ answer.overdue.emission overdue.emission same).mp confirmed)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RetryProgress
