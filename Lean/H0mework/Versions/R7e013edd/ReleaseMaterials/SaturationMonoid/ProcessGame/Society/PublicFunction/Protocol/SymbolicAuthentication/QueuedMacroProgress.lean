import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.FundedSignatureEntry

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.QueuedMacroProgress
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := model.source.code)) (law : StageReception.Law model.source.code)

abbrev rank := CommunicationProgressSource.rank model start vocabulary encoding law
abbrev used := UnifiedServicePotential.used model start vocabulary encoding law
abbrev queue (past : JointResponse.Stages model) :=
  QueueScheduler.untried model.source.code (OriginQueue.baseline start)
    (EventStep.seed (EventHistory.execute start past)).past

theorem packets_survive_actual_stages (cursor : Cursor model.source.code) (more : JointResponse.Stages model) :
    (EventStep.seed cursor).frame.sent <+: (EventStep.seed (EventHistory.execute cursor more)).frame.sent := by
  induction more generalizing cursor with
  | nil => exact List.prefix_refl _
  | cons stage more ih =>
    have one : (EventStep.seed cursor).frame.sent <+: (EventStep.seed (cursor.after stage.1 stage.2)).frame.sent := by
      rw [EventStep.actual_next_state]
      exact (QueueScheduler.advance_preserves_memory_and_queue model.source.code (some stage.1.work.val)
        (EventStep.applied cursor stage.1 stage.2) (EventStep.seed cursor)).2
    exact one.trans (ih _)

theorem pending_queue_has_an_actual_admitted_untried_packet
    (past : JointResponse.Stages model) (pending : JointResponse.queueClear model start past = false) :
    ∃ serial, serial < (EventStep.seed (EventHistory.execute start past)).frame.sent.length ∧
      serial ∈ queue model start past := by
  cases chosen : OriginQueue.environment start (EventStep.seed (EventHistory.execute start past)).history
      (EventStep.seed (EventHistory.execute start past)).past (EventStep.seed (EventHistory.execute start past)).frame with
  | none => simp only [JointResponse.queueClear, JointResponse.current, chosen, Option.isNone_none] at pending; contradiction
  | some event =>
    obtain ⟨serial, _, present, fresh⟩ := QueueScheduler.generated_move_has_actual_queue_and_fresh_address
      model.source.code (OriginQueue.baseline start) _ _ _ event chosen
    exact ⟨serial, present, fresh⟩

theorem zero_communication_progress_preserves_the_actual_pending_queue
    (past later : JointResponse.Stages model) (ordered : past <+: later)
    (pending : JointResponse.queueClear model start past = false)
    (noDrop : rank model start vocabulary encoding law past ≤ rank model start vocabulary encoding law later) :
    JointResponse.queueClear model start later = false := by
  have credit := UnifiedServicePotential.actual_extension_preserves_used model start vocabulary encoding law past later ordered
  have addresses := MixedBirthPotential.actual_extension_cannot_refill_queue_addresses model start past later ordered
  have sameCard : (queue model start past).card ≤ (queue model start later).card := by
    unfold rank CommunicationProgressSource.rank UnifiedServicePotential.remaining at noDrop
    change (queue model start later).card ≤ (queue model start past).card at addresses
    change _ + (queue model start past).card ≤ _ + (queue model start later).card at noDrop
    omega
  obtain ⟨more, exactLater⟩ := ordered
  have subset : queue model start later ⊆ queue model start past := by
    rw [← exactLater]
    unfold queue
    rw [OriginQueue.execute_append]
    obtain ⟨events, history⟩ := OriginQueue.an_actual_prefix_retains_the_original_baseline (EventHistory.execute start past) more
    rw [← history]
    exact QueueScheduler.untried_append_subset model.source.code _ _ _
      (OriginQueue.an_actual_prefix_retains_the_original_baseline start past).length_le
  have same := Finset.eq_of_subset_of_card_le subset sameCard
  obtain ⟨serial, present, fresh⟩ := pending_queue_has_an_actual_admitted_untried_packet model start past pending
  have stillPresent : serial < (EventStep.seed (EventHistory.execute start later)).frame.sent.length := by
    rw [← exactLater, OriginQueue.execute_append]
    exact lt_of_lt_of_le present (packets_survive_actual_stages model (EventHistory.execute start past) more).length_le
  have stillFresh : serial ∈ queue model start later := by rw [same]; exact fresh
  obtain ⟨event, chosen⟩ := QueueScheduler.a_pending_admitted_packet_generates_a_move model.source.code
    (OriginQueue.baseline start) (EventStep.seed (EventHistory.execute start later)).history
    (EventStep.seed (EventHistory.execute start later)).past (EventStep.seed (EventHistory.execute start later)).frame serial stillPresent stillFresh
  change (QueueScheduler.opponent model.source.code (OriginQueue.baseline start)
    (EventStep.seed (EventHistory.execute start later)).history
    (EventStep.seed (EventHistory.execute start later)).past (EventStep.seed (EventHistory.execute start later)).frame).isNone = false
  rw [chosen]
  rfl

theorem actual_registration_progress_strictly_spends_communication_rank
    (past later : JointResponse.Stages model) (delay : Nat) (ordered : past <+: later)
    (progress : used model start vocabulary encoding law past < used model start vocabulary encoding law later)
    (compliant : AdaptiveRejectionHistory.Compliant start delay later) :
    rank model start vocabulary encoding law later < rank model start vocabulary encoding law past := by
  have cap := UnifiedServicePotential.actual_compliant_history_has_the_original_capacity model start vocabulary encoding law later delay compliant
  have addresses := MixedBirthPotential.actual_extension_cannot_refill_queue_addresses model start past later ordered
  unfold rank CommunicationProgressSource.rank UnifiedServicePotential.remaining
  unfold used at progress
  omega

private theorem response_work_increases_used (past : JointResponse.Stages model)
    (action : JointResponse.Action model start vocabulary encoding law past)
    (response : UnifiedResponseBudget.responseKind (JointResponse.kind model start vocabulary encoding law action) = true) :
    used model start vocabulary encoding law past < used model start vocabulary encoding law (JointResponse.after model start vocabulary encoding law past action) := by
  have grew := UnifiedResponseBudget.an_actual_response_action_generates_registration_progress model start vocabulary encoding law past action response
  have confirmed := RetryExecutionBudget.count_never_decreases model start vocabulary encoding law _ _
    (JointResponse.every_action_retains_the_whole_actual_prefix model start vocabulary encoding law past action)
  have weighted := Nat.mul_le_mul_right (CommunicationWorkBudget.slotAllowance model start) confirmed
  unfold used UnifiedServicePotential.used
  omega

theorem a_selected_pending_queue_step_is_paid_work_or_the_original_wait
    (past : JointResponse.Stages model) (action : UnifiedRecoveryDispatch.Action model start vocabulary encoding law past)
    (selected : UnifiedRecoveryDispatch.step model start vocabulary encoding law past = .advance action)
    (pending : JointResponse.queueClear model start past = false) :
    used model start vocabulary encoding law past < used model start vocabulary encoding law
      (UnifiedRecoveryDispatch.after model start vocabulary encoding law past action) ∨
    UnifiedRecoveryDispatch.after model start vocabulary encoding law past action =
      past ++ [(SilentWindow.quiet, OriginQueue.environment start)] := by
  cases action with
  | recovery answer =>
    have clear := answer.queue
    rw [pending] at clear
    contradiction
  | original action =>
    have original := UnifiedServicePotential.original_selection_is_retained model start vocabulary encoding law past action selected
    cases action with
    | wait live => exact Or.inr rfl
    | communication action =>
      cases action with
      | wait live => exact Or.inr rfl
      | conflict answer chosen =>
        exact Or.inl (response_work_increases_used model start vocabulary encoding law past (.communication (.conflict answer chosen)) rfl)
      | rejection answer chosen =>
        exact Or.inl (response_work_increases_used model start vocabulary encoding law past (.communication (.rejection answer chosen)) rfl)
      | retry answer chosen =>
        have grew := RetryExecutionBudget.every_actual_retry_action_generates_confirmation_progress model start vocabulary encoding law past
          (.communication (.retry answer chosen)) rfl
        have registered := UnifiedResponseBudget.count_never_decreases model start vocabulary encoding law _ _
          (TimedRetry.the_original_history_is_preserved start past vocabulary encoding law answer)
        have weighted := Nat.mul_le_mul_right (CommunicationWorkBudget.slotAllowance model start) grew
        dsimp only [JointResponse.after, UnifiedResponse.after] at weighted
        have positive : 0 < CommunicationWorkBudget.slotAllowance model start := by unfold CommunicationWorkBudget.slotAllowance; omega
        left
        change used model start vocabulary encoding law past < used model start vocabulary encoding law answer.stages
        simp only [Nat.add_mul, Nat.one_mul] at weighted
        unfold used UnifiedServicePotential.used
        omega
    | withdrawal ready accepted chosen | refused ready accepted chosen =>
      unfold JointResponse.step at original
      split at original
      · contradiction
      · split at original
        · cases response : UnifiedResponse.step model start vocabulary encoding law past <;>
            simp only [response, pending, Bool.false_eq_true, ↓reduceDIte] at original <;> cases original
        · contradiction

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.QueuedMacroProgress
