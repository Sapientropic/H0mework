import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.QueuedMacroProgress

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.QueuedWindowProgress
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open private the_original_roster_is_preserved from
  H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CommunicationWorkBudget

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := model.source.code)) (law : StageReception.Law model.source.code)

abbrev atCut := UnifiedRunPrefix.atCut model start vocabulary encoding law
abbrev rank := CommunicationProgressSource.rank model start vocabulary encoding law
def width := start.ownerStart + 2
abbrev quiet : Nat → Rule model.source.code := fun _ => SilentWindow.quiet

-- A non-progressing mixed run must execute the original queue waits. The source
-- roster then forces an external delivery attempt; no delivery receipt is supplied.
theorem source_queue_turns_force_progress_in_the_actual_mixed_run
    (past : JointResponse.Stages model) (delay : Nat)
    (pending : JointResponse.queueClear model start past = false)
    (reserve : width model start * CommunicationWorkBudget.slotAllowance model start < JointResponse.fuel model start past)
    (compliant : AdaptiveRejectionHistory.Compliant start delay
      (atCut model start vocabulary encoding law past (width model start))) :
    rank model start vocabulary encoding law (atCut model start vocabulary encoding law past (width model start)) <
      rank model start vocabulary encoding law past := by
  by_contra noProgress
  have noDrop : rank model start vocabulary encoding law past ≤
      rank model start vocabulary encoding law (atCut model start vocabulary encoding law past (width model start)) := by omega
  have original (n : Nat) : past <+: atCut model start vocabulary encoding law past n :=
    UnifiedRecoveryRun.every_run_keeps_the_whole_actual_history model start vocabulary encoding law n past
  have ordered (n m : Nat) (before : n ≤ m) :
      atCut model start vocabulary encoding law past n <+: atCut model start vocabulary encoding law past m :=
    FundedSignatureEntry.actual_cut_is_a_prefix_of_every_later_cut model start vocabulary encoding law past n m before
  have unchanged (n : Nat) (inside : n ≤ width model start) :
      rank model start vocabulary encoding law (atCut model start vocabulary encoding law past n) =
        rank model start vocabulary encoding law past := by
    have before := CommunicationProgressSource.actual_extension_cannot_refill_the_communication_rank model start vocabulary encoding law _ _ (original n)
    have after := CommunicationProgressSource.actual_extension_cannot_refill_the_communication_rank model start vocabulary encoding law _ _ (ordered n _ inside)
    change rank model start vocabulary encoding law (atCut model start vocabulary encoding law past n) ≤ rank model start vocabulary encoding law past at before
    change rank model start vocabulary encoding law (atCut model start vocabulary encoding law past (width model start)) ≤
      rank model start vocabulary encoding law (atCut model start vocabulary encoding law past n) at after
    omega
  have queued (n : Nat) (inside : n ≤ width model start) :
      JointResponse.queueClear model start (atCut model start vocabulary encoding law past n) = false :=
    QueuedMacroProgress.zero_communication_progress_preserves_the_actual_pending_queue model start vocabulary encoding law
      past _ (original n) pending (by
        change rank model start vocabulary encoding law past ≤ rank model start vocabulary encoding law (atCut model start vocabulary encoding law past n)
        rw [unchanged n inside])
  have live (n : Nat) (inside : n ≤ width model start) :
      0 < JointResponse.fuel model start (atCut model start vocabulary encoding law past n) := by
    have cost := Nat.mul_le_mul_right (CommunicationWorkBudget.slotAllowance model start) inside
    exact UnifiedRunCost.a_source_reserve_keeps_every_actual_prefix_live model start vocabulary encoding law n past (by omega)
  have onlyWaits : ∀ n ≤ width model start,
      atCut model start vocabulary encoding law past n = past ++ OriginQueue.stages start (quiet model) n := by
    intro n inside
    induction n with
    | zero => simp only [atCut, UnifiedRunPrefix.zero_has_the_original_stages, OriginQueue.stages, List.append_nil]
    | succ n ih =>
      let here := atCut model start vocabulary encoding law past n
      have queuePending := queued n (by omega)
      have alive := live n (by omega)
      cases selected : UnifiedRecoveryDispatch.step model start vocabulary encoding law here with
      | clear closed =>
        have clear := closed.2.2
        change JointResponse.queueClear model start here = false at queuePending
        rw [queuePending] at clear
        contradiction
      | exhausted empty =>
        change 0 < JointResponse.fuel model start here at alive
        omega
      | advance action =>
        have next : atCut model start vocabulary encoding law past (n + 1) =
            UnifiedRecoveryDispatch.after model start vocabulary encoding law here action := by
          rw [atCut, UnifiedRunPrefix.the_next_actual_prefix_is_the_same_original_step]
          change UnifiedRunPrefix.nextStages model start vocabulary encoding law here = _
          simp only [UnifiedRunPrefix.nextStages, selected]
        rcases QueuedMacroProgress.a_selected_pending_queue_step_is_paid_work_or_the_original_wait
          model start vocabulary encoding law here action selected queuePending with work | wait
        · have localCompliance := FundedSignatureEntry.original_compliance_restricts_to_the_same_prefix model start _ _
            (ordered (n + 1) (width model start) inside) delay compliant
          rw [next] at localCompliance
          have drops := QueuedMacroProgress.actual_registration_progress_strictly_spends_communication_rank
            model start vocabulary encoding law here _ delay
            (UnifiedRecoveryDispatch.every_action_keeps_the_whole_actual_history model start vocabulary encoding law here action) work localCompliance
          change rank model start vocabulary encoding law _ < rank model start vocabulary encoding law here at drops
          rw [← next] at drops
          change rank model start vocabulary encoding law (atCut model start vocabulary encoding law past (n + 1)) <
            rank model start vocabulary encoding law (atCut model start vocabulary encoding law past n) at drops
          rw [unchanged (n + 1) inside, unchanged n (by omega)] at drops
          exact False.elim (Nat.lt_irrefl _ drops)
        · rw [next, wait]
          change atCut model start vocabulary encoding law past n ++ [_] = _
          rw [ih (by omega)]
          simp only [OriginQueue.stages, List.append_assoc, quiet]
  let cursor := EventHistory.execute start past
  have states (n : Nat) (inside : n ≤ width model start) :
      EventStep.seed (EventHistory.execute start (atCut model start vocabulary encoding law past n)) =
        OriginQueue.state start cursor (quiet model) n := by
    rw [onlyWaits n inside, OriginQueue.execute_append, OriginQueue.executed_stages_are_the_actual_cursor]
  obtain ⟨offset, small, external⟩ := OriginQueue.an_external_turn_occurs_in_each_pair start cursor (quiet model)
    (OriginQueue.warmup cursor) (Nat.le_refl _)
  let index := OriginQueue.warmup cursor + offset
  have early : index < width model start := by
    have sameOwner := the_original_roster_is_preserved model start past
    change cursor.ownerStart = start.ownerStart at sameOwner
    dsimp only [index, OriginQueue.warmup]
    unfold width
    omega
  have fits : OriginQueue.baseline start ≤ (EventStep.seed cursor).past.length :=
    (OriginQueue.an_actual_prefix_retains_the_original_baseline start past).length_le
  obtain ⟨serial, present, fresh⟩ := QueuedMacroProgress.pending_queue_has_an_actual_admitted_untried_packet model start
    (atCut model start vocabulary encoding law past index) (queued index (by omega))
  rw [states index (by omega)] at present
  unfold QueuedMacroProgress.queue at fresh
  rw [states index (by omega)] at fresh
  have physicalRoom : index < (EventStep.seed cursor).remaining := by
    have positive : 1 ≤ CommunicationWorkBudget.slotAllowance model start := by unfold CommunicationWorkBudget.slotAllowance; omega
    have scale := Nat.mul_le_mul_left (width model start) positive
    simp only [Nat.mul_one] at scale
    change width model start * CommunicationWorkBudget.slotAllowance model start < (EventStep.seed cursor).remaining at reserve
    omega
  obtain ⟨_, _, queueDrop⟩ := OriginQueue.an_external_pending_packet_decreases_the_actual_rank start cursor (quiet model)
    fits index serial physicalRoom external present fresh
  dsimp only [OriginQueue.rank] at queueDrop
  rw [← states (index + 1) (by omega), ← states index (by omega)] at queueDrop
  change MixedBirthPotential.rank model start (atCut model start vocabulary encoding law past (index + 1)) <
    MixedBirthPotential.rank model start (atCut model start vocabulary encoding law past index) at queueDrop
  have credit := UnifiedServicePotential.actual_extension_preserves_used model start vocabulary encoding law _ _
    (ordered index (index + 1) (by omega))
  have one := unchanged index (by omega)
  have two := unchanged (index + 1) (by omega)
  unfold rank CommunicationProgressSource.rank UnifiedServicePotential.remaining at one two
  omega

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.QueuedWindowProgress
