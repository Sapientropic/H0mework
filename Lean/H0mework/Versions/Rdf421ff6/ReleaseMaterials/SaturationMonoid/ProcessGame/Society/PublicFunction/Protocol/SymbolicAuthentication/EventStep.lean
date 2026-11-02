import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LocalContentRuntime

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.EventStep

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol
open Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}
  (cursor : Cursor code) (protocol : Rule code)

abbrev seed := cursor.source.feedbackState cursor.entry cursor.cut
abbrev fixed (reply : Move code) : Opponent code := fun _ _ _ => reply
abbrev next (reply : Move code) := cursor.after protocol (fixed reply)
abbrev selected (rival : Opponent code) := rival (seed cursor).history (seed cursor).past (seed cursor).frame
abbrev boundary := cursor.source.history.length + 2 + cursor.cut

/-- Only the next reply is generated. Later choices are generated at the next
actual seed; no complete future callback table is enumerated. -/
def advance (domain : List (Cursor code)) : List (Cursor code) :=
  domain.flatMap fun current => (moves code).map (next current protocol)

theorem the_actual_next_reply_has_a_generated_successor
    (domain : List (Cursor code)) (inside : cursor ∈ domain) (rival : Opponent code) :
    next cursor protocol (selected cursor rival) ∈ advance protocol domain :=
  List.mem_flatMap.mpr ⟨cursor, inside, List.mem_map.mpr
    ⟨selected cursor rival, every_move_is_generated code _, rfl⟩⟩

theorem selected_reply_preserves_the_entire_next_state (rival : Opponent code) :
    (next cursor protocol (selected cursor rival)).source.feedbackState
        (next cursor protocol (selected cursor rival)).entry (cursor.cut + 1) =
      (cursor.after protocol rival).source.feedbackState (cursor.after protocol rival).entry (cursor.cut + 1) := by
  change (Cursor.target cursor protocol (fixed (selected cursor rival))).feedbackState
    (Cursor.targetInput cursor protocol (fixed (selected cursor rival))) (cursor.cut + 1) =
      (Cursor.target cursor protocol rival).feedbackState (Cursor.targetInput cursor protocol rival) (cursor.cut + 1)
  rw [Future.the_whole_future_run_is_the_actual_state, Future.the_whole_future_run_is_the_actual_state]
  simp only [Residual.run]
  rw [Residual.advance_is_its_actual_choice, Residual.advance_is_its_actual_choice]
  congr 1

private theorem prior_current (rival : Opponent code) (ordinal : Nat)
    (earlier : ordinal ≤ boundary cursor) :
    (cursor.after protocol rival).source.currentAt ordinal = cursor.source.currentAt ordinal := by
  have same := Machine.actual_prefix_from_events cursor.source.input (Cursor.target cursor protocol rival).input
    rfl rfl (boundary cursor)
    (Future.prior_raw_event cursor.source cursor.entry cursor.cut (Cursor.controller cursor protocol rival)
      (term cursor.source cursor.entry cursor.cut protocol).val rfl) ordinal earlier
  unfold Machine.currentAt
  change ProgrammeSource.rawCurrent (Cursor.target cursor protocol rival).input
    (ProgrammeHistory.visitAt (Cursor.target cursor protocol rival).input ordinal).current = _
  rw [same]
  rfl

private theorem prior_word (rival : Opponent code) (ordinal : Nat)
    (earlier : ordinal < boundary cursor) :
    ProgrammeSource.rawEvent (cursor.after protocol rival).source.input
        (ProgrammeHistory.visitAt (cursor.after protocol rival).source.input ordinal).current =
      ProgrammeSource.rawEvent cursor.source.input (ProgrammeHistory.visitAt cursor.source.input ordinal).current :=
  (Native.Coupling.History.occurrences cursor.source.input (Cursor.target cursor protocol rival).input
    rfl rfl (boundary cursor)
    (Future.prior_raw_event cursor.source cursor.entry cursor.cut (Cursor.controller cursor protocol rival)
      (term cursor.source cursor.entry cursor.cut protocol).val rfl) ordinal earlier).2

theorem selected_reply_preserves_every_completed_native_occurrence (rival : Opponent code)
    (ordinal : Nat) (completed : ordinal ≤ boundary cursor) :
    (next cursor protocol (selected cursor rival)).source.currentAt ordinal =
        (cursor.after protocol rival).source.currentAt ordinal ∧
      ProgrammeSource.rawEvent (next cursor protocol (selected cursor rival)).source.input
          (ProgrammeHistory.visitAt (next cursor protocol (selected cursor rival)).source.input ordinal).current =
        ProgrammeSource.rawEvent (cursor.after protocol rival).source.input
          (ProgrammeHistory.visitAt (cursor.after protocol rival).source.input ordinal).current := by
  refine ⟨(prior_current cursor protocol _ ordinal completed).trans (prior_current cursor protocol rival ordinal completed).symm, ?_⟩
  by_cases earlier : ordinal < boundary cursor
  · exact (prior_word cursor protocol _ ordinal earlier).trans (prior_word cursor protocol rival ordinal earlier).symm
  · have last : ordinal = boundary cursor := by omega
    subst ordinal
    rw [show boundary cursor = (cursor.source.history.length + 1 + (cursor.cut + 0)) + 1 by dsimp [boundary]; omega]
    change ((Cursor.target cursor protocol (fixed (selected cursor rival))).actualExecution
        (cursor.source.history.length + 1 + (cursor.cut + 0))).submitted =
      ((Cursor.target cursor protocol rival).actualExecution
        (cursor.source.history.length + 1 + (cursor.cut + 0))).submitted
    rw [Future.future_word_is_actually_submitted, Future.future_word_is_actually_submitted]
    · simp only [Residual.run, word, decision]
      congr 1
    all_goals rfl

theorem current_round : (CursorSettlement.current cursor).round =
    code.initial.round + (cursor.source.history.length + 2 + cursor.cut) := by
  change (cursor.source.feedbackState cursor.entry cursor.cut).current.round = _
  rw [← cursor.source.feedback_current_is_actual cursor.entry rfl rfl cursor.cut, Machine.current_round]

theorem selected_reply_preserves_the_entire_completed_quote (rival : Opponent code) (scope : Scope) :
    CursorSettlement.quote (next cursor protocol (selected cursor rival)) scope =
      CursorSettlement.quote (cursor.after protocol rival) scope := by
  have states := selected_reply_preserves_the_entire_next_state cursor protocol rival
  have rounds := congrArg (fun state : State code => state.current.round) states
  change (CursorSettlement.current (next cursor protocol (selected cursor rival))).round =
    (CursorSettlement.current (cursor.after protocol rival)).round at rounds
  unfold CursorSettlement.quote
  rw [rounds]
  split <;> try rfl
  split <;> try rfl
  rename_i origin
  split <;> try rfl
  rename_i past
  have round := current_round (cursor.after protocol rival)
  have bounded : CursorSettlement.depth cursor scope + 1 ≤ boundary cursor := by
    dsimp only [CursorSettlement.depth, boundary, Cursor.after, Cursor.source, Cursor.target, Future.target, Execution.target] at *
    omega
  have same := selected_reply_preserves_every_completed_native_occurrence cursor protocol rival
    (CursorSettlement.depth cursor scope + 1) bounded
  obtain ⟨before, word⟩ := same
  change ((next cursor protocol (selected cursor rival)).source.actualExecution (CursorSettlement.depth cursor scope)).before =
    ((cursor.after protocol rival).source.actualExecution (CursorSettlement.depth cursor scope)).before at before
  change ((next cursor protocol (selected cursor rival)).source.actualExecution (CursorSettlement.depth cursor scope)).submitted =
    ((cursor.after protocol rival).source.actualExecution (CursorSettlement.depth cursor scope)).submitted at word
  change (match Settlement.issuedAt code.law
      ((next cursor protocol (selected cursor rival)).source.actualExecution (CursorSettlement.depth cursor scope)).before
      ((next cursor protocol (selected cursor rival)).source.actualExecution (CursorSettlement.depth cursor scope)).submitted scope.instanceId with
    | none => none
    | some payment => if payment.scope = scope then some payment else none) = _
  rw [before, word]
  rfl

abbrev applied (rival : Opponent code) : Input code := ⟨Cursor.controller cursor protocol rival, cursor.entry.budget⟩

private theorem current_control (rival : Opponent code) :
    Reaction.Feedback.advance code (Residual.scheduleAt cursor.source cursor.cut (term cursor.source cursor.entry cursor.cut protocol).val 0)
        (applied cursor protocol rival) (seed cursor) =
      Reaction.Feedback.advance code (some protocol.work.val) (applied cursor protocol rival) (seed cursor) := by
  by_cases stopped : (seed cursor).remaining = 0
  · cases control : Residual.scheduleAt cursor.source cursor.cut (term cursor.source cursor.entry cursor.cut protocol).val 0 <;>
      simp [Reaction.Feedback.advance, word, decision, stopped]
  · have positive : 0 < (seed cursor).remaining := by omega
    simp [Residual.scheduleAt, term, positive, seed]

theorem actual_next_state (rival : Opponent code) :
    seed (cursor.after protocol rival) =
      Reaction.Feedback.advance code (some protocol.work.val) (applied cursor protocol rival) (seed cursor) := by
  change (Cursor.target cursor protocol rival).feedbackState (Cursor.targetInput cursor protocol rival) (cursor.cut + 1) = _
  rw [Future.the_whole_future_run_is_the_actual_state]
  exact current_control cursor protocol rival

theorem actual_next_word (rival : Opponent code) :
    ProgrammeSource.rawEvent (cursor.after protocol rival).source.input
        (ProgrammeHistory.visitAt (cursor.after protocol rival).source.input (boundary cursor)).current =
      word code (some protocol.work.val) (applied cursor protocol rival) (seed cursor) := by
  have history := congrArg State.history (current_control cursor protocol rival)
  simp only [history_keeps_every_actual_word] at history
  have words := List.singleton_inj.mp (List.append_cancel_left history)
  rw [show boundary cursor = (cursor.source.history.length + 1 + (cursor.cut + 0)) + 1 by dsimp [boundary]; omega]
  change ((Cursor.target cursor protocol rival).actualExecution (cursor.source.history.length + 1 + (cursor.cut + 0))).submitted = _
  rw [Future.future_word_is_actually_submitted]
  · exact words
  · rfl

/-- Two prefixes retain their own sources. Only already generated states and
raw occurrences are compared; neither source supplies the other's future. -/
structure Matches (left right : Cursor code) : Prop where
  history_length : left.source.history.length = right.source.history.length
  cut : left.cut = right.cut
  ownerStart : left.ownerStart = right.ownerStart
  state : seed left = seed right
  currents : ∀ ordinal, ordinal ≤ boundary right → left.source.currentAt ordinal = right.source.currentAt ordinal
  words : ∀ ordinal, ordinal < boundary right →
    ProgrammeSource.rawEvent left.source.input (ProgrammeHistory.visitAt left.source.input ordinal).current =
      ProgrammeSource.rawEvent right.source.input (ProgrammeHistory.visitAt right.source.input ordinal).current

theorem matches_self : Matches cursor cursor := ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl⟩

theorem matches_step (left right : Cursor code) (same : Matches left right) (rival : Opponent code) :
    Matches (next left protocol (selected right rival)) (right.after protocol rival) := by
  have boundaries : boundary left = boundary right := by simp only [boundary, same.history_length, same.cut]
  have state : seed (next left protocol (selected right rival)) = seed (right.after protocol rival) := by
    rw [actual_next_state, actual_next_state]
    rw [same.state]
    rw [Residual.advance_is_its_actual_choice, Residual.advance_is_its_actual_choice]
    simp only [Cursor.controller, driver, same.ownerStart, fixed, selected]
  have words : word code (some protocol.work.val) (applied left protocol (fixed (selected right rival))) (seed left) =
      word code (some protocol.work.val) (applied right protocol rival) (seed right) := by
    have histories := congrArg State.history state
    rw [actual_next_state, actual_next_state] at histories
    simp only [history_keeps_every_actual_word] at histories
    rw [same.state] at histories
    rw [same.state]
    exact List.singleton_inj.mp (List.append_cancel_left histories)
  refine ⟨same.history_length, congrArg (· + 1) same.cut, same.ownerStart, state, ?_, ?_⟩
  · intro ordinal bounded
    have bound : ordinal ≤ boundary right + 1 := bounded
    by_cases prior : ordinal ≤ boundary right
    · exact (prior_current left protocol _ ordinal (by omega)).trans
        ((same.currents ordinal prior).trans (prior_current right protocol rival ordinal prior).symm)
    · have last : ordinal = boundary right + 1 := by omega
      subst ordinal
      have current := congrArg (fun item : State code => item.current) state
      rw [← (next left protocol (selected right rival)).source.feedback_current_is_actual
          (next left protocol (selected right rival)).entry rfl rfl _,
        ← (right.after protocol rival).source.feedback_current_is_actual (right.after protocol rival).entry rfl rfl _] at current
      change (next left protocol (selected right rival)).source.currentAt (boundary left + 1) =
        (right.after protocol rival).source.currentAt (boundary right + 1) at current
      rw [boundaries] at current
      exact current
  · intro ordinal bounded
    have bound : ordinal < boundary right + 1 := bounded
    by_cases prior : ordinal < boundary right
    · exact (prior_word left protocol _ ordinal (by omega)).trans
        ((same.words ordinal prior).trans (prior_word right protocol rival ordinal prior).symm)
    · have last : ordinal = boundary right := by omega
      subst ordinal
      rw [← boundaries, actual_next_word, boundaries, actual_next_word]
      exact words

theorem matches_quote (left right : Cursor code) (same : Matches left right) (scope : Scope) :
    CursorSettlement.quote left scope = CursorSettlement.quote right scope := by
  have rounds := congrArg (fun state : State code => state.current.round) same.state
  change (CursorSettlement.current left).round = (CursorSettlement.current right).round at rounds
  unfold CursorSettlement.quote
  rw [rounds]
  split <;> try rfl
  split <;> try rfl
  rename_i origin
  split <;> try rfl
  rename_i past
  have round := current_round right
  have bounded : CursorSettlement.depth right scope + 1 < boundary right := by
    dsimp only [CursorSettlement.depth, boundary] at *
    omega
  have before := same.currents (CursorSettlement.depth right scope + 1) (Nat.le_of_lt bounded)
  have submitted := same.words (CursorSettlement.depth right scope + 1) bounded
  change (left.source.actualExecution (CursorSettlement.depth right scope)).before =
    (right.source.actualExecution (CursorSettlement.depth right scope)).before at before
  change (left.source.actualExecution (CursorSettlement.depth right scope)).submitted =
    (right.source.actualExecution (CursorSettlement.depth right scope)).submitted at submitted
  change (match Settlement.issuedAt code.law (left.source.actualExecution (CursorSettlement.depth right scope)).before
      (left.source.actualExecution (CursorSettlement.depth right scope)).submitted scope.instanceId with
    | none => none
    | some payment => if payment.scope = scope then some payment else none) = _
  rw [before, submitted]
  rfl

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.EventStep
