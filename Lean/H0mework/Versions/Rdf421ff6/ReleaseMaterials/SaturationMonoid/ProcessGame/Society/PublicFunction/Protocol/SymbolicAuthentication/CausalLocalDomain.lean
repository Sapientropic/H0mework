import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LocalClaimGate

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CausalLocalDomain

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol
open Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}
  (cursor : Cursor code) (protocol : Rule code)

open EventStep

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

omit [DecidableEq Port] [DecidableEq Technology] in
theorem external_choice_is_idempotent (move : Move code) :
    Distributed.Recall.Information.Agency.externalChoice code
      (Distributed.Recall.Information.Agency.externalChoice code move) =
        Distributed.Recall.Information.Agency.externalChoice code move := by
  cases move with
  | none => rfl
  | some event => rcases event with ⟨event, supported⟩; cases event <;> rfl

def replies (current : Cursor code) : List (Move code) :=
  if (Distributed.Recall.Information.Agency.ownerAt code current.ownerStart (seed current).history.length).isSome
    then [none] else ((moves code).map (Distributed.Recall.Information.Agency.externalChoice code)).eraseDups

def chosen (left right : Cursor code) (rival : Opponent code) : Move code :=
  if (Distributed.Recall.Information.Agency.ownerAt code left.ownerStart (seed left).history.length).isSome
    then none else Distributed.Recall.Information.Agency.externalChoice code (selected right rival)

def advance (domain : List (Cursor code)) : List (Cursor code) :=
  domain.flatMap fun current => (replies current).map (next current protocol)

def history (domain : List (Cursor code)) : List (Rule code) → List (Cursor code)
  | [] => domain
  | rule :: tail => history (advance rule domain) tail

theorem a_compact_reply_preserves_the_entire_actual_completed_prefix (left right : Cursor code) (same : Matches left right) (rival : Opponent code) :
    Matches (next left protocol (chosen left right rival)) (right.after protocol rival) := by
  have boundaries : boundary left = boundary right := by simp only [boundary, same.history_length, same.cut]
  have state : seed (next left protocol (chosen left right rival)) = seed (right.after protocol rival) := by
    rw [actual_next_state, actual_next_state]
    rw [same.state]
    rw [Residual.advance_is_its_actual_choice, Residual.advance_is_its_actual_choice]
    cases own : Distributed.Recall.Information.Agency.ownerAt code right.ownerStart (seed right).history.length with
    | none => simp [Cursor.controller, driver, chosen, same.ownerStart, same.state, own, fixed, selected, external_choice_is_idempotent]
    | some site => simp [Cursor.controller, driver, chosen, same.ownerStart, same.state, own, selected]
  have words : word code (some protocol.work.val) (applied left protocol (fixed (chosen left right rival))) (seed left) =
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
      rw [← (next left protocol (chosen left right rival)).source.feedback_current_is_actual
          (next left protocol (chosen left right rival)).entry rfl rfl _,
        ← (right.after protocol rival).source.feedback_current_is_actual (right.after protocol rival).entry rfl rfl _] at current
      change (next left protocol (chosen left right rival)).source.currentAt (boundary left + 1) =
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

theorem every_finite_actual_trace_has_a_compact_representative
    (domain : List (Cursor code)) (left right : Cursor code) (inside : left ∈ domain)
    (same : Matches left right) (stages : List (EventHistory.Stage (code := code))) :
    ∃ representative ∈ history domain (stages.map Prod.fst), Matches representative (EventHistory.execute right stages) := by
  induction stages generalizing domain left right with
  | nil => exact ⟨left, inside, same⟩
  | cons stage tail ih =>
    rcases stage with ⟨rule, rival⟩
    have admitted : chosen left right rival ∈ replies left := by
      unfold chosen replies
      split
      · simp
      · apply List.mem_eraseDups.mpr
        exact List.mem_map.mpr ⟨selected right rival, every_move_is_generated code _, rfl⟩
    have generated : next left rule (chosen left right rival) ∈ advance rule domain :=
      List.mem_flatMap.mpr ⟨left, inside, List.mem_map.mpr ⟨_, admitted, rfl⟩⟩
    exact ih _ _ _ generated (a_compact_reply_preserves_the_entire_actual_completed_prefix rule left right same rival)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CausalLocalDomain
