import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Joint

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Machine

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (source : Machine Party Good Port Technology Instrument)

abbrev withFeedback (opponent : Opponent source.code) (budget : Nat) :
    Machine Party Good Port Technology Instrument :=
  {source with
    opponent := opponent
    continuation := []
    feedback? := some ⟨opponent, budget⟩
    feedbackOverrides := []}

theorem feedback_uses_one_opponent_from_its_first_response (opponent : Opponent source.code) (budget : Nat) :
    (source.withFeedback opponent budget).opponent = opponent ∧
      (source.withFeedback opponent budget).feedback? = some ⟨opponent, budget⟩ := ⟨rfl, rfl⟩

theorem response_frame_is_the_original_response : source.responseFrame.word =
    source.response (source.code.historyCurrent source.history) := by
  unfold responseFrame response
  cases source.policy? <;> rfl

theorem feedback_initial_is_the_actual_response_successor (input : Feedback.Input source.code) :
    source.currentAt (source.history.length + 2) = (source.feedbackInitial input).current := by
  rw [source.next_is_actual, source.response_is_actual, source.original_history_current_is_actual]
  exact congrArg (source.code.law.next _) source.response_frame_is_the_original_response.symm

theorem feedback_word_is_actual (input : Feedback.Input source.code)
    (active : source.feedback? = some input) (empty : source.continuation = []) (index : Nat) :
    (source.actualExecution (source.history.length + 1 + index)).submitted =
      Feedback.word source.code (source.feedbackPolicy index) input (source.feedbackState input index) := by
  rw [source.actual_word]
  unfold body
  rw [source.current_round]
  have address : source.code.initial.round + (source.history.length + 1 + index + 1) -
      source.code.initial.round - 1 = source.history.length + 1 + index := by omega
  rw [address, List.getElem?_eq_none (by omega), if_pos (by omega), empty, List.getElem?_nil]
  simp only [laterResponse, active]
  rw [show source.history.length + 1 + index - source.history.length - 1 = index by omega]

theorem feedback_current_is_actual (input : Feedback.Input source.code)
    (active : source.feedback? = some input) (empty : source.continuation = []) (index : Nat) :
    source.currentAt (source.history.length + 2 + index) = (source.feedbackState input index).current := by
  induction index with
  | zero => exact source.feedback_initial_is_the_actual_response_successor input
  | succ index ih =>
      rw [show source.history.length + 2 + (index + 1) =
          (source.history.length + 1 + index) + 2 by omega,
        source.next_is_actual, source.feedback_word_is_actual input active empty]
      rw [show source.history.length + 1 + index + 1 = source.history.length + 2 + index by omega, ih]
      rfl

def feedbackWords (count : Nat) : History (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument) :=
  (List.range count).map fun index => (source.actualExecution (source.history.length + 1 + index)).submitted

theorem feedback_keeps_the_complete_actual_history (input : Feedback.Input source.code)
    (active : source.feedback? = some input) (empty : source.continuation = []) (index : Nat) :
    (source.feedbackState input index).history =
      source.history ++ [source.responseFrame.word] ++ source.feedbackWords index := by
  induction index with
  | zero => simp only [feedbackState, feedbackInitial, feedbackWords, List.range_zero,
      List.map_nil, List.append_nil]
  | succ index ih =>
      change (Feedback.advance source.code (source.feedbackPolicy index) input (source.feedbackState input index)).history = _
      rw [Feedback.history_keeps_every_actual_word, ih, ← source.feedback_word_is_actual input active empty]
      simp only [feedbackWords, List.range_succ, List.map_append, List.map_cons, List.map_nil, List.append_assoc]

theorem feedback_body_reads_the_actual_local_current (input : Feedback.Input source.code)
    (active : source.feedback? = some input) (empty : source.continuation = []) (index : Nat) :
    (source.feedbackState input index).current =
      (source.actualExecution (source.history.length + 1 + index)).before := by
  change _ = source.currentAt (source.history.length + 1 + index + 1)
  rw [show source.history.length + 1 + index + 1 = source.history.length + 2 + index by omega]
  exact (source.feedback_current_is_actual input active empty index).symm

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Machine
