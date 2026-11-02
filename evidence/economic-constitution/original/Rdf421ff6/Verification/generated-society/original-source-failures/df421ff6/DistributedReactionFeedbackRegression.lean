import SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Source
import SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Regression

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Regression

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

abbrev need := Reaction.Regression.need
def issue : Request Bool Unit Unit Unit Unit := ⟨true, [], (), [], .issue () true false 2⟩
def repay : Request Bool Unit Unit Unit Unit := ⟨true, [], (), [], .settle () true false 2⟩

abbrev code : Code Bool Unit Unit Unit Unit := { Reaction.Regression.code with
  initial := {Reaction.Regression.code.initial with claims := fun _ _ _ => 0}
  bootstrap := [issue]
  actions := [need, repay]
  actionLimit := 1
  signals := 3
  initialSignal := 0
  readLocal := fun _ snapshot => if 0 < snapshot.liabilities () false then 1 else 2
  eventAlphabet := [.activate 0, .send 0 0, .deliver 0, .deliver 1]
  eligible := fun events => decide (events = [.activate 0]) }

def policy : code.Policy := fun key _ =>
  if key.2 = 0 then [need] else if key.2 = 1 then [repay] else []

theorem policy_is_generated : policy ∈ code.policies := by
  apply code.every_local_policy_is_enumerated
  intro key _
  simp only [policy]
  split
  · exact (mem_words_iff _ _ _).mpr (by simp)
  · split <;> exact (mem_words_iff _ _ _).mpr (by simp)

def opponent : Opponent code := fun history past _ =>
  if history.length = past.length + 1 then
    match past.length with
    | 0 => some ⟨.activate 0, by decide +kernel⟩
    | 1 => some ⟨.send 0 0, by decide +kernel⟩
    | 2 => some ⟨.deliver 0, by decide +kernel⟩
    | 3 => some ⟨.activate 0, by decide +kernel⟩
    | 4 => some ⟨.deliver 0, by decide +kernel⟩
    | 5 => some ⟨.activate 0, by decide +kernel⟩
    | 6 => some ⟨.send 0 0, by decide +kernel⟩
    | 7 => some ⟨.deliver 1, by decide +kernel⟩
    | 8 => some ⟨.activate 0, by decide +kernel⟩
    | _ => none
  else none

abbrev base : Machine Bool Unit Unit Unit Unit where
  code := code
  reference := policy
  reference_generated := policy_is_generated
  history := [[issue]]
  original := by decide +kernel
  opponent := opponent
  side := .original

theorem original_service_is_feasible : code.feasible policy := by decide +kernel

abbrev input : Input code := ⟨opponent, 8⟩
abbrev source := base.withFeedback opponent 8
abbrev state (index : Nat) := source.feedbackState input index

theorem one_actual_opponent_is_used_before_and_after_the_cut :
    source.opponent = input.opponent ∧
      source.feedback? = some input ∧
      (source.emissionEvents (code.historyCurrent [[issue]])) = [.activate 0] := by
  exact ⟨rfl, rfl, by decide +kernel⟩

theorem actual_words_do_not_replay_the_accumulated_frame :
    (List.range 10).map (fun index => (source.actualExecution index).submitted) =
      [[issue], [need], [], [], [repay], [], [repay], [], [], []] := by decide +kernel

theorem delayed_duplicate_and_updated_packets_keep_their_actual_history :
    (state 3).past = [.activate 0, .send 0 0, .deliver 0, .activate 0] ∧
      (state 3).history = [[issue], [need], [], [], [repay]] ∧
      (state 3).frame.word = [need, repay] ∧
      (state 3).frame.inbox 0 = 1 ∧
      (state 8).frame.sent.length = 2 ∧
      ((state 8).frame.sent[0]?).map (fun packet => packet.signal) = some 1 ∧
      ((state 8).frame.sent[1]?).map (fun packet => packet.signal) = some 2 ∧
      (state 8).frame.inbox 0 = 2 ∧
      (state 8).past.length = 9 ∧
      (state 8).remaining = 0 := by decide +kernel

theorem local_debt_reading_drives_actual_payment_and_preserves_its_native_archive :
    Financial.outstanding source.input (Native.generate source 1).finance.current = 2 ∧
      (source.actualExecution 4).after.stock true () = 0 ∧
      (source.actualExecution 4).after.stock false () = 2 ∧
      Financial.outstanding source.input (Native.generate source 4).finance.current = 0 ∧
      (Native.generate source 4).finance.current.slots.length = 1 ∧
      (Native.generate source 9).finance.current.slots = (Native.generate source 4).finance.current.slots ∧
      (state 5).frame.localLegal = false := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, ?_, by decide +kernel⟩
  with_unfolding_all rfl

theorem the_actual_terminal_archive_survives_duplicate_payment_attempts :
    ∃ archive, (Native.generate source 4).finance.current.slots = [.terminal archive] ∧
      (Native.generate source 9).finance.current.slots = [.terminal archive] := by
  let terminalStatus : ResponsibilityLifecycle.ObligationSlot (Financial.vocabulary source.input) → Bool
    | .live _ => false
    | .terminal _ => true
  have terminal : (Native.generate source 4).finance.current.slots.map terminalStatus = [true] := by decide +kernel
  have closed : ∃ archive, (Native.generate source 4).finance.current.slots = [.terminal archive] := by
    cases slots : (Native.generate source 4).finance.current.slots with
    | nil => simp [slots] at terminal
    | cons head tail =>
        cases tail with
        | cons _ _ => simp [slots] at terminal
        | nil =>
            cases head with
            | live _ => simp [slots, terminalStatus] at terminal
            | terminal archive => exact ⟨archive, rfl⟩
  obtain ⟨archive, closed⟩ := closed
  rcases local_debt_reading_drives_actual_payment_and_preserves_its_native_archive with
    ⟨_, _, _, _, _, retained, _⟩
  exact ⟨archive, closed, retained.trans closed⟩

abbrev stoppedSource := base.withFeedback opponent 0

theorem exhausted_budget_preserves_the_original_cut_and_does_not_restart :
    (stoppedSource.actualExecution 1).submitted = [need] ∧
      (stoppedSource.actualExecution 2).submitted = [] ∧
      (stoppedSource.actualExecution 3).submitted = [] ∧
      Financial.outstanding stoppedSource.input (Native.generate stoppedSource 3).finance.current = 2 := by
  decide +kernel

def expensive : Request Bool Unit Unit Unit Unit := ⟨true, [], (), [], .use true [((), 5)] .contribution⟩
abbrev deniedCode : Code Bool Unit Unit Unit Unit := {code with sendCost := fun _ _ => [expensive]}
def deniedOpponent : Opponent deniedCode := fun _ past _ =>
  if past.isEmpty then some ⟨.activate 0, by decide +kernel⟩
  else some ⟨.send 0 0, by decide +kernel⟩
abbrev deniedBase : Machine Bool Unit Unit Unit Unit :=
  {base with code := deniedCode, opponent := deniedOpponent, feedback? := none}
abbrev deniedSource := deniedBase.withFeedback deniedOpponent 8

theorem unpaid_communication_cannot_create_a_cross_cut_packet :
    (deniedSource.actualExecution 2).submitted = [expensive] ∧
      (deniedSource.actualExecution 2).after.stock true () = 2 ∧
      (deniedSource.feedbackState ⟨deniedOpponent, 8⟩ 1).frame.sent = [] ∧
      (deniedSource.feedbackState ⟨deniedOpponent, 8⟩ 1).frame.localLegal = false ∧
      Financial.outstanding deniedSource.input (Native.generate deniedSource 2).finance.current = 2 := by
  decide +kernel

abbrev overridden := source.withContinuation [[expensive]]

theorem explicit_word_continuation_overrides_feedback :
    overridden.feedback? = none ∧ (overridden.actualExecution 2).submitted = [expensive] := by
  exact ⟨rfl, by decide +kernel⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Regression
