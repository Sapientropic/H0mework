import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry

set_option autoImplicit false
set_option maxHeartbeats 5000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry

open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}
  (views : List (View (code := code))) (template : Template (code := code))
  (selected : Activation template) (point : Cursor code) (rival : Opponent code)

def cursorAt (n : Nat) : Cursor code :=
  match compile views template selected.site with
  | .ready rule _ _ =>
      let source := Cursor.target point rule rival
      ⟨source.reference,source.reference_generated,source.history,source.original,source.opponent,source.side,
        Cursor.targetInput point rule rival,source.feedbackOverrides,point.cut+n,point.ownerStart⟩
  | .unsupported _ _ _ => {point with cut := point.cut+n}

abbrev target := (cursorAt views template selected point rival 0).source
abbrev entry := (cursorAt views template selected point rival 0).entry

theorem target_ready (rule : Distributed.Recall.Information.Agency.Protocol.Rule code)
    (work : rule.work.val = policy views template selected.site)
    (events : rule.events = eventTable views template selected.site)
    (result : compile views template selected.site = .ready rule work events) :
    target views template selected point rival = Cursor.target point rule rival := by
  unfold target cursorAt
  rw [result]

theorem target_unsupported (key : code.Key) (original : key ∈ code.keys)
    (outside : ¬ supported views template selected.site key)
    (result : compile views template selected.site = .unsupported key original outside) :
    target views template selected point rival = point.source := by
  unfold target cursorAt
  rw [result]

theorem the_acquisition_cursor_is_its_own_actual_target (n : Nat) :
    (cursorAt views template selected point rival n).source = target views template selected point rival := by
  cases result : compile views template selected.site <;> simp only [target,cursorAt,result]

theorem target_history : (target views template selected point rival).history = point.source.history := by
  cases result : compile views template selected.site <;> simp only [cursorAt,result]

abbrev state (n : Nat) := (target views template selected point rival).feedbackState
  (entry views template selected point rival) (point.cut+n)

abbrev actualExecution (n : Nat) := (target views template selected point rival).actualExecution
  (depth point+n)

theorem the_actual_word_is_generated_by_the_original_protocol_state (n : Nat) :
    (actualExecution views template selected point rival n).submitted =
      Feedback.word code ((target views template selected point rival).feedbackPolicy (point.cut+n))
        (entry views template selected point rival) (state views template selected point rival n) := by
  have active : (target views template selected point rival).feedback? =
      some (entry views template selected point rival) := rfl
  have empty : (target views template selected point rival).continuation = [] := rfl
  have emitted := (target views template selected point rival).feedback_word_is_actual
    (entry views template selected point rival) active empty (point.cut+n)
  have address : (target views template selected point rival).history.length+1+(point.cut+n) = depth point+n := by
    rw [target_history]
    dsimp only [depth]
    omega
  rw [address] at emitted
  exact emitted

theorem the_complete_original_financial_prefix_is_preserved
    (ordinal : Nat) (earlier : ordinal ≤ arrival point) :
    Native.Coupling.Match code point.source.input (target views template selected point rival).input
      (Financial.accountAt point.source.input ordinal)
      (Financial.accountAt (target views template selected point rival).input ordinal) := by
  cases result : compile views template selected.site with
  | ready rule work events =>
    rw [target_ready views template selected point rival rule work events result]
    exact Future.complete_finance_before point.source point.entry point.cut
      (Cursor.controller point rule rival) (term point.source point.entry point.cut rule).val rfl ordinal earlier
  | unsupported key original outside =>
    rw [target_unsupported views template selected point rival key original outside result]
    exact ⟨rfl,rfl⟩

variable (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))

def evaluation (views : List (View (code := model.source.code)))
    (template : Template (code := model.source.code)) (selected : Activation template)
    (point : Cursor model.source.code) (rival : Opponent model.source.code) : Option (Evaluation model.source.code) :=
  match compile views template selected.site with
  | .ready rule _ _ => some (Replanning.actualEvaluation model point rule rival)
  | .unsupported _ _ _ => none

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry
