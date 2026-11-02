import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Recovery

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 32768

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix

open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}

theorem after_budget (point : Cursor code) (rule : Distributed.Recall.Information.Agency.Protocol.Rule code)
    (rival : Opponent code) : (seed (point.after rule rival)).remaining = (seed point).remaining-1 := by
  change ((Future.target point.source point.entry point.cut (Cursor.controller point rule rival)
    (term point.source point.entry point.cut rule).val).feedbackState
      (Future.takeover point.source point.entry point.cut (Cursor.controller point rule rival)) (point.cut+1)).remaining = _
  rw [Future.the_whole_future_run_is_the_actual_state]
  exact Residual.remaining_is_the_seed_budget _ _ _ _ _

theorem after_state_scheduled (point : Cursor code) (rule : Distributed.Recall.Information.Agency.Protocol.Rule code)
    (rival : Opponent code) : seed (point.after rule rival) = Feedback.advance code
      (Residual.scheduleAt point.source point.cut (term point.source point.entry point.cut rule).val 0)
      ⟨Cursor.controller point rule rival,point.entry.budget⟩ (seed point) := by
  change (Future.target point.source point.entry point.cut (Cursor.controller point rule rival)
    (term point.source point.entry point.cut rule).val).feedbackState
      (Future.takeover point.source point.entry point.cut (Cursor.controller point rule rival)) (point.cut+1) = _
  rw [Future.the_whole_future_run_is_the_actual_state]
  rfl

theorem after_state (point : Cursor code) (rule : Distributed.Recall.Information.Agency.Protocol.Rule code)
    (rival : Opponent code) (active : 0 < (seed point).remaining) :
    seed (point.after rule rival) = Feedback.advance code (some rule.work.val)
      ⟨Cursor.controller point rule rival,point.entry.budget⟩ (seed point) := by
  rw [after_state_scheduled]
  simp only [Residual.scheduleAt,term,List.getElem?_replicate,if_pos active,Option.getD_some]

theorem the_current_actual_word (point : View (code := code))
    (rule : Distributed.Recall.Information.Agency.Protocol.Rule code) (rival : Opponent code) :
    Replay.submitted point rival rule = Feedback.word code
      (Residual.scheduleAt point.point.source point.point.cut
        (term point.point.source point.point.entry point.point.cut rule).val 0)
      ⟨Cursor.controller point.point rule rival,point.point.entry.budget⟩ (seed point.point) := by
  change ((Future.target point.point.source point.point.entry point.point.cut (Cursor.controller point.point rule rival)
    (term point.point.source point.point.entry point.point.cut rule).val).actualExecution
      (point.point.source.history.length+1+(point.point.cut+0))).submitted = _
  exact Future.future_word_is_actually_submitted point.point.source point.point.entry point.point.cut
    (Cursor.controller point.point rule rival) (term point.point.source point.point.entry point.point.cut rule).val rfl 0

omit [DecidableEq Port] [DecidableEq Technology] in
private theorem step_keeps_refused (policy : code.Policy)
    (initial : RawCurrent Party Good (Mandate.State Party Technology) Instrument) (frame : code.Frame)
    (event : Event Party Good Port (Mandate.State Party Technology) Instrument code.sites)
    (refused : frame.localLegal = false) : (code.step policy initial frame event).localLegal = false := by
  cases event with
  | adversary => exact refused
  | send => simp only [Code.step,refused,Bool.false_and]
  | deliver address =>
    simp only [Code.step]
    cases frame.sent[address]? <;> simp only [refused,Bool.false_and]
  | activate => simp only [Code.step,refused,Bool.false_and]

theorem after_keeps_refused (point : Cursor code) (rule : Distributed.Recall.Information.Agency.Protocol.Rule code)
    (rival : Opponent code) (active : 0 < (seed point).remaining)
    (refused : (seed point).frame.localLegal = false) : (seed (point.after rule rival)).frame.localLegal = false := by
  rw [after_state point rule rival active]
  unfold Feedback.advance
  cases chosen : decision code ⟨Cursor.controller point rule rival,point.entry.budget⟩ (seed point) with
  | none => exact refused
  | some event => exact step_keeps_refused _ _ _ _ refused

variable (template : Template (code := code)) (selected : Activation template)

inductive Path : List (View (code := code)) → View (code := code) → Opponent code → Type where
  | complete {views point rival} (cleared : remaining point.point point.origin template = 0) : Path views point rival
  | nonPositive {views point rival} (notPositive : ¬ 0 < template.amount) : Path views point rival
  | exhausted {views point rival} (empty : (seed point.point).remaining = 0) : Path views point rival
  | unsupported {views point rival} (key : code.Key) (original : key ∈ code.keys)
      (outside : ¬ Inquiry.supported views template selected.site key) : Path views point rival
  | blocked {views point rival} (rule : Distributed.Recall.Information.Agency.Protocol.Rule code)
      (work : rule.work.val = Information.policy views template selected.site)
      (events : rule.events = Inquiry.eventTable views template selected.site)
      (item : ExecutionItem Party Good Port (Mandate.State Party Technology) Instrument)
      (original : item ∈ code.law.rawItems (Replay.before point rival rule) (Replay.submitted point rival rule))
      (refused : ¬ code.law.Valid item.before item.request) : Path views point rival
  | advanced {views point rival} (rule : Distributed.Recall.Information.Agency.Protocol.Rule code)
      (work : rule.work.val = Information.policy views template selected.site)
      (events : rule.events = Inquiry.eventTable views template selected.site)
      (active : 0 < (seed point.point).remaining)
      (legal : Open.Legal code.law (Replay.before point rival rule) (Replay.submitted point rival rule))
      (tail : Path (PublicDomain.next rule views) (Evidence.after point rule rival) rival) : Path views point rival

def produce (views : List (View (code := code))) (point : View (code := code)) (rival : Opponent code) :
    Path template selected views point rival :=
  if cleared : remaining point.point point.origin template = 0 then .complete cleared
  else if positive : 0 < template.amount then
    if empty : (seed point.point).remaining = 0 then .exhausted empty
    else match Inquiry.compile views template selected.site with
      | .unsupported key original outside => .unsupported key original outside
      | .ready rule work events =>
        match Distributed.inspect (fun item : ExecutionItem Party Good Port (Mandate.State Party Technology) Instrument =>
          code.law.Valid item.before item.request)
          (code.law.rawItems (Replay.before point rival rule) (Replay.submitted point rival rule)) with
        | .rejected item original refused => .blocked rule work events item original refused
        | .accepted legal => .advanced rule work events (Nat.pos_of_ne_zero empty) legal
            (produce (PublicDomain.next rule views) (Evidence.after point rule rival) rival)
  else .nonPositive positive
termination_by (seed point.point).remaining
decreasing_by
  rw [show (Evidence.after point rule rival).point = point.point.after rule rival from rfl,after_budget]
  omega

namespace Path
variable {template selected} {views : List (View (code := code))} {point : View (code := code)} {rival : Opponent code}

def rules : {views : List (View (code := code))} → {point : View (code := code)} → {rival : Opponent code} →
    Path template selected views point rival → List (Distributed.Recall.Information.Agency.Protocol.Rule code)
  | _,_,_,.advanced rule _ _ _ _ tail => rule :: tail.rules
  | _,_,_,.complete _ | _,_,_,.nonPositive _ | _,_,_,.exhausted _ | _,_,_,.unsupported _ _ _ |
      _,_,_,.blocked _ _ _ _ _ _ => []

def final : {views : List (View (code := code))} → {point : View (code := code)} → {rival : Opponent code} →
    Path template selected views point rival → View (code := code)
  | _,_,_,.advanced _ _ _ _ _ tail => tail.final
  | _,point,_,.complete _ | _,point,_,.nonPositive _ | _,point,_,.exhausted _ | _,point,_,.unsupported _ _ _ |
      _,point,_,.blocked _ _ _ _ _ _ => point

def finalViews : {views : List (View (code := code))} → {point : View (code := code)} → {rival : Opponent code} →
    Path template selected views point rival → List (View (code := code))
  | _,_,_,.advanced _ _ _ _ _ tail => tail.finalViews
  | views,_,_,.complete _ | views,_,_,.nonPositive _ | views,_,_,.exhausted _ | views,_,_,.unsupported _ _ _ |
      views,_,_,.blocked _ _ _ _ _ _ => views

def Legal : {views : List (View (code := code))} → {point : View (code := code)} → {rival : Opponent code} →
    Path template selected views point rival → Prop
  | _,point,rival,.advanced rule _ _ _ _ tail =>
      Open.Legal code.law (Replay.before point rival rule) (Replay.submitted point rival rule) ∧ tail.Legal
  | _,_,_,.complete _ | _,_,_,.nonPositive _ | _,_,_,.exhausted _ | _,_,_,.unsupported _ _ _ |
      _,_,_,.blocked _ _ _ _ _ _ => True

theorem all_new_actual_submissions_are_legal (path : Path template selected views point rival) : path.Legal := by
  induction path with
  | advanced rule work events active legal tail ih => exact ⟨legal,ih⟩
  | complete | nonPositive | exhausted | unsupported | blocked => trivial

theorem final_is_the_original_actual_rule_fold (path : Path template selected views point rival) :
    path.final.point = path.rules.foldl (fun current rule => current.after rule rival) point.point := by
  induction path with
  | advanced rule work events active legal tail ih => exact ih
  | complete | nonPositive | exhausted | unsupported | blocked => rfl

theorem final_keeps_the_actual_original_debt (path : Path template selected views point rival)
    (covered : Knowledge.Contains views point) : Knowledge.Contains path.finalViews path.final := by
  induction path with
  | advanced rule work events active legal tail ih => exact ih (PublicDomain.after _ _ covered rule _)
  | complete | nonPositive | exhausted | unsupported | blocked => exact covered

theorem no_actual_suffix_clears_a_historical_refusal (path : Path template selected views point rival)
    (refused : (seed point.point).frame.localLegal = false) : (seed path.final.point).frame.localLegal = false := by
  induction path with
  | advanced rule work events active legal tail ih => exact ih (after_keeps_refused _ _ _ active refused)
  | complete | nonPositive | exhausted | unsupported | blocked => exact refused

theorem every_executed_cut_spends_the_original_budget (path : Path template selected views point rival) :
    (seed path.final.point).remaining + path.rules.length = (seed point.point).remaining := by
  induction path with
  | @advanced views point rival rule work events active legal tail ih =>
      have spent := after_budget point.point rule rival
      change (seed tail.final.point).remaining + (tail.rules.length+1) = _
      change (seed tail.final.point).remaining + tail.rules.length = _ at ih
      rw [show (Evidence.after point rule rival).point = point.point.after rule rival from rfl,spent] at ih
      omega
  | complete | nonPositive | exhausted | unsupported | blocked => simp only [final,rules,List.length_nil,Nat.add_zero]

end Path
end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix
