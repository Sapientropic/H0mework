import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 32768

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay

open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}
  (worker : Fin code.sites) (rival : Opponent code)

structure Failure where
  point : View (code := code)
  word : Word (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)
  attempt : Attempt worker word point rival
  stopped : match attempt with | .paid _ _ _ => False | _ => True

namespace Path
variable {worker rival} {views : List (View (code := code))} {point : View (code := code)}
  {requested : List (Word (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))}

def failure : {views : List (View (code := code))} → {point : View (code := code)} →
    {requested : List (Word (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))} →
    {rival : Opponent code} → Path worker views point requested rival → Option (Failure worker rival)
  | _,_,_,_,.complete => none
  | _,point,word::_,_,.unsupported outside => some ⟨point,word,.unsupported outside,True.intro⟩
  | _,point,word::_,_,.withheld supported different => some ⟨point,word,.withheld supported different,True.intro⟩
  | _,point,word::_,_,.refused supported emitted illegal => some ⟨point,word,.refused supported emitted illegal,True.intro⟩
  | _,_,_,_,.paid _ _ _ tail => tail.failure

theorem failure_is_at_the_first_unreplayed_word (path : Path worker views point requested rival) :
    path.failure.map Failure.word = requested[path.successful]? := by
  induction path with
  | complete => rfl
  | unsupported => rfl
  | withheld => rfl
  | refused => rfl
  | paid supported emitted legal tail ih => exact ih

def AcceptedPrefix : {views : List (View (code := code))} → {point : View (code := code)} →
    {requested : List (Word (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))} →
    {rival : Opponent code} → Path worker views point requested rival → Prop
  | _,_,_,_,.complete | _,_,_,_,.unsupported _ | _,_,_,_,.withheld _ _ | _,_,_,_,.refused _ _ _ => True
  | _,point,word::_,rival,.paid supported _ _ tail =>
      submitted point rival (protocol worker word supported) = word ∧
      Open.Legal code.law (before point rival (protocol worker word supported)) word ∧ tail.AcceptedPrefix

theorem all_earlier_words_were_actually_submitted_and_legal (path : Path worker views point requested rival) :
    path.AcceptedPrefix := by
  induction path with
  | complete => trivial
  | unsupported => trivial
  | withheld => trivial
  | refused => trivial
  | paid supported emitted legal tail ih => exact ⟨emitted,legal,ih⟩

theorem final_is_the_original_actual_rule_fold (path : Path worker views point requested rival) :
    path.final.point = path.rules.foldl (fun current rule => current.after rule rival) point.point := by
  unfold final
  generalize path.rules = rules
  clear path
  induction rules generalizing point with
  | nil => rfl
  | cons rule rest ih => exact ih

theorem the_entire_original_financial_prefix_is_retained
    (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument))
    {worker : Fin model.source.code.sites}
    {views : List (View (code := model.source.code))} {point : View (code := model.source.code)}
    {requested : List (Word (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))}
    {rival : Opponent model.source.code}
    (path : Path worker views point requested rival)
    (ordinal : Nat) (earlier : ordinal ≤ arrival point.point) :
    Native.Coupling.Match model.source.code point.point.source.input path.final.point.source.input
      (Financial.accountAt point.point.source.input ordinal)
      (Financial.accountAt path.final.point.source.input ordinal) := by
  rw [final_is_the_original_actual_rule_fold]
  exact Installation.Chain.fold_keeps_the_complete_native_financial_prefix
    (model := model) point.point rival path.rules ordinal earlier

end Path

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay
