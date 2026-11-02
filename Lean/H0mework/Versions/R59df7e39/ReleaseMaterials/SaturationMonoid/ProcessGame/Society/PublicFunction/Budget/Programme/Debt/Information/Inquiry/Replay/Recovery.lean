import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Failure

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 32768

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Recovery

open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (views : List (View (code := model.source.code))) (point : View (code := model.source.code))
  (worker : Fin model.source.code.sites)
  (requested : List (Word (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)))
  (rival : Opponent model.source.code)
  (reference : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code)

abbrev path := Replay.generate worker views point requested rival

def template : Option (Template (code := model.source.code)) :=
  match (path model views point worker requested rival).failure with
  | none => none
  | some failure => ((templates (code := model.source.code)).filter
      fun template => decide (template.request ∈ failure.word)).head?

theorem every_repair_template_comes_from_the_actual_first_failed_word
    (next : Template (code := model.source.code))
    (generated : template model views point worker requested rival = some next) :
    ∃ failure,(path model views point worker requested rival).failure = some failure ∧
      next ∈ templates (code := model.source.code) ∧ next.request ∈ failure.word := by
  unfold template at generated
  cases result : (path model views point worker requested rival).failure with
  | none => simp only [result] at generated;cases generated
  | some failure =>
    rw [result] at generated
    have member := List.mem_of_mem_head? generated
    have both := List.mem_filter.mp member
    exact ⟨failure,rfl,both.1,of_decide_eq_true both.2⟩

inductive Query where
  | absent (noTemplate : template model views point worker requested rival = none)
  | unavailable (next : Template (code := model.source.code))
      (generated : template model views point worker requested rival = some next)
      (noActivation : Debt.activation next = none)
  | reviewed (next : Template (code := model.source.code))
      (generated : template model views point worker requested rival = some next)
      (selected : Activation next) (registered : Debt.activation next = some selected)
      (decision : Review.Outcome model (path model views point worker requested rival).finalViews next selected reference)
      (exact : decision = Review.generate model (path model views point worker requested rival).finalViews next selected reference)

def query : Query model views point worker requested rival reference :=
  match generated : template model views point worker requested rival with
  | none => .absent generated
  | some next => match registered : Debt.activation next with
    | none => .unavailable next generated registered
    | some selected => .reviewed next generated selected registered
        (Review.generate model (path model views point worker requested rival).finalViews next selected reference) rfl

variable {model views point worker requested rival reference}

def Query.rule : Query model views point worker requested rival reference → Option (Distributed.Recall.Information.Agency.Protocol.Rule model.source.code)
  | .reviewed _ _ _ _ (.accepted rule _ _ _) _ => some rule
  | .absent _ | .unavailable _ _ _ | .reviewed _ _ _ _ (.unsupported _ _ _) _ |
      .reviewed _ _ _ _ (.rejected _ _ _ _) _ | .reviewed _ _ _ _ (.actualRefused _ _ _ _ _ _ _ _ _) _ => none

variable (model views point worker requested rival reference)

def finish : View (code := model.source.code) :=
  match (query model views point worker requested rival reference).rule with
  | none => (path model views point worker requested rival).final
  | some rule => Evidence.after (path model views point worker requested rival).final rule rival

def executed := (path model views point worker requested rival).rules ++
  (query model views point worker requested rival reference).rule.toList

def finalViews :=
  match (query model views point worker requested rival reference).rule with
  | none => (path model views point worker requested rival).finalViews
  | some rule => PublicDomain.next rule (path model views point worker requested rival).finalViews

theorem finish_is_one_original_actual_rule_fold :
    (finish model views point worker requested rival reference).point =
      Installation.Chain.fold (model := model) point.point rival (executed model views point worker requested rival reference) := by
  unfold finish executed
  cases result : (query model views point worker requested rival reference).rule with
  | none => simpa only [Option.toList_none,List.append_nil,Installation.Chain.fold] using
      Path.final_is_the_original_actual_rule_fold (path model views point worker requested rival)
  | some rule =>
    change ((path model views point worker requested rival).final.point.after rule rival) = _
    rw [Installation.Chain.fold,List.foldl_append]
    rw [←Path.final_is_the_original_actual_rule_fold]
    rfl

def Protected : Prop :=
  match (query model views point worker requested rival reference).rule with
  | none => (finish model views point worker requested rival reference).point.source =
      (path model views point worker requested rival).final.point.source
  | some rule => ∀ opponent : Opponent model.source.code,
      Synthesis.accepts model.source.code
        (economicAxes (path model views point worker requested rival).final.point.source
          (path model views point worker requested rival).final.point.cut)
        (Replanning.actualEvaluation model (path model views point worker requested rival).final.point rule opponent)
        (Replanning.actualEvaluation model (path model views point worker requested rival).final.point reference opponent)

theorem the_actual_failure_cannot_bypass_full_responsibility_admission
    (covered : Knowledge.Contains views point) : Protected model views point worker requested rival reference := by
  have known := (path model views point worker requested rival).final_keeps_the_actual_original_debt covered
  unfold Protected
  cases result : query model views point worker requested rival reference with
  | absent noTemplate => simp only [Query.rule,finish,result]
  | unavailable next generated noActivation => simp only [Query.rule,finish,result]
  | reviewed next generated selected registered decision exact =>
    cases decision with
    | accepted rule work events accepted =>
      simp only [Query.rule]
      intro opponent
      obtain ⟨representative,inside,matched⟩ := Knowledge.cursor_covered _ _ known
      exact (Acceptance.aligned_acceptance model representative _ matched opponent rule reference).mp
        ((Replanning.acceptable_iff_every_common_external_opponent model _ reference rule).mp accepted
          ⟨representative,inside⟩ opponent)
    | unsupported => simp only [Query.rule,finish,result]
    | rejected => simp only [Query.rule,finish,result]
    | actualRefused => simp only [Query.rule,finish,result]

abbrev bound := Replanning.native model (finish model views point worker requested rival reference).point
abbrev facade := Native.AuthorityRuntime.facade (bound model views point worker requested rival reference)
abbrev activated (n : Nat) := Runtime.readState (bound model views point worker requested rival reference)
  (depth (finish model views point worker requested rival reference).point+n)
abbrev native (n : Nat) := Runtime.read (bound model views point worker requested rival reference)
  (depth (finish model views point worker requested rival reference).point+n)

theorem the_original_root_consumes_first_failure_repair_finance_and_next
    (covered : Knowledge.Contains views point) (n : Nat) :
    let current := activated model views point worker requested rival reference n
    Protected model views point worker requested rival reference ∧
      (path model views point worker requested rival).failure.map Failure.word =
        requested[(path model views point worker requested rival).successful]? ∧
      (∀ ordinal ≤ arrival point.point,Native.Coupling.Match model.source.code point.point.source.input
        (finish model views point worker requested rival reference).point.source.input
        (Financial.accountAt point.point.source.input ordinal)
        (Financial.accountAt (finish model views point worker requested rival reference).point.source.input ordinal)) ∧
      (native model views point worker requested rival reference n).joint.finance =
        Financial.accountAt (finish model views point worker requested rival reference).point.source.input
          (arrival (finish model views point worker requested rival reference).point+n+1) ∧
      HEq ((facade model views point worker requested rival reference).readoutAt current .responsibilities)
        (current.tick.generated.projectionOutcome (.component ())) ∧
      HEq current.tick.generated.wholeLedgerWriteBack
        (current.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current.current.visit.current) ∧
      current.tick.nextCurrent = (facade model views point worker requested rival reference).process.stateAt
        ((facade model views point worker requested rival reference).process.successor current.state) := by
  let current := activated model views point worker requested rival reference n
  have rooted := (facade model views point worker requested rival reference).readoutAt_factorizes current .responsibilities
  refine ⟨the_actual_failure_cannot_bypass_full_responsibility_admission model views point worker requested rival reference covered,
    (path model views point worker requested rival).failure_is_at_the_first_unreplayed_word,?_,?_,
    rooted.2.2.2.1,rooted.2.2.1,rooted.2.2.2.2⟩
  · intro ordinal earlier
    rw [finish_is_one_original_actual_rule_fold]
    exact Installation.Chain.fold_keeps_the_complete_native_financial_prefix (model := model)
      point.point rival (executed model views point worker requested rival reference) ordinal earlier
  · rw [(native model views point worker requested rival reference n).joint_exact]
    have account := (Native.generate (finish model views point worker requested rival reference).point.source
      (depth (finish model views point worker requested rival reference).point+n)).finance_exact
    have index : depth (finish model views point worker requested rival reference).point+n+2 =
        arrival (finish model views point worker requested rival reference).point+n+1 := by
      dsimp only [depth,arrival];omega
    rw [index] at account
    exact account

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Recovery
