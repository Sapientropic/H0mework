import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 32768

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Recovery

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
  (requested : List (Word (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))) (rival : Opponent model.source.code)

abbrev original := Replay.Recovery.path model views point worker requested rival
abbrev template := Replay.Recovery.template model views point worker requested rival

inductive Result where
  | absent (noTemplate : template model views point worker requested rival = none)
  | unavailable (next : Template (code := model.source.code))
      (generated : template model views point worker requested rival = some next)
      (noActivation : Debt.activation next = none)
  | continued (next : Template (code := model.source.code))
      (generated : template model views point worker requested rival = some next)
      (selected : Activation next) (registered : Debt.activation next = some selected)
      (history : Path next selected (original model views point worker requested rival).finalViews
        (original model views point worker requested rival).final rival)
      (exact : history = Suffix.produce next selected (original model views point worker requested rival).finalViews
        (original model views point worker requested rival).final rival)

def generate : Result model views point worker requested rival :=
  match generated : template model views point worker requested rival with
  | none => .absent generated
  | some next => match registered : Debt.activation next with
    | none => .unavailable next generated registered
    | some selected => .continued next generated selected registered
        (Suffix.produce next selected (original model views point worker requested rival).finalViews
          (original model views point worker requested rival).final rival) rfl

variable {model views point worker requested rival}

def Result.final : Result model views point worker requested rival → View (code := model.source.code)
  | .absent _ | .unavailable _ _ _ => (original model views point worker requested rival).final
  | .continued _ _ _ _ history _ => history.final

def Result.finalViews : Result model views point worker requested rival → List (View (code := model.source.code))
  | .absent _ | .unavailable _ _ _ => (original model views point worker requested rival).finalViews
  | .continued _ _ _ _ history _ => history.finalViews

def Result.rules : Result model views point worker requested rival → List (Distributed.Recall.Information.Agency.Protocol.Rule model.source.code)
  | .absent _ | .unavailable _ _ _ => []
  | .continued _ _ _ _ history _ => history.rules

def Result.Legal : Result model views point worker requested rival → Prop
  | .absent _ | .unavailable _ _ _ => True
  | .continued _ _ _ _ history _ => history.Legal

theorem Result.all_new_actual_submissions_are_legal (result : Result model views point worker requested rival) : result.Legal := by
  cases result with
  | absent | unavailable => trivial
  | continued next generated selected registered history exact => exact history.all_new_actual_submissions_are_legal

theorem Result.final_is_its_original_actual_rule_fold (result : Result model views point worker requested rival) :
    result.final.point = result.rules.foldl (fun current rule => current.after rule rival)
      (original model views point worker requested rival).final.point := by
  cases result with
  | absent | unavailable => rfl
  | continued next generated selected registered history exact => exact history.final_is_the_original_actual_rule_fold

theorem Result.final_keeps_the_original_debt_knowledge (result : Result model views point worker requested rival)
    (covered : Knowledge.Contains views point) : Knowledge.Contains result.finalViews result.final := by
  have known := (original model views point worker requested rival).final_keeps_the_actual_original_debt covered
  cases result with
  | absent | unavailable => exact known
  | continued next generated selected registered history exact => exact history.final_keeps_the_actual_original_debt known

theorem Result.never_erases_the_historical_refusal (result : Result model views point worker requested rival)
    (refused : (seed (original model views point worker requested rival).final.point).frame.localLegal = false) :
    (seed result.final.point).frame.localLegal = false := by
  cases result with
  | absent | unavailable => exact refused
  | continued next generated selected registered history exact => exact history.no_actual_suffix_clears_a_historical_refusal refused

theorem Result.spends_only_the_original_remaining_budget (result : Result model views point worker requested rival) :
    (seed result.final.point).remaining + result.rules.length =
      (seed (original model views point worker requested rival).final.point).remaining := by
  cases result with
  | absent | unavailable => exact Nat.add_zero _
  | continued next generated selected registered history exact => exact history.every_executed_cut_spends_the_original_budget

variable (model views point worker requested rival)

abbrev finish := (generate model views point worker requested rival).final
def executed := (original model views point worker requested rival).rules ++
  (generate model views point worker requested rival).rules

theorem finish_is_the_single_actual_rule_fold :
    (finish model views point worker requested rival).point = Installation.Chain.fold (model := model)
      point.point rival (executed model views point worker requested rival) := by
  rw [Installation.Chain.fold,executed,List.foldl_append,
    ←Replay.Path.final_is_the_original_actual_rule_fold]
  exact (generate model views point worker requested rival).final_is_its_original_actual_rule_fold

abbrev bound := Replanning.native model (finish model views point worker requested rival).point
abbrev facade := Native.AuthorityRuntime.facade (bound model views point worker requested rival)
abbrev activated (n : Nat) := Runtime.readState (bound model views point worker requested rival)
  (depth (finish model views point worker requested rival).point+n)
abbrev native (n : Nat) := Runtime.read (bound model views point worker requested rival)
  (depth (finish model views point worker requested rival).point+n)

theorem the_original_root_consumes_legal_suffix_failure_finance_and_own_next
    (covered : Knowledge.Contains views point) (n : Nat) :
    let result := generate model views point worker requested rival
    let current := activated model views point worker requested rival n
    result.Legal ∧ Knowledge.Contains result.finalViews result.final ∧
      ((seed (original model views point worker requested rival).final.point).frame.localLegal = false →
        (seed result.final.point).frame.localLegal = false) ∧
      (seed result.final.point).remaining+result.rules.length =
        (seed (original model views point worker requested rival).final.point).remaining ∧
      (∀ ordinal ≤ arrival point.point,Native.Coupling.Match model.source.code point.point.source.input
        result.final.point.source.input (Financial.accountAt point.point.source.input ordinal)
        (Financial.accountAt result.final.point.source.input ordinal)) ∧
      (native model views point worker requested rival n).joint.finance =
        Financial.accountAt result.final.point.source.input (arrival result.final.point+n+1) ∧
      HEq ((facade model views point worker requested rival).readoutAt current .responsibilities)
        (current.tick.generated.projectionOutcome (.component ())) ∧
      HEq current.tick.generated.wholeLedgerWriteBack
        (current.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current.current.visit.current) ∧
      current.tick.nextCurrent = (facade model views point worker requested rival).process.stateAt
        ((facade model views point worker requested rival).process.successor current.state) := by
  let result := generate model views point worker requested rival
  let current := activated model views point worker requested rival n
  have rooted := (facade model views point worker requested rival).readoutAt_factorizes current .responsibilities
  refine ⟨result.all_new_actual_submissions_are_legal,result.final_keeps_the_original_debt_knowledge covered,
    result.never_erases_the_historical_refusal,result.spends_only_the_original_remaining_budget,?_,?_,
    rooted.2.2.2.1,rooted.2.2.1,rooted.2.2.2.2⟩
  · intro ordinal earlier
    change Native.Coupling.Match _ _ (finish model views point worker requested rival).point.source.input _ _
    rw [finish_is_the_single_actual_rule_fold]
    exact Installation.Chain.fold_keeps_the_complete_native_financial_prefix (model := model)
      point.point rival (executed model views point worker requested rival) ordinal earlier
  · rw [(native model views point worker requested rival n).joint_exact]
    have account := (Native.generate result.final.point.source (depth result.final.point+n)).finance_exact
    have address : depth result.final.point+n+2 = arrival result.final.point+n+1 := by
      dsimp only [depth,arrival];omega
    rw [address] at account
    exact account

abbrev forWorld (budget : Nat) (world : Distributed.Recall.Information.World model budget) :=
  facade model (completeViews model budget) (ofWorld model budget world) worker requested rival

theorem every_source_generated_world_keeps_its_actual_original_debt_without_a_coverage_premise
    (budget : Nat) (world : Distributed.Recall.Information.World model budget) :
    let result := generate model (completeViews model budget) (ofWorld model budget world) worker requested rival
    Knowledge.Contains result.finalViews result.final :=
  (generate model (completeViews model budget) (ofWorld model budget world) worker requested rival).final_keeps_the_original_debt_knowledge
    (Knowledge.member _ _ (every_source_generated_world_is_in_the_information_domain model budget world))

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Recovery
