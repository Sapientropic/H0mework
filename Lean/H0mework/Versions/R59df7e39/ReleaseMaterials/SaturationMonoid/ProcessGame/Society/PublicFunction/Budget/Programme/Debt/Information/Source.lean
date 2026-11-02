import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information

set_option autoImplicit false
set_option maxHeartbeats 5000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information

open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}
  (views : List (View (code := code))) (template : Template (code := code))
  (selected : Activation template) (point : Cursor code)

abbrev target := Future.target point.source point.entry point.cut (environment template selected)
  [some (policy views template selected.site)]

abbrev actualExecution := (target views template selected point).actualExecution (depth point)

def nextPoint : Cursor code :=
  let next := target views template selected point
  ⟨next.reference,next.reference_generated,next.history,next.original,next.opponent,next.side,
    Future.takeover point.source point.entry point.cut (environment template selected),
    next.feedbackOverrides,point.cut+1,point.ownerStart⟩

theorem the_actual_activation_submits_only_locally_recovered_work :
    (actualExecution views template selected point).submitted =
      if (seed point).remaining = 0 then [] else
        code.action (policy views template selected.site) selected.site ((seed point).frame.inbox selected.site) := by
  change ((target views template selected point).actualExecution
    (point.source.history.length+1+(point.cut+0))).submitted = _
  rw [Future.future_word_is_actually_submitted point.source point.entry point.cut
    (environment template selected) [some (policy views template selected.site)] rfl 0]
  change Feedback.word code (some (policy views template selected.site))
    ⟨environment template selected,point.entry.budget⟩ (seed point) = _
  by_cases exhausted : (seed point).remaining = 0
  · simp only [Feedback.word,decision,exhausted,if_pos]
  · simp [Feedback.word,decision,exhausted,environment,stepLocal,Code.step]

theorem information_conflict_cannot_emit_an_old_debt_payment
    (actual : View (code := code))
    (empty : work views template selected.site (observation actual selected.site) = []) :
    (actualExecution views template selected actual.point).submitted = [] := by
  rw [the_actual_activation_submits_only_locally_recovered_work]
  have noWork : code.action (policy views template selected.site) selected.site
      ((seed actual.point).frame.inbox selected.site) = [] := by
    simp only [Code.action,policy_at]
    change (if code.memoryReady (observation actual selected.site) then
      work views template selected.site (observation actual selected.site) else []) = []
    rw [empty];exact ite_self _
  rw [noWork];exact ite_self _

theorem recovered_work_is_the_actual_original_share_word
    (actual : View (code := code))
    (correct : work views template selected.site (observation actual selected.site) = desired template actual)
    (budget : (seed actual.point).remaining ≠ 0)
    (memory : code.memoryReady (observation actual selected.site) = true) :
    (actualExecution views template selected actual.point).submitted = word actual.point actual.origin template := by
  rw [the_actual_activation_submits_only_locally_recovered_work,if_neg budget]
  simp only [Code.action,policy_at]
  change (if code.memoryReady (observation actual selected.site) then
    work views template selected.site (observation actual selected.site) else []) = _
  rw [memory,if_pos rfl,correct]

theorem actual_recovery_preserves_the_full_original_financial_prefix
    (ordinal : Nat) (earlier : ordinal ≤ arrival point) :
    Native.Coupling.Match code point.source.input (target views template selected point).input
      (Financial.accountAt point.source.input ordinal)
      (Financial.accountAt (target views template selected point).input ordinal) :=
  Future.complete_finance_before point.source point.entry point.cut (environment template selected)
    [some (policy views template selected.site)] rfl ordinal earlier

inductive ExecutionAnswer (actual : View (code := code)) where
  | uncertain (other : View (code := code)) (generated : other ∈ views)
      (same : observation other selected.site = observation actual selected.site)
      (different : desired template other ≠ desired template actual)
      (noAttempt : (actualExecution views template selected actual.point).submitted = [])
  | exhausted (budget : (seed actual.point).remaining = 0)
      (noAttempt : (actualExecution views template selected actual.point).submitted = [])
  | unavailableMemory (memory : code.memoryReady (observation actual selected.site) = false)
      (noAttempt : (actualExecution views template selected actual.point).submitted = [])
  | submitted (correct : (actualExecution views template selected actual.point).submitted =
      word actual.point actual.origin template)

def generateExecution (actual : View (code := code)) (generated : actual ∈ views) :
    ExecutionAnswer views template selected actual :=
  match recover views template selected.site actual generated with
  | .uncertain other present same different empty => .uncertain other present same different
      (information_conflict_cannot_emit_an_old_debt_payment views template selected actual empty)
  | .resolved correct =>
    if budget : (seed actual.point).remaining = 0 then
      .exhausted budget (by rw [the_actual_activation_submits_only_locally_recovered_work,if_pos budget])
    else if memory : code.memoryReady (observation actual selected.site) = true then
      .submitted (recovered_work_is_the_actual_original_share_word views template selected actual correct budget memory)
    else .unavailableMemory (Bool.eq_false_iff.mpr memory) (by
      rw [the_actual_activation_submits_only_locally_recovered_work,if_neg budget]
      simp only [Code.action,show code.memoryReady (observation actual selected.site) = false from
        Bool.eq_false_iff.mpr memory,Bool.false_eq_true,if_false])

def generateWorldExecution
    (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument)) (budget : Nat)
    (template : Template (code := model.source.code)) (selected : Activation template)
    (world : Distributed.Recall.Information.World model budget) :=
  generateExecution (completeViews model budget) template selected (ofWorld model budget world)
    (every_source_generated_world_is_in_the_information_domain model budget world)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information
