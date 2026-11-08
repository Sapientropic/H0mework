import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.PaidOriginRetainedState
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 80000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.PaidOriginQueueChecks
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open RenewedDispatchTrace PaidOriginQueueMemo
@[irreducible] def rankOf
 (old : Code Bool Bool ProductiveMandateSource.Port (Mandate.State Bool Bool) Unit)
 (origin : Cursor old) (endpoint : Cursor (PaidInvocationSource.code old contract))
 (before : Feedback.State (PaidInvocationSource.code old contract)) : Nat :=
 endpoint.ownerStart-before.history.length+
  2*(QueueScheduler.untried (PaidInvocationSource.code old contract) (OriginQueue.baseline origin) before.past).card

def requiredAt (point : Cursor DispatchWindowSource.code) :=
 rankOf (RenewedDispatchSource.code point) (RenewedDispatchSource.start point) (fundedAt point) (fundedBeforeAt point)
def countAt (point : Cursor DispatchWindowSource.code) := min (requiredAt point) (fundedBeforeAt point).remaining
def finalAt (point : Cursor DispatchWindowSource.code) :=
 EventHistory.execute (fundedAt point) (OriginQueue.stages (liftedAt point) (fun _ => SilentWindow.quiet) (countAt point))

def queueCheck (point : Cursor DispatchWindowSource.code) : Bool :=
 decide (requiredAt point = 2 ∧ countAt point = 2 ∧
  decide (requiredAt point ≤ (fundedBeforeAt point).remaining) = true ∧
  (fundedAt point).cut = 88 ∧
  StageReception.delivered (firstAt point) 7 = false ∧ StageReception.delivered (secondAt point) 7 = true)

private theorem queue_source_checked : queueCheck point = true :=
 (congrArg queueCheck point_is_the_incrementally_computed_paid_successor).trans (by decide +kernel)

private theorem required_from_the_same_incremental_state
 (old : Code Bool Bool ProductiveMandateSource.Port (Mandate.State Bool Bool) Unit)
 (origin : Cursor old) (past : List (EventHistory.Stage (code := old)))
 (answer : PaidOriginQueue.Ready old contract origin past true true)
 (endpoint : Cursor (PaidInvocationSource.code old contract))
 (before : Feedback.State (PaidInvocationSource.code old contract))
 (same : answer.start = endpoint) (state : EventStep.seed endpoint = before) :
 answer.required = rankOf old origin endpoint before := by
 unfold rankOf PaidOriginQueue.Ready.required OriginQueue.horizon OriginQueue.warmup OriginQueue.initialRank
 rw [same,state,answer.original_baseline]

theorem required_is_the_original_incremental_rank : ready.required = requiredAt point :=
 required_from_the_same_incremental_state old origin past ready (fundedAt point)
  (fundedBeforeAt point) start_is_the_original_incremental_payment_endpoint
  funded_seed_is_the_original_incremental_state

theorem remaining_is_the_original_incremental_budget :
 (EventStep.seed start).remaining = (fundedBeforeAt point).remaining :=
 congrArg (fun before : Feedback.State code => before.remaining) actual_seed_is_the_original_incremental_state

theorem count_is_the_original_incremental_count : ready.count = countAt point :=
 congrArg₂ Nat.min required_is_the_original_incremental_rank remaining_is_the_original_incremental_budget

theorem final_is_the_original_incremental_execution : final = finalAt point :=
 congrArg₂ (fun (cursor : Cursor code) (count : Nat) =>
  EventHistory.execute cursor (OriginQueue.stages (liftedAt point) (fun _ => SilentWindow.quiet) count))
  start_is_the_original_incremental_payment_endpoint count_is_the_original_incremental_count

private theorem executed_cut (cursor : Cursor code) (stages : List (EventHistory.Stage (code := code))) :
 (EventHistory.execute cursor stages).cut = cursor.cut+stages.length := by
 induction stages generalizing cursor with
 | nil => rfl
 | cons stage tail ih =>
  change (EventHistory.execute (cursor.after stage.1 stage.2) tail).cut = _
  rw [ih]
  change cursor.cut+1+tail.length = cursor.cut+(tail.length+1)
  omega

theorem the_original_queue_generates_two_actual_steps_and_delivers_only_the_pending_packet :
 ready.required = 2 ∧ ready.count = 2 ∧ ready.complete = true ∧ start.cut = 88 ∧ final.cut = 90 ∧
 StageReception.delivered (ready.row 0) 7 = false ∧ StageReception.delivered row 7 = true ∧
 (OriginQueue.baseline (PaidOriginQueue.lifted old contract origin)) = OriginQueue.baseline origin := by
 have checked : queueCheck point = true := queue_source_checked
 have facts : requiredAt point = 2 ∧ countAt point = 2 ∧
  decide (requiredAt point ≤ (fundedBeforeAt point).remaining) = true ∧
  (fundedAt point).cut = 88 ∧
  StageReception.delivered (firstAt point) 7 = false ∧ StageReception.delivered (secondAt point) 7 = true := by
  simpa only [queueCheck,decide_eq_true_eq] using checked
 have finalClock : (finalAt point).cut = 90 := by
  unfold finalAt
  rw [executed_cut,OriginQueue.stage_count,facts.2.2.2.1,facts.2.1]
 have complete := congrArg₂ (fun required remaining : Nat => decide (required ≤ remaining))
  required_is_the_original_incremental_rank remaining_is_the_original_incremental_budget
 exact ⟨required_is_the_original_incremental_rank.trans facts.1,
  count_is_the_original_incremental_count.trans facts.2.1,complete.trans facts.2.2.1,
  (congrArg (fun cursor : Cursor code => cursor.cut) start_is_the_original_incremental_payment_endpoint).trans facts.2.2.2.1,
  (congrArg (fun cursor : Cursor code => cursor.cut) final_is_the_original_incremental_execution).trans finalClock,
  (congrArg (fun record : StageTrace.Record (code := code) => StageReception.delivered record 7) actual_first_is_the_incremental_row).trans facts.2.2.2.2.1,
  (congrArg (fun record : StageTrace.Record (code := code) => StageReception.delivered record 7) actual_second_is_the_incremental_row).trans facts.2.2.2.2.2,
  ready.original_baseline⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.PaidOriginQueueChecks
