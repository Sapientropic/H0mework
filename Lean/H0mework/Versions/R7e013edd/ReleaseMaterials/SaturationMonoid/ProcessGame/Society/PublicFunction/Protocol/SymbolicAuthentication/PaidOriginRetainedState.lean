import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.PaidOriginQueueMemo
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 80000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.PaidOriginRetainedState
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open RenewedDispatchTrace PaidOriginQueueMemo
def retainedCheck (point : Cursor DispatchWindowSource.code) : Bool :=
 let trace := traceAt point
 let old := RenewedDispatchSource.code point
 let baseline := OriginQueue.baseline (RenewedDispatchSource.start point)
 decide (trace.cursor.cut = 86 ∧ trace.before.frame.sent.length = 8 ∧
  QueueScheduler.attempted old baseline trace.before.past = {0,1,2,3,4,5,6} ∧
  QueueScheduler.untried old baseline trace.before.past = {7})

private theorem retained_source_checked : retainedCheck point = true :=
 (congrArg retainedCheck point_is_the_incrementally_computed_paid_successor).trans (by decide +kernel)

theorem the_actual_successor_keeps_seven_attempts_and_one_pending_packet :
 saved.cut = 86 ∧ (EventStep.seed saved).frame.sent.length = 8 ∧
 QueueScheduler.attempted old (OriginQueue.baseline origin) (EventStep.seed saved).past = {0,1,2,3,4,5,6} ∧
 QueueScheduler.untried old (OriginQueue.baseline origin) (EventStep.seed saved).past = {7} := by
 have checked : retainedCheck point = true := retained_source_checked
 have facts : cache.cursor.cut = 86 ∧ cache.before.frame.sent.length = 8 ∧
  QueueScheduler.attempted old (OriginQueue.baseline origin) cache.before.past = {0,1,2,3,4,5,6} ∧
  QueueScheduler.untried old (OriginQueue.baseline origin) cache.before.past = {7} := by
  simpa only [retainedCheck,cache,origin,old,decide_eq_true_eq] using checked
 have seed : EventStep.seed saved = cache.before := saved_seed_is_the_actual_incremental_state
 exact ⟨(congrArg (fun cursor : Cursor old => cursor.cut) saved_is_the_actual_incremental_endpoint).trans facts.1,
  (congrArg (fun state : Feedback.State old => state.frame.sent.length) seed).trans facts.2.1,
  (congrArg (fun state : Feedback.State old => QueueScheduler.attempted old (OriginQueue.baseline origin) state.past) seed).trans facts.2.2.1,
  (congrArg (fun state : Feedback.State old => QueueScheduler.untried old (OriginQueue.baseline origin) state.past) seed).trans facts.2.2.2⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.PaidOriginRetainedState
