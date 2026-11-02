import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned

set_option autoImplicit false
set_option maxRecDepth 65536
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open Budget.Programme.Debt Budget.Programme.Debt.Information Budget.Programme.Debt.Information.Inquiry
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (task : Task (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

structure Audit where
  cache : Cache task
  live : Driving.Progress.Live cache
  owned : Owns task cache
  decision : cache.Decision task.reader

namespace Audit
variable {task} (audit : Audit task)
abbrev committed := audit.cache.commit task.reader
  (observation (audit.cache.current task.point task.rival) task.reader) audit.decision
abbrev rule := audit.committed.programme.at task.original audit.cache.past.length

theorem committed_past : audit.committed.past = audit.cache.past :=
  Paid.State.committing_the_stored_decision_preserves_all_paid_past _ _ _ _

theorem committed_live : Driving.Progress.Live audit.committed := by
  unfold Driving.Progress.Live
  rw [audit.committed_past]
  exact audit.live

theorem its_own_live_stage_is_really_executed :
    (advance task audit.committed).past = audit.cache.past ++ [audit.rule] := by
  rw [advance_past]
  unfold Driving.Progress.rules
  rw [if_pos audit.committed_live,audit.committed_past]
  unfold Driving.Progress.rule
  rw [audit.committed_past]

theorem an_admitted_stage_is_the_original_learned_rule
    (accepted : Selection.acceptable task.model task.domain task.original audit.cache.programme
      (audit.cache.proposal task.reader)) (made : audit.decision = .admitted accepted) :
    audit.rule = audit.cache.learned task.reader := by
  unfold rule committed
  rw [made]
  change (audit.cache.proposal task.reader).at task.original audit.cache.past.length = _
  change ((audit.cache.past ++ (audit.cache.learned task.reader :: audit.cache.programme.controls.drop
    (audit.cache.past.length+1))).take (horizon task.domain))[audit.cache.past.length]?.getD _ = _
  have live := audit.live.2
  rw [List.getElem?_take_of_lt live,List.getElem?_append_right (Nat.le_refl _)]
  simp only [Nat.sub_self,List.getElem?_cons_zero,Option.getD_some]
end Audit

namespace Walk
variable {task}
def audit : {cache : Cache task} → Walk task cache → Option (Audit task)
  | _, .exhausted | _, .terminal _ => none
  | cache, .learned live owned decision => some ⟨cache,live,owned,decision⟩
  | _, .waiting _ _ later => later.audit

theorem every_audited_update_is_its_actual_last_stage {cache : Cache task}
    (walk : Walk task cache) (record : Audit task) (found : walk.audit = some record) :
    walk.final.past = record.cache.past ++ [record.rule] := by
  induction walk with
  | exhausted | terminal => cases found
  | @learned cache live owned decision =>
      cases Option.some.inj found
      exact Audit.its_own_live_stage_is_really_executed (task := task) ⟨cache,live,owned,decision⟩
  | waiting live foreign later ih => exact ih found
end Walk

namespace Turn
variable {task} {cache : Cache task}
def audit : Turn task cache → Option (Audit task)
  | .paid _ _ _ walk => walk.audit
  | _ => none

def funded : Turn task cache → Bool
  | .paid .. => true
  | _ => false
private theorem carry_knowledge (supported : Paid.request task.quote ∈ words task.model.source.code.actions task.model.source.code.actionLimit)
    (booked : cache.Booked (Paid.requestedRule task.reader task.quote supported))
    (covered : Knowledge.Contains cache.beliefs (cache.current task.point task.rival)) :
    Knowledge.Contains (cache.carry (Paid.requestedRule task.reader task.quote supported) booked).beliefs
      ((cache.carry (Paid.requestedRule task.reader task.quote supported) booked).current task.point task.rival) := by
  have next := Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Observed.Transcript.every_actual_past_keeps_a_representative_in_the_same_public_domain
    [Paid.requestedRule task.reader task.quote supported] cache.beliefs (cache.current task.point task.rival) covered task.rival
  change Knowledge.Contains _ (Evidence.after (cache.current task.point task.rival) _ task.rival) at next
  rw [←Paid.State.carrying_a_reserved_request_is_the_actual_next_stage cache _ booked task.point task.rival] at next
  exact next

theorem knowledge_survives_every_actual_attempt_wait_and_owned_update (event : Turn task cache)
    (covered : Knowledge.Contains cache.beliefs (cache.current task.point task.rival)) :
    Knowledge.Contains event.final.beliefs (event.final.current task.point task.rival) := by
  cases event with
  | unsupported => exact covered
  | unreserved =>
      change Knowledge.Contains (if task.continueUnreserved then advance task cache else cache).beliefs
        ((if task.continueUnreserved then advance task cache else cache).current task.point task.rival)
      split
      · exact advance_knowledge task cache covered
      · exact covered
  | unpaid supported booked missing => exact carry_knowledge supported booked covered
  | paid supported booked receipt walk => exact walk.knowledge_survives (carry_knowledge supported booked covered)

end Turn

structure Report where
  before : Nat
  after : Nat
  paid : Bool
  learnedAt : Option Nat
  admitted : Option Bool
  deriving Repr

def report (cache : Cache task) (event : Turn task cache) : Report :=
  ⟨cache.past.length,event.final.past.length,event.funded,event.learnedAt,event.decision⟩

def reports : Nat → Cache task → List Report
  | 0, _ => []
  | fuel+1, cache => report task cache (turn task cache) :: reports fuel (turn task cache).final

theorem the_whole_run_preserves_actual_origin_knowledge (fuel : Nat) (cache : Cache task)
    (covered : Knowledge.Contains cache.beliefs (cache.current task.point task.rival)) :
    Knowledge.Contains (run task fuel cache).beliefs ((run task fuel cache).current task.point task.rival) := by
  induction fuel generalizing cache with
  | zero => exact covered
  | succ fuel ih => exact ih _ ((turn task cache).knowledge_survives_every_actual_attempt_wait_and_owned_update covered)


/-- One actual event is evaluated once and supplies both the next cache and its report. -/
def trace : Nat → Cache task → Cache task × List Report
  | 0, cache => (cache,[])
  | fuel+1, cache =>
      let event := turn task cache
      let later := trace fuel event.final
      (later.1,report task cache event :: later.2)

theorem trace_is_the_original_run_and_reports (fuel : Nat) (cache : Cache task) :
    trace task fuel cache = (run task fuel cache,reports task fuel cache) := by
  induction fuel generalizing cache with
  | zero => rfl
  | succ fuel ih => simp only [trace,ih,run,reports]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned
