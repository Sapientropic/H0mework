import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Reservation.Feedback.Asynchronous.Round

set_option autoImplicit false
set_option maxRecDepth 65536
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Budget.Programme.Debt Budget.Programme.Debt.Information Budget.Programme.Debt.Information.Inquiry
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole
open Prefix
open PublicFunction.Protocol.SymbolicAuthentication
open Publication.Reservation.Feedback.Asynchronous

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]

/-- Task data and a replaceable planning implementation. The source still checks
its own initial cache and each actual update. -/
structure Task where
  model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)
  domain : List (Cursor model.source.code)
  original : Prefix.Rule model.source.code
  baseline : Program model.source.code (horizon domain)
  point : View (code := model.source.code)
  rival : Opponent model.source.code
  reader : Fin model.source.code.sites
  quote : Charge.Quote (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)
  vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)
  encoding : StageTransport.Encoding (code := model.source.code)
  law : StageReception.Law model.source.code
  continueUnreserved : Bool := false
  planner : Rolling.Receipt.Planner model := Rolling.Receipt.defaultPlanner model
  /-- Any implementation must decide the unchanged full original relation. -/
  initialVerifier : Decidable (Selection.acceptable model domain original baseline baseline) := inferInstance

variable (task : Task (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))
abbrev Cache := Paid.State task.model task.domain task.original task.baseline (Cut.seed task.point.point).remaining

variable (state : Cache task)
def Owns : Prop :=
  let cursor := (state.current task.point task.rival).point
  Distributed.Recall.Information.Agency.ownerAt task.model.source.code cursor.ownerStart
    (EventStep.seed cursor).history.length = some task.reader
instance : Decidable (Owns task state) := by unfold Owns;infer_instance

def advance : Cache task :=
  Reception.refresh task.point task.rival task.reader task.vocabulary task.encoding task.law state.past.length
    (Driving.Progress.next state)

theorem advance_past : (advance task state).past = state.past ++ Driving.Progress.rules state :=
  Driving.Progress.the_next_cached_stage_is_paid_into_the_actual_past state

theorem advance_knowledge
    (covered : Knowledge.Contains state.beliefs (state.current task.point task.rival)) :
    Knowledge.Contains (advance task state).beliefs ((advance task state).current task.point task.rival) :=
  Reception.every_actual_new_receipt_preserves_actual_knowledge _ _ _ _ _ _ _ _ _
    (Driving.Progress.actual_local_knowledge_survives_the_cached_stage state _ _ covered)

/-- Waiting runs the accepted cache; the original learner is called only on its own live turn. -/
inductive Walk : Cache task → Type where
  | exhausted {state : Cache task} : Walk state
  | terminal {state : Cache task} (finished : ¬ Driving.Progress.Live state) : Walk state
  | learned {state : Cache task} (live : Driving.Progress.Live state) (owned : Owns task state)
      (decision : state.Decision task.reader) : Walk state
  | waiting {state : Cache task} (live : Driving.Progress.Live state) (foreign : ¬ Owns task state)
      (later : Walk (advance task state)) : Walk state

private def await : (fuel : Nat) → (state : Cache task) → Walk task state
  | 0, _ => .exhausted
  | fuel+1, state =>
      if live : Driving.Progress.Live state then
        if owned : Owns task state then .learned live owned (state.inspect task.reader)
        else .waiting live owned (await fuel (advance task state))
      else .terminal live

namespace Walk
variable {task state}
def final : {state : Cache task} → Walk task state → Cache task
  | state, .exhausted | state, .terminal _ => state
  | state, .learned _ _ decision =>
      advance task (state.commit task.reader (observation (state.current task.point task.rival) task.reader) decision)
  | _, .waiting _ _ later => later.final

def rules : {state : Cache task} → Walk task state → List (Prefix.Rule task.model.source.code)
  | _, .exhausted | _, .terminal _ => []
  | state, .learned _ _ decision =>
      Driving.Progress.rules (state.commit task.reader (observation (state.current task.point task.rival) task.reader) decision)
  | state, .waiting _ _ later => Driving.Progress.rules state ++ later.rules

def decision : {state : Cache task} → Walk task state → Option Bool
  | _, .exhausted | _, .terminal _ => none
  | _, .learned _ _ (.admitted _) => some true
  | _, .learned _ _ (.refused _) => some false
  | _, .waiting _ _ later => later.decision

def learnedAt : {state : Cache task} → Walk task state → Option Nat
  | _, .exhausted | _, .terminal _ => none
  | state, .learned .. => some state.past.length
  | _, .waiting _ _ later => later.learnedAt

def resolved : {state : Cache task} → Walk task state → Prop
  | _, .exhausted => False
  | _, .terminal _ | _, .learned .. => True
  | _, .waiting _ _ later => later.resolved

private theorem await_resolves (fuel : Nat) (cache : Cache task)
    (room : horizon task.domain < cache.past.length + fuel) :
    (await task fuel cache).resolved := by
  induction fuel generalizing cache with
  | zero => have inside := cache.within;omega
  | succ fuel ih =>
      unfold await
      split
      · rename_i live
        split
        · trivial
        · change (await task fuel (advance task cache)).resolved
          apply ih
          have moved : (advance task cache).past.length = cache.past.length+1 := by
            rw [advance_past]
            simp only [Driving.Progress.rules,if_pos live,List.length_append,List.length_singleton]
          omega
      · trivial

theorem the_source_bound_resolves_without_fuel_exhaustion (cache : Cache task) :
    (await task (horizon task.domain+1) cache).resolved :=
  await_resolves _ _ (by omega)

theorem past_is_the_literal_actual_word (walk : Walk task state) :
    walk.final.past = state.past ++ walk.rules := by
  induction walk with
  | exhausted | terminal => exact (List.append_nil _).symm
  | learned live owned decision =>
      rw [final,advance_past]
      rw [Paid.State.committing_the_stored_decision_preserves_all_paid_past]
      rfl
  | waiting live foreign later ih =>
      rw [final,ih,advance_past,List.append_assoc]
      rfl

theorem knowledge_survives (walk : Walk task state)
    (covered : Knowledge.Contains state.beliefs (state.current task.point task.rival)) :
    Knowledge.Contains walk.final.beliefs (walk.final.current task.point task.rival) := by
  induction walk with
  | exhausted | terminal => exact covered
  | @learned state live owned decision =>
      apply advance_knowledge
      have reading := Rolling.Receipt.the_actual_local_record_generates_its_own_covered_planning_domain
        state.beliefs (state.current task.point task.rival) covered task.reader
      cases decision <;> exact reading
  | @waiting state live foreign later ih => exact ih (advance_knowledge task state covered)
end Walk

inductive Turn (state : Cache task) where
  | unsupported (outside : Paid.request task.quote ∉ words task.model.source.code.actions task.model.source.code.actionLimit)
  | unreserved (supported : Paid.request task.quote ∈ words task.model.source.code.actions task.model.source.code.actionLimit)
      (missing : ¬ state.Booked (Paid.requestedRule task.reader task.quote supported))
  | unpaid (supported : Paid.request task.quote ∈ words task.model.source.code.actions task.model.source.code.actionLimit)
      (booked : state.Booked (Paid.requestedRule task.reader task.quote supported))
      (missing : ¬ Paid.funded state task.reader task.quote task.point task.rival)
  | paid (supported : Paid.request task.quote ∈ words task.model.source.code.actions task.model.source.code.actionLimit)
      (booked : state.Booked (Paid.requestedRule task.reader task.quote supported))
      (receipt : Paid.funded state task.reader task.quote task.point task.rival)
      (walk : Walk task (state.carry (Paid.requestedRule task.reader task.quote supported) booked))

/-- The actual fee is consumed once before waiting; waiting does not launch another solver. -/
def turn : Turn task state :=
  if supported : Paid.request task.quote ∈ words task.model.source.code.actions task.model.source.code.actionLimit then
    if booked : state.Booked (Paid.requestedRule task.reader task.quote supported) then
      if receipt : Paid.funded state task.reader task.quote task.point task.rival then
        .paid supported booked receipt (await task (horizon task.domain+1)
          (state.carry (Paid.requestedRule task.reader task.quote supported) booked))
      else .unpaid supported booked receipt
    else .unreserved supported booked
  else .unsupported supported

namespace Turn
variable {task state}
def resolved : Turn task state → Prop
  | .paid _ _ _ walk => walk.resolved
  | _ => True

theorem every_generated_request_resolves_its_paid_wait : (turn task state).resolved := by
  unfold turn
  split
  · split
    · split
      · exact Walk.the_source_bound_resolves_without_fuel_exhaustion _
      · trivial
    · trivial
  · trivial

def final : Turn task state → Cache task
  | .unsupported _ => state
  | .unreserved _ _ => if task.continueUnreserved then advance task state else state
  | .unpaid supported booked _ => state.carry (Paid.requestedRule task.reader task.quote supported) booked
  | .paid _ _ _ walk => walk.final

def rules : Turn task state → List (Prefix.Rule task.model.source.code)
  | .unsupported _ => []
  | .unreserved _ _ => if task.continueUnreserved then Driving.Progress.rules state else []
  | .unpaid supported _ _ => [Paid.requestedRule task.reader task.quote supported]
  | .paid supported _ _ walk => Paid.requestedRule task.reader task.quote supported :: walk.rules

def decision : Turn task state → Option Bool
  | .paid _ _ _ walk => walk.decision
  | _ => none

def learnedAt : Turn task state → Option Nat
  | .paid _ _ _ walk => walk.learnedAt
  | _ => none

theorem past_is_the_literal_actual_word (event : Turn task state) :
    event.final.past = state.past ++ event.rules := by
  cases event with
  | unsupported => exact (List.append_nil _).symm
  | unreserved =>
      change (if task.continueUnreserved then advance task state else state).past =
        state.past ++ (if task.continueUnreserved then Driving.Progress.rules state else [])
      split
      · exact advance_past task state
      · exact (List.append_nil _).symm
  | unpaid => rfl
  | paid supported booked receipt walk =>
      rw [final,Walk.past_is_the_literal_actual_word]
      change (state.past ++ [_]) ++ _ = _
      rw [List.append_assoc];rfl

theorem every_learned_result_has_its_original_actual_charge
    (event : Turn task state) (ordinal : Nat) (learned : event.learnedAt = some ordinal) :
    Charge.paid task.quote task.model task.reader (state.current task.point task.rival) task.rival
      (Charge.endAt task.quote task.model task.reader (state.current task.point task.rival) task.rival) := by
  cases event with
  | unsupported | unreserved | unpaid => cases learned
  | paid supported booked receipt walk =>
      exact Payment.a_ready_actual_request_generates_its_own_charge_receipt _ _ _ _ _ receipt
end Turn

def run : Nat → Cache task → Cache task
  | 0, state => state
  | fuel+1, state => run fuel (turn task state).final

def executed : Nat → Cache task → List (Prefix.Rule task.model.source.code)
  | 0, _ => []
  | fuel+1, state => (turn task state).rules ++ executed fuel (turn task state).final

theorem the_whole_run_locks_every_actual_fee_wait_and_selected_stage (fuel : Nat) (state : Cache task) :
    (run task fuel state).past = state.past ++ executed task fuel state := by
  induction fuel generalizing state with
  | zero => exact (List.append_nil _).symm
  | succ fuel ih =>
      rw [run,ih,Turn.past_is_the_literal_actual_word,List.append_assoc]
      rfl
end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned
