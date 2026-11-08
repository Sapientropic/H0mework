import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DemandBallotConsumer
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.QueueScheduler

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DemandTransitSource
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open RenewedQuorumConsumer (code)
open DemandScheduleConsumer (original)
open DemandBallotSource (vocabulary ballots)

abbrev signed (callbacks : Nat → Opponent code) := DemandBallotSource.run original callbacks [true,true]
abbrev departure (callbacks : Nat → Opponent code) := EventHistory.execute original (signed callbacks).stages

def encoding (callbacks : Nat → Opponent code) : StageTransport.Encoding (code := code) := fun signal =>
  (ballots (signed callbacks)).find? fun vote => decide
    (vote.scope = RenewedQuorumSource.slot true ∧
      ((signal = 2 ∧ vote.key = 0) ∨ (signal = 3 ∧ vote.key = 1)))

theorem every_serialized_body_is_an_actual_paid_prefix_ballot
    (callbacks : Nat → Opponent code) (signal : Fin code.signals)
    (body : StageBudget.Ballot (code := code)) (serialized : encoding callbacks signal = some body) :
    body ∈ ballots (signed callbacks) ∧
      StageBudget.verify vocabulary original (signed callbacks).stages body = true := by
  have member := List.mem_of_find?_eq_some serialized
  refine ⟨member,?_⟩
  obtain ⟨charge,inside,issued⟩ := List.mem_filterMap.mp member
  have actual := (DemandScheduleExecution.generated_steps_are_actual_ordered_paid_occurrences
    (fun _ => true) callbacks _ original _ rfl [true,true]).2.2.1 charge inside
  apply decide_eq_true
  apply List.mem_flatMap.mpr
  refine ⟨charge.row,actual,List.mem_filterMap.mpr ⟨0,?_,issued⟩⟩
  apply List.mem_range.mpr
  rw [charge.submitted]
  simp only [List.length_singleton];omega

def compile (callbacks : Nat → Opponent code) (before : Feedback.State code) : Rule code :=
  ⟨⟨DemandSchedulePolicy.work true,DemandSchedulePolicy.work_generated true⟩,fun key _ =>
    if key.1 = 2 then
      if DemandRenewalStep.refill before.current then RenewedQuorumSource.activation _ _ _ key.1
      else ⟨none,List.mem_cons_self⟩
    else if decide (1 ≤ before.current.stock 1 .service) &&
        ((ballots (signed callbacks)).any fun vote => vote.key == key.1) &&
        !((before.frame.sent.drop (EventStep.seed (departure callbacks)).frame.sent.length).any fun packet => packet.sender == key.1)
      then RenewedQuorumSource.sending _ _ _ key.1 else ⟨none,List.mem_cons_self⟩⟩

def network (enabled : Bool) (before : Feedback.State code) : Opponent code :=
  if enabled && decide (1 ≤ before.current.stock 1 .service)
    then QueueScheduler.opponent code 0 else EventStep.fixed none

structure Trace where
  stages : List (EventHistory.Stage (code := code))
  state : Feedback.State code

def steps (callbacks : Nat → Opponent code) (enabled : Bool) :
    Nat → (cursor : Cursor code) → (before : Feedback.State code) → before = EventStep.seed cursor → Trace :=
  Nat.rec (fun _ before _ => ⟨[],before⟩) fun _ recur cursor before correct =>
    let protocol := compile callbacks before
    let rival := network enabled before
    let row := DemandSchedulePolicy.materialAt cursor protocol rival before
    let afterCorrect := DemandSchedulePolicy.cached_after_is_the_same_source_successor cursor protocol rival before correct
    let rest := recur (cursor.after protocol rival) row.after afterCorrect
    ⟨(protocol,rival) :: rest.stages,rest.state⟩

theorem every_generated_tail_uses_the_literal_same_source_successor
    (callbacks : Nat → Opponent code) (enabled : Bool) (n : Nat)
    (cursor : Cursor code) (before : Feedback.State code) (correct : before = EventStep.seed cursor) :
    (steps callbacks enabled n cursor before correct).stages.length = n ∧
      (steps callbacks enabled n cursor before correct).state =
        EventStep.seed (EventHistory.execute cursor (steps callbacks enabled n cursor before correct).stages) := by
  induction n generalizing cursor before with
  | zero => exact ⟨rfl,correct⟩
  | succ n ih =>
    obtain ⟨length,state⟩ := ih (cursor.after (compile callbacks before) (network enabled before)) _
      (DemandSchedulePolicy.cached_after_is_the_same_source_successor _ _ _ _ correct)
    exact ⟨congrArg Nat.succ length,state⟩

abbrev sourceState (callbacks : Nat → Opponent code) :
    (signed callbacks).state = EventStep.seed (departure callbacks) :=
  DemandScheduleExecution.every_report_state_is_the_same_original_source_state original (fun _ => true) callbacks [true,true]

def window (callbacks : Nat → Opponent code) : Nat :=
  min (2 * (2 * code.sites) + 1) (signed callbacks).state.remaining

abbrev tail (callbacks : Nat → Opponent code) (enabled : Bool) :=
  steps callbacks enabled (window callbacks) (departure callbacks) (signed callbacks).state (sourceState callbacks)
abbrev full (callbacks : Nat → Opponent code) (enabled : Bool) :=
  (signed callbacks).stages ++ (tail callbacks enabled).stages
abbrev final (callbacks : Nat → Opponent code) (enabled : Bool) :=
  EventHistory.execute original (full callbacks enabled)
abbrev reception (delay : Nat) := RenewedQuorumSource.reception RenewedQuorumConsumer.resources 2 true delay

def produce (callbacks : Nat → Opponent code) (enabled : Bool) (delay : Nat) :=
  InterfaceQuorum.produce original vocabulary (encoding callbacks) (reception delay)
    (full callbacks enabled) 2 (RenewedQuorumSource.slot true) 2

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DemandTransitSource
