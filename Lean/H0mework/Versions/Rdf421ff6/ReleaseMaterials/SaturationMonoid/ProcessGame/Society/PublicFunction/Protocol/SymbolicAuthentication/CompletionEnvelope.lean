import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.BatchReentryRuntime

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CompletionEnvelope

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}

def available (baseline : Nat) (before : Feedback.State code) : List (Choice code) :=
  code.eventAlphabet.attach.filter fun event => match event.val with
    | .deliver serial => decide (serial < before.frame.sent.length ∧
        serial ∉ QueueScheduler.attempted code baseline before.past)
    | _ => false

abbrev fresh (start current : Cursor code) := available (OriginQueue.baseline start) (EventStep.seed current)

-- Only external turns with a real pending packet spend this allowance.
-- A delivery attempt resets it; payment is checked separately.
def gap (start : Cursor code) (rows : List (StageTrace.Record (code := code))) : Nat :=
  rows.foldl (fun count row => match row.call with
    | .external move => if (available (OriginQueue.baseline start) row.before).isEmpty then 0 else
      match Distributed.Recall.Information.Agency.externalChoice code move with
      | some event => match event.val with | .deliver _ => 0 | _ => count + 1
      | none => count + 1
    | _ => count) 0

def choices (start : Cursor code) (past : List (EventHistory.Stage (code := code))) (allowance : Nat) : List (Move code) :=
  let current := EventHistory.execute start past
  if (Distributed.Recall.Information.Agency.ownerAt code current.ownerStart (EventStep.seed current).history.length).isSome then [none]
  else match fresh start current with
    | [] => [none]
    | head :: tail =>
      if gap start (StageTrace.records start past) < allowance then none :: ((head :: tail).map some)
      else (head :: tail).map some

theorem the_generated_communication_domain_is_nonempty
    (start : Cursor code) (past : List (EventHistory.Stage (code := code))) (allowance : Nat) :
    choices start past allowance ≠ [] := by
  dsimp only [choices]
  split_ifs
  all_goals
    cases fresh start (EventHistory.execute start past) <;> simp

theorem every_generated_delivery_has_a_real_fresh_admitted_packet
    (start current : Cursor code) (event : Choice code) (member : event ∈ fresh start current) :
    ∃ serial, event.val = .deliver serial ∧ serial ∈ QueueScheduler.admitted code ∧
      serial < (EventStep.seed current).frame.sent.length ∧
      serial ∉ QueueScheduler.attempted code (OriginQueue.baseline start) (EventStep.seed current).past := by
  have checked := (List.mem_filter.mp member).2
  rcases event with ⟨event, supported⟩
  cases event <;> try contradiction
  rename_i serial
  have facts : serial < (EventStep.seed current).frame.sent.length ∧
      serial ∉ QueueScheduler.attempted code (OriginQueue.baseline start) (EventStep.seed current).past := of_decide_eq_true checked
  exact ⟨serial, rfl, List.mem_toFinset.mpr (List.mem_filterMap.mpr ⟨.deliver serial, supported, rfl⟩), facts⟩

def raw (current : Cursor code) (rival : Opponent code) : Move code :=
  if (Distributed.Recall.Information.Agency.ownerAt code current.ownerStart (EventStep.seed current).history.length).isSome
    then none else EventStep.selected current rival

def intake (current : Cursor code) (rival : Opponent code) : Move code :=
  Distributed.Recall.Information.Agency.externalChoice code (raw current rival)

structure Input (code : Code Party Good Port (Mandate.State Party Technology) Instrument) where
  cut : Nat
  raw : Move code
  admitted : Move code
  within : Bool

def observe (start : Cursor code) (past : List (EventHistory.Stage (code := code)))
    (allowance : Nat) (rival : Opponent code) : Input code :=
  let current := EventHistory.execute start past
  ⟨current.cut, raw current rival, intake current rival,
    decide (intake current rival ∈ choices start past allowance)⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CompletionEnvelope
