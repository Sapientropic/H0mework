import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DemandSchedulePolicy

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DemandScheduleExecution
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open RenewedQuorumConsumer (code)
open RenewedQuorumSource (fee)

inductive Status where
  | finished | resourceRefusal | windowExhausted
  deriving DecidableEq, Repr

structure Charge where
  row : StageTrace.Record (code := code)
  second : Bool
  submitted : row.submitted = [fee second]
  paid : code.law.Valid row.before.current (fee second)

structure Report where
  stages : List (EventHistory.Stage (code := code))
  charges : List Charge
  pending : List Bool
  status : Status
  state : Feedback.State code

def Report.served (report : Report) := report.charges.map Charge.second

def empty (before : Feedback.State code) (demands : List Bool) : Report :=
  ⟨[],[],demands,if demands.isEmpty then .finished else .windowExhausted,before⟩

def prepend (stage : EventHistory.Stage (code := code)) (report : Report) : Report :=
  {report with stages := stage :: report.stages}

def steps (available : Nat → Bool) (rivals : Nat → Opponent code) :
    Nat → (cursor : Cursor code) → (before : Feedback.State code) →
      before = EventStep.seed cursor → List Bool → Report :=
  Nat.rec (fun _ before _ demands => empty before demands) fun _ recur cursor before correct demands =>
    match demands with
    | [] => empty before []
    | second :: tail =>
      if before.remaining = 0 then empty before demands else
      let protocol := DemandSchedulePolicy.compile before.current (available cursor.cut) second
      let rival := rivals cursor.cut
      let row := DemandSchedulePolicy.materialAt cursor protocol rival before
      let nextCorrect := DemandSchedulePolicy.cached_after_is_the_same_source_successor cursor protocol rival before correct
      if actual : DemandSchedulePolicy.payer row = true then
        if paid : code.law.Valid row.before.current (fee second) then
          let rest := recur (cursor.after protocol rival) row.after nextCorrect tail
          {rest with
            stages := (protocol,rival) :: rest.stages
            charges := ⟨row,second,
              DemandSchedulePolicy.cached_payer_submits_the_original_fee cursor before correct _ _ rival actual,
              paid⟩ :: rest.charges}
        else ⟨[(protocol,rival)],[],demands,.resourceRefusal,row.after⟩
      else prepend (protocol,rival) (recur (cursor.after protocol rival) row.after nextCorrect demands)

-- The public horizon is the remaining budget of this exact source occurrence.
def run (cursor : Cursor code) (available : Nat → Bool) (rivals : Nat → Opponent code)
    (demands : List Bool) : Report :=
  steps available rivals (EventStep.seed cursor).remaining cursor (EventStep.seed cursor) rfl demands

def Sound (cursor : Cursor code) (demands : List Bool) (report : Report) : Prop :=
  report.served ++ report.pending = demands ∧
    (report.status = .finished ↔ report.pending = []) ∧
    (∀ charge ∈ report.charges, charge.row ∈ StageTrace.records cursor report.stages) ∧
    report.state = EventStep.seed (EventHistory.execute cursor report.stages)

theorem generated_steps_are_actual_ordered_paid_occurrences
    (available : Nat → Bool) (rivals : Nat → Opponent code) (n : Nat)
    (cursor : Cursor code) (before : Feedback.State code) (correct : before = EventStep.seed cursor)
    (demands : List Bool) :
    Sound cursor demands (steps available rivals n cursor before correct demands) := by
  induction n generalizing cursor before demands with
  | zero =>
    cases demands <;> simp [steps,empty,Sound,Report.served,StageTrace.records,EventHistory.execute,correct]
  | succ n ih =>
    cases demands with
    | nil => simp [steps,empty,Sound,Report.served,StageTrace.records,EventHistory.execute,correct]
    | cons second tail =>
      simp only [steps]
      split_ifs with stopped actual paid
      · simp [empty,Sound,Report.served,StageTrace.records,EventHistory.execute,correct]
      · obtain ⟨ordered,finished,inside,state⟩ := ih (cursor.after _ _) _
          (DemandSchedulePolicy.cached_after_is_the_same_source_successor _ _ _ _ correct) tail
        refine ⟨?_,finished,?_,state⟩
        · change second :: ((steps available rivals n (cursor.after _ _) _ _ tail).served ++
            (steps available rivals n (cursor.after _ _) _ _ tail).pending) = second :: tail
          rw [ordered]
        · intro charge member
          rcases List.mem_cons.mp member with first | later
          · subst charge
            exact List.mem_cons.mpr (Or.inl
              (DemandSchedulePolicy.cached_material_is_the_actual_occurrence _ _ _ _ correct))
          · exact List.mem_cons_of_mem _ (inside charge later)
      · exact ⟨rfl,by simp,by simp,
          DemandSchedulePolicy.cached_after_is_the_same_source_successor _ _ _ _ correct⟩
      · obtain ⟨ordered,finished,inside,state⟩ := ih (cursor.after _ _) _
          (DemandSchedulePolicy.cached_after_is_the_same_source_successor _ _ _ _ correct) (second :: tail)
        refine ⟨ordered,finished,?_,state⟩
        intro charge member
        exact List.mem_cons_of_mem _ (inside charge member)

theorem every_generated_charge_is_an_actual_paid_original_request
    (cursor : Cursor code) (available : Nat → Bool) (rivals : Nat → Opponent code)
    (demands : List Bool) (charge : Charge)
    (member : charge ∈ (run cursor available rivals demands).charges) :
    charge.row ∈ StageTrace.records cursor (run cursor available rivals demands).stages ∧
      charge.row.submitted = [fee charge.second] ∧
      code.law.Valid charge.row.before.current (fee charge.second) :=
  ⟨(generated_steps_are_actual_ordered_paid_occurrences available rivals _ cursor _ rfl demands).2.2.1 charge member,
    charge.submitted,charge.paid⟩

theorem every_report_state_is_the_same_original_source_state
    (cursor : Cursor code) (available : Nat → Bool) (rivals : Nat → Opponent code) (demands : List Bool) :
    (run cursor available rivals demands).state =
      EventStep.seed (EventHistory.execute cursor (run cursor available rivals demands).stages) :=
  (generated_steps_are_actual_ordered_paid_occurrences available rivals _ cursor _ rfl demands).2.2.2

theorem blocked_is_never_finished
    (cursor : Cursor code) (available : Nat → Bool) (rivals : Nat → Opponent code)
    (demands : List Bool) (blocked : (run cursor available rivals demands).pending ≠ []) :
    (run cursor available rivals demands).status ≠ .finished := by
  intro finished
  exact blocked ((generated_steps_are_actual_ordered_paid_occurrences available rivals _ cursor _ rfl demands).2.1.mp finished)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DemandScheduleExecution
