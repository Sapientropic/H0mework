import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Refusal.Raw

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Iteration
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed Distributed.Reaction
open Input.Challenge.Redress.Shared.Iteration
open Budget.Programme.Debt Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole
open Computation.Search.Segmented.Publication.Learning.Paid
open Owned.PublicTask.Local Owned.PublicTask.Local.Inquiry Owned.PublicTask.Local.Inquiry.Planning
noncomputable section

namespace Current

structure Step (state : Current) where
  private mk ::
  original : GlobalPolicy.Output state.task
  generated : original = GlobalPolicy.produce state.task
  recovery : Option (Refusal.Result state)
  recovery_exact : recovery = match original with
    | .rejected _ => Refusal.produce state
    | .generated .. => none

structure Transition (state : Current) where
  target : Current
  native : Input.Event.Evolution state.cursor.saved target.cursor.saved

/-- Keep the dependent endpoint and its actual path in one branch result. -/
def Step.transition {state : Current} (step : Step state) : Transition state :=
  match step.original,step.recovery with
  | .rejected _,none => ⟨opened state,state.opening⟩
  | .rejected _,some made => ⟨made.nextCurrent,made.native⟩
  | .generated _ made,_ => ⟨after state made,afterNative state made⟩

def Step.target {state : Current} (step : Step state) : Current := step.transition.target

def Step.native {state : Current} (step : Step state) :
    Input.Event.Evolution state.cursor.saved step.target.cursor.saved :=
  step.transition.native

def produce (state : Current) : Step state :=
  match generated : GlobalPolicy.produce state.task with
  | .rejected row =>
      match recovered : Refusal.produce state with
      | none => ⟨.rejected row,generated.symm,none,recovered.symm⟩
      | some made => ⟨.rejected row,generated.symm,some made,recovered.symm⟩
  | .generated cache made => ⟨.generated cache made,generated.symm,none,rfl⟩

def Step.blocked {state : Current} (step : Step state) : Bool :=
  match step.original,step.recovery with
  | .rejected _,none => true
  | _,_ => false

theorem Step.repaired_refusal_uses_its_actual_successor {state : Current} (step : Step state)
    (row : Selection.Rejection state.task.model state.task.domain state.task.original state.task.baseline state.task.baseline)
    (rejected : step.original = .rejected row) (made : Refusal.Result state)
    (recovered : step.recovery = some made) : step.target = made.nextCurrent := by
  simp only [Step.target,Step.transition,rejected,recovered]

theorem Step.an_actual_recovery_does_not_stop_recursion {state : Current} (step : Step state)
    (made : Refusal.Result state) (recovered : step.recovery = some made) : step.blocked = false := by
  cases original : step.original <;> simp only [Step.blocked,original,recovered]

theorem Step.original_services_keep_their_actual_successor {state : Current} (step : Step state)
    {cache : Inquiry.Frame state.task} (made : GlobalPolicy.Service state.task cache)
    (selected : step.original = .generated cache made) :
    step.target = after state made ∧ step.blocked = false := by
  cases recovered : step.recovery <;> simp only [Step.target,Step.transition,Step.blocked,selected,recovered,and_self]

theorem Step.an_unrepaired_refusal_keeps_the_original_task {state : Current} (step : Step state)
    (row : Selection.Rejection state.task.model state.task.domain state.task.original state.task.baseline state.task.baseline)
    (rejected : step.original = .rejected row) (absent : step.recovery = none) :
    step.target.task = state.task ∧ step.blocked = true := by
  simp only [Step.target,Step.transition,Step.blocked,rejected,absent,opened,and_self]

/-- Finite observation follows the exact generated Current. It never recompiles
an entered round from a bare packet or treats an observation bound as terminal. -/
inductive Run : Current → Nat → Type where
  | observed (state : Current) : Run state 0
  | blocked {state : Current} {count : Nat} (step : Step state)
      (generated : step = produce state) (blocked : step.blocked = true) : Run state (count+1)
  | entered {state : Current} {count : Nat} (step : Step state)
      (generated : step = produce state) (live : step.blocked ≠ true)
      (later : Run step.target count) : Run state (count+1)

def execute : (count : Nat) → (state : Current) → Run state count
  | 0,state => .observed state
  | count+1,state =>
      let step := produce state
      if blocked : step.blocked = true then .blocked step rfl blocked
      else .entered step rfl blocked (execute count step.target)

namespace Run

def finishCurrent : {state : Current} → {count : Nat} → Run state count → Current
  | _,_,.observed state => state
  | _,_,.blocked step _ _ => step.target
  | _,_,.entered _ _ _ later => later.finishCurrent

def native {state : Current} {count : Nat} (run : Run state count) :
    Input.Event.Evolution state.cursor.saved run.finishCurrent.cursor.saved := by
  induction run with
  | observed => exact .same _
  | blocked step => exact step.native
  | entered step generated live later ih => exact .append step.native ih

end Run
end Current

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Iteration
