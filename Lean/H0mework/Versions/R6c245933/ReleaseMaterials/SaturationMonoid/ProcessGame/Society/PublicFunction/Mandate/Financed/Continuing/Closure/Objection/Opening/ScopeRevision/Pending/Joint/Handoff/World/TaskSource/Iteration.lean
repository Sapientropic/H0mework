import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Iteration.Autonomous

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 600000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Iteration
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Input.Challenge.Redress.Shared.Iteration
noncomputable section

abbrev Step (state : Requests.Cursor) := Current.Step (Current.initial state)
def produce (state : Requests.Cursor) : Step state := Current.produce (Current.initial state)

/-- Explicit planner-only observation retains the original stopping behavior. -/
def executeLegacy (count : Nat) (state : Requests.Cursor) := Current.execute count (Current.initial state)

/-- First run the original planner/repair; every later round receives the own
word of that exact successor before calling its original planner again. -/
inductive Run (state : Requests.Cursor) : Nat → Type where
  | private observed : Run state 0
  | private entered {count : Nat} (first : Step state) (generated : first = produce state)
      (later : Current.Autonomous.Walk first.target count) : Run state (count+1)

def execute (count : Nat) (state : Requests.Cursor) : Run state count :=
  match count with
  | 0 => .observed
  | count+1 =>
      let first := produce state
      .entered first rfl (Current.Autonomous.execute first.target count)

namespace Run
variable {state : Requests.Cursor} {count : Nat}
def finishCurrent : {count : Nat} → Run state count → Current
  | _,.observed => Current.initial state
  | _,.entered _ _ later => later.finish

def finish (run : Run state count) : Requests.Cursor := run.finishCurrent.cursor

def native (run : Run state count) : Input.Event.Evolution state.saved run.finish.saved := by
  cases run
  next => exact .same _
  next first generated later => exact .append first.native later.native

def finance (run : Run state count) := Input.Event.Future.Expiry.Progress.Response.financeAlong run.native

def first? : {count : Nat} → Run state count → Option (Step state)
  | _,.observed => none
  | _,.entered first _ _ => some first

def sourceInputs : {count : Nat} → Run state count → List (List Action)
  | _,.observed => []
  | _,.entered _ _ later => later.inputs

theorem no_original_responsibility_is_erased (run : Run state count)
    (row : Input.Event.Future.Expiry.Progress.Responsibility.Row state.saved) :
    (Input.Event.Future.Expiry.Progress.Responsibility.transport run.native row).row.origin = row.origin ∧
    row.state.history <+: (Input.Event.Future.Expiry.Progress.Responsibility.transport run.native row).state.history ∧
    Nonempty ((Input.Event.Future.Expiry.Progress.Responsibility.transport run.native row).native.Run row.origin.initial
      (Input.Event.Future.Expiry.Progress.Responsibility.transport run.native row).state) :=
  ⟨(Input.Event.Future.Expiry.Progress.Responsibility.every_actual_step_retains_its_original_admission_and_history run.native row).1,
    (Input.Event.Future.Expiry.Progress.Responsibility.every_actual_step_retains_its_original_admission_and_history run.native row).2,
    ⟨Input.Event.Future.Expiry.Progress.Responsibility.completeOriginal run.native row⟩⟩

end Run
end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Iteration
