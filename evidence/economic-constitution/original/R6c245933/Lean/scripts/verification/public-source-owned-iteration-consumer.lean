import SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Iteration
import SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Future.Regression

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.CountedRawRefusalConsumer
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle
open Mandate.Financed
open Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint
open Distributed Distributed.Reaction
open Computation.Search.Segmented.Publication.Learning.Paid
open Owned.PublicTask.Local.Inquiry.Planning
open Budget.Programme.Debt
open Input.Challenge.Redress.Shared.Iteration

abbrev authority := Future.Regression.ready
abbrev original := Future.Regression.inventory
def late := Joint.submit authority (Joint.submit authority original []) []
def reviewed := Future.advance authority late .revision

def check (label : String) (passed : Bool) : IO Unit := do
  unless passed do throw (IO.userError ("FAIL " ++ label))
  IO.println ("PASS " ++ label)
  (← IO.getStdout).flush

def branch {task : Owned.Task (Party := Bool) (Good := Good) (Port := Mandate.Source.Port)
    (Technology := Unit) (Instrument := Unit)} : GlobalPolicy.Output task → String
  | .rejected reason => "typed source rejection: " ++ match reason.row.test with
      | .legal => "legal" | .complete => "complete" | .profile => "profile"
      | .native => "native" | .economic _ => "economic"
  | .generated _ _ => "generated original Service"

def run : IO Unit := do
  IO.println "START public default execute 2 on the original nonempty World"
  (← IO.getStdout).flush
  let some fresh := Handoff.choose (Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.B authority) reviewed.inputs
    | throw (IO.userError "the source did not generate its revised scope")
  let saved := World.initial (Handoff.Continuation.initial authority late fresh (Handoff.generateEpoch authority late fresh))
  let raw : Requests.Cursor := ⟨⟨World.Epoch.ofFresh fresh,saved⟩,[]⟩
  check "the original World has old finance and public service responsibility"
    (decide (0 < saved.finance.current.slots.length ∧ 0 < saved.pastServices.length))
  IO.println "ENTER original public Iteration.execute 2; original planner/repair then actual own-source round"
  (← IO.getStdout).flush
  let actual := TaskSource.Iteration.execute 2 raw
  let some first := actual.first?
    | throw (IO.userError "FAIL the public default lost its original first step")
  IO.println ("FIRST " ++ branch first.original)
  (← IO.getStdout).flush
  check "the original first planner returns its typed refusal"
    (match first.original with | .rejected _ => true | .generated .. => false)
  let some repaired := first.recovery
    | throw (IO.userError "FAIL original raw refusal was not actually repaired")
  check "the original failed request is still offset 2 item 0"
    (decide (repaired.fault.offset.val = 2 ∧ repaired.fault.item.index = 0))
  check "the actual repair contains its original pending residual"
    (decide (repaired.response.next.pending.length = 2))
  let some basis := first.target.origin
    | throw (IO.userError "FAIL first actual successor lost its source basis")
  check "the actual first basis is the same repair response history"
    (decide (basis.first.2.inputs = repaired.response.next.saved.2.inputs))
  check "the actual first basis retains the same raw residual"
    (decide (basis.pending = repaired.response.report.residual))
  let own := Input.Event.Future.ownWord first.target.ready.2
  check "the public default receives exactly its successor source word"
    (decide (actual.sourceInputs = [own]))
  let arrived := actual.finishCurrent
  check "the source word remains in the next original Task directory"
    (decide (own ∈ arrived.task.futureRequests))
  let some carried := arrived.origin
    | throw (IO.userError "FAIL second actual successor lost all source ancestry")
  check "the second actual response adds one basis without dropping the first"
    (decide (carried.ancestors.length = basis.ancestors.length+1))
  let some previous := carried.ancestors.head?
    | throw (IO.userError "FAIL first source basis disappeared")
  check "the actual successor retains the earlier source history"
    (decide (previous.first.2.inputs = basis.first.2.inputs))
  check "the actual successor retains the earlier pending residual"
    (decide (previous.pending = basis.pending))
  check "the original full directory remains in the second actual Task"
    (decide (first.target.task.futureRequests.length ≤ arrived.task.futureRequests.length))
  IO.println s!"DEFAULT RETURN rounds=2 sourceWords={actual.sourceInputs.length} bases={carried.ancestors.length+1} pending={arrived.cursor.pending.length}"
  (← IO.getStdout).flush
  IO.println "DEFAULT ACTUAL CONTINUATION CONSUMER PASS: 12/12"
  (← IO.getStdout).flush

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.CountedRawRefusalConsumer
def main : IO Unit := SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.CountedRawRefusalConsumer.run
