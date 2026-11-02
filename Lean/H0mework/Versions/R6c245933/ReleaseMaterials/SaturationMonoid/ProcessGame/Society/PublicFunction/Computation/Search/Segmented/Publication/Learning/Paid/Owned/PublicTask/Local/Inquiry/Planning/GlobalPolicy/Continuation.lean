import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned.PublicTask.Local.Inquiry.Planning.GlobalPolicy.Repair

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 600000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned.PublicTask.Local.Inquiry.Planning.GlobalPolicy.Continuation
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Budget.Programme.Debt Budget.Programme.Debt.Information Budget.Programme.Debt.Information.Inquiry
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole
open PublicFunction.Protocol.SymbolicAuthentication

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (task : Owned.Task (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

variable {task}

def Residual {cache : Inquiry.Frame task} : Service task cache → Type
  | .unavailable _ _ _ | .worldShort .. | .worldCompleted .. => Unit
  | .completed step _ _ _ outcome _ => match outcome with
      | .selected _ => Unit
      | .blocked rejected =>
          Repair.Response step.path.finish
            (rejected (Repair.remaining task step.path.finish step.path.finish.programme))

def resume {cache : Inquiry.Frame task} (made : Service task cache) : Residual made := match made with
  | .unavailable _ _ _ | .worldShort .. | .worldCompleted .. => ()
  | .completed step _ _ _ outcome _ => match outcome with
      | .selected _ => ()
      | .blocked rejected => Repair.respond step.path.finish
          (rejected (Repair.remaining task step.path.finish step.path.finish.programme))

variable {cache : Inquiry.Frame task}

def controls (made : Service task cache) (reply : Residual made) : List (Prefix.Rule task.model.source.code) :=
  match made,reply with
  | .unavailable step _ _,_ => step.path.finish.past
  | .worldShort ..,_ | .worldCompleted ..,_ => made.controls
  | .completed _ _ _ _ (.selected _) _,_ => made.controls
  | .completed _ _ _ _ (.blocked _) _,reply => reply.path.finish.past

def full (made : Service task cache) (reply : Residual made) : Cursor task.model.source.code :=
  match made,reply with
  | .unavailable _ _ _,_ | .worldShort ..,_ | .worldCompleted ..,_ => made.full
  | .completed _ _ _ _ (.selected _) _,_ => made.full
  | .completed _ _ _ _ (.blocked _) _,reply => reply.full

/-- A blocked comparison is retained; its next action is independently admitted or precisely refused. -/
def Contract (made : Service task cache) (reply : Residual made) : Prop :=
  made.Contract ∧ match made,reply with
  | .unavailable _ _ _,_ | .worldShort ..,_ | .worldCompleted ..,_ => True
  | .completed _ _ _ _ (.selected _) _,_ => True
  | .completed step _ _ _ (.blocked _) _,reply =>
      Inquiry.Preservation.Restoration.Accepts task step.path.finish.programme reply.path.finish.programme ∧
      Inquiry.Preservation.Settles task reply.path ∧
      reply.path.finish.past.length = step.path.finish.past.length+1 ∧
      reply.full = Splice.install (Planning.current task step.path.finish).point task.rival reply.path.word

theorem contract (made : Service task cache) (reply : Residual made) : Contract made reply := by
  refine ⟨made.contract,?_⟩
  cases made with
  | unavailable | worldShort | worldCompleted => trivial
  | completed step _ permit _ outcome _ =>
      cases outcome with
      | selected => trivial
      | blocked => exact ⟨reply.restores,reply.settles,reply.advances permit.live,reply.actual_source⟩

theorem complete_paid_prefix (made : Service task cache) (reply : Residual made)
    (visit : Nat) (earlier : visit ≤ arrival made.paidCurrent) :
    Native.Coupling.Match task.model.source.code made.paidCurrent.source.input (full made reply).source.input
      (Financial.accountAt made.paidCurrent.source.input visit) (Financial.accountAt (full made reply).source.input visit) := by
  cases made with
  | unavailable step generated missing => exact Service.complete_paid_prefix (.unavailable step generated missing) visit earlier
  | completed step generated permit paid outcome compiled =>
      cases outcome with
      | selected candidate =>
          exact Service.complete_paid_prefix (.completed step generated permit paid (.selected candidate) compiled) visit earlier
      | blocked => exact reply.complete_paid_prefix visit earlier


  | worldShort step generated permit paid input supplied rate declared missing =>
      exact Service.complete_paid_prefix (.worldShort step generated permit paid input supplied rate declared missing) visit earlier
  | worldCompleted step generated permit paid input supplied rate declared covered selected =>
      exact Service.complete_paid_prefix (.worldCompleted step generated permit paid input supplied rate declared covered selected) visit earlier

abbrev bound (made : Service task cache) (reply : Residual made) := Replanning.native task.model (full made reply)
abbrev facade (made : Service task cache) (reply : Residual made) := Native.AuthorityRuntime.facade (bound made reply)
abbrev activated (made : Service task cache) (reply : Residual made) :=
  Inquiry.Runtime.readState (bound made reply) (depth (full made reply))

theorem the_same_actual_root_consumes_the_generated_continuation_and_its_own_next
    (made : Service task cache) (reply : Residual made) :
    let active := activated made reply
    Contract made reply ∧
    HEq ((facade made reply).readoutAt active .responsibilities)
      (active.tick.generated.projectionOutcome (.component ())) ∧
    HEq active.tick.generated.wholeLedgerWriteBack
      (active.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt active.current.visit.current) ∧
    active.tick.nextCurrent = (facade made reply).process.stateAt ((facade made reply).process.successor active.state) := by
  have rooted := (facade made reply).readoutAt_factorizes (activated made reply) .responsibilities
  exact ⟨contract made reply,rooted.2.2.2.1,rooted.2.2.1,rooted.2.2.2.2⟩

variable (task)
def produce (cache : Inquiry.Frame task) :=
  let made := GlobalPolicy.invoke task cache
  Sigma.mk made (resume made)

theorem the_original_paid_service_generates_its_own_obstruction_driven_next (cache : Inquiry.Frame task) :
    Contract (produce task cache).1 (produce task cache).2 := contract _ _

end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned.PublicTask.Local.Inquiry.Planning.GlobalPolicy.Continuation
