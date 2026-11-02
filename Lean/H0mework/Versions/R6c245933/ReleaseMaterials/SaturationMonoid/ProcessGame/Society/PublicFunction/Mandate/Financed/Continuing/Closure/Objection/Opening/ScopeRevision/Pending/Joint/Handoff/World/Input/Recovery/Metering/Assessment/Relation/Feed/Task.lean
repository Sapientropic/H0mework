import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Recovery.Metering.Assessment.Relation.Feed
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Communication.Task.Core

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Recovery.Metering.Assessment.Relation.Feed
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole
open Computation.Search.Segmented.Publication.Learning.Paid
noncomputable section

variable (prior : Owned.Task (Party := Bool) (Good := Good) (Port := Mandate.Source.Port)
  (Technology := Unit) (Instrument := Unit)) (point : Distributed.Recall.Information.Agency.Protocol.Continuation.Cursor prior.model.source.code)
  {fuel : Nat} (program : Whole.Program prior.model.source.code fuel)
  (rival : Opponent prior.model.source.code)

/-- This is the candidate's emitter, including its own table, programme and
past. A common planning start cannot replace this endpoint. -/
def continuation : Distributed.Recall.Information.Agency.Protocol.Continuation.Cursor prior.model.source.code :=
  let actual := source prior.model point prior.original program rival
  let opponent := Future.jointOpponent point.source point.entry point.cut
    (Whole.controller point prior.original program rival)
  ⟨actual.reference,actual.reference_generated,actual.history,actual.original,actual.opponent,actual.side,
    Future.takeover point.source point.entry point.cut opponent,actual.feedbackOverrides,
    point.cut+Cut.horizon point.source point.entry point.cut,point.ownerStart⟩

theorem continuation_is_the_same_candidate_source :
    (continuation prior point program rival).source =
      source prior.model point prior.original program rival := rfl

theorem continuation_keeps_the_candidates_complete_frame :
    (continuation prior point program rival).source.feedbackState
      (continuation prior point program rival).entry (continuation prior point program rival).cut =
    (source prior.model point prior.original program rival).feedbackState
      (Future.takeover point.source point.entry point.cut
        (Future.jointOpponent point.source point.entry point.cut
          (Whole.controller point prior.original program rival)))
      (point.cut+Cut.horizon point.source point.entry point.cut) := rfl

variable {epoch : Epoch} (inventory : Inventory epoch) (word : List Action)

def continuedForecast := scopeForecast (window prior.model point prior.original program rival inventory)
  word (Runtime.read (window prior.model point prior.original program rival inventory).packet.2 word)

def continuedTask (intent : Intent) :=
  let actual := (continuedForecast prior point program rival inventory word).read intent
  TaskSource.Communication.task actual.next.saved.2 actual.next.pending prior
    (continuation prior point program rival)

def continuedAdmission (intent : Intent) :=
  Owned.Source.seed (continuedTask prior point program rival inventory word intent)

/-- Each original port's actual result owns the reconstruction costs, native
responsibilities and new World; the old-law cursor is retried there. -/
def continuedWindow (intent : Intent) : Window (⟨epoch,inventory⟩ : Packet) :=
  let actual := (continuedForecast prior point program rival inventory word).read intent
  ⟨⟨actual.next.saved.1,TaskSource.Communication.Source.saved actual.next.saved.2
      (continuation prior point program rival)⟩,
    .append (ScopeForecast.after actual).native
      (TaskSource.Communication.Source.native actual.next.saved.2 (continuation prior point program rival))⟩

theorem continued_task_uses_its_own_actual_world (intent : Intent) :
    (continuedTask prior point program rival inventory word intent).worldInput =
      some (.actual (continuedWindow prior point program rival inventory word intent).packet.2) := rfl

theorem continued_task_keeps_every_original_position (intent : Intent)
    (old : Distributed.Recall.Information.Agency.Protocol.Continuation.Cursor prior.model.source.code) (member : old ∈ prior.domain) :
    TaskSource.Communication.Source.cursor
      ((continuedForecast prior point program rival inventory word).read intent).next.saved.2 old ∈
      (continuedTask prior point program rival inventory word intent).domain :=
  TaskSource.Communication.every_original_position_is_reconstructed _ prior _ old member

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Recovery.Metering.Assessment.Relation.Feed
