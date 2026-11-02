import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskInput.Work.Reconstruction
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Recovery.Metering.Assessment.Relation.Feed.Work.Prefix.Autonomous

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskInput
open Institutions.Capitalism.Universal.Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {law : RawLaw Party Good Port Technology Instrument}
  {scope : Mandate.Scope (Party := Party) (Good := Good) (Port := Port)}

namespace Work.Actual
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole
open Computation.Search.Segmented.Publication.Learning.Paid
open Input.Recovery.Metering.Assessment.Relation
noncomputable section

variable (input : TaskInput law scope)
  (prior : Owned.Task (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

def units : Nat := by
  cases input with
  | actual inventory => exact TaskSource.Commitment.units prior + TaskSource.Commitment.Requests.units prior

  | received inventory origin => exact TaskSource.Commitment.units prior + TaskSource.Commitment.Requests.units prior + TaskSource.Commitment.Autonomous.units prior (origin.ancestors.length+1)

def Protection (past : List (Rule prior.model.source.code))
    (reference : Whole.Program prior.model.source.code (horizon prior.domain))
    (candidate : Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Global.Candidate
      (tariff := prior.recoveryPricing) (requested := prior.futureRequests)
      prior.model prior.domain prior.original past reference) : Prop := by
  cases input with
  | actual inventory => exact prior.worldCurrent.isSome = true ∧
      TaskSource.Commitment.NoWorse prior inventory past reference candidate.protocol

  | received inventory origin => exact prior.worldCurrent.isSome = true ∧
      TaskSource.Commitment.NoWorse prior inventory past reference candidate.protocol

/-- The post-response basis is compared with the candidate's actual successor. -/
def FutureProtection (past : List (Rule prior.model.source.code))
    (reference : Whole.Program prior.model.source.code (horizon prior.domain))
    (candidate : Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Global.Candidate
      (tariff := prior.recoveryPricing) (requested := prior.futureRequests)
      prior.model prior.domain prior.original past reference) : Prop := by
  cases input with
  | actual _inventory => exact True
  | received inventory origin =>
    exact ScopeForecast.NoWorse
      (TaskSource.Commitment.Autonomous.generate prior inventory past origin candidate.protocol).forecast
      (TaskSource.Commitment.Autonomous.baseline origin).forecast ∧
      TaskSource.Commitment.Autonomous.HistoryAccepts
        (TaskSource.Commitment.Autonomous.generateHistory prior inventory past origin candidate.protocol)

variable (original : Reconstruction.OriginalBatch input prior)

def QueryProtection
    (past : List (Rule prior.model.source.code))
    (reference : Whole.Program prior.model.source.code (horizon prior.domain))
    (candidate : Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Global.Candidate
      (tariff := prior.recoveryPricing) (requested := prior.futureRequests)
      prior.model prior.domain prior.original past reference) : Prop := by
  cases input with
  | actual inventory =>
      exact TaskSource.Commitment.Requests.Accepts prior inventory past original reference candidate.protocol
        (TaskSource.Commitment.Requests.execute prior inventory past candidate.protocol)

  | received inventory origin =>
      exact TaskSource.Commitment.Requests.Accepts prior inventory past original reference candidate.protocol
        (TaskSource.Commitment.Requests.execute prior inventory past candidate.protocol)

variable  (rebuilt : Reconstruction.Batch input prior original)
  (past : List (Rule prior.model.source.code))
  (reference : Whole.Program prior.model.source.code (horizon prior.domain))

def Outcome : Type := by
  cases input with
  | actual inventory => exact Feed.Work.Prefix.Actual.Outcome prior inventory past reference original rebuilt

  | received inventory origin => exact Feed.Work.Prefix.Autonomous.Outcome prior inventory past reference original rebuilt origin

def compile : Outcome input prior original rebuilt past reference := by
  cases input with
  | actual inventory => exact Feed.Work.Prefix.Actual.compile prior inventory past reference original rebuilt

  | received inventory origin => exact Feed.Work.Prefix.Autonomous.compile prior inventory past reference original rebuilt origin

def candidate? (outcome : Outcome input prior original rebuilt past reference) :
    Option (Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Global.Candidate
      (tariff := prior.recoveryPricing) (requested := prior.futureRequests)
      prior.model prior.domain prior.original past reference) := by
  cases input with
  | actual inventory => exact Feed.Work.Prefix.Actual.candidate? outcome

  | received inventory origin => exact Feed.Work.Prefix.Autonomous.candidate? outcome

def Reviewed (outcome : Outcome input prior original rebuilt past reference) : Prop := by
  cases input with
  | actual inventory => exact Feed.Work.Prefix.Actual.Reviewed outcome

  | received inventory origin => exact Feed.Work.Prefix.Autonomous.Reviewed outcome

theorem reviewed (outcome : Outcome input prior original rebuilt past reference) :
    Reviewed input prior original rebuilt past reference outcome := by
  cases input with
  | actual inventory => exact Feed.Work.Prefix.Actual.reviewed outcome

  | received inventory origin => exact Feed.Work.Prefix.Autonomous.reviewed outcome

theorem selected_keeps_the_original_queries (outcome : Outcome input prior original rebuilt past reference)
    (candidate : Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Global.Candidate
      (tariff := prior.recoveryPricing) (requested := prior.futureRequests)
      prior.model prior.domain prior.original past reference)
    (chosen : candidate? input prior original rebuilt past reference outcome = some candidate) :
    QueryProtection input prior original past reference candidate := by
  cases input with
  | actual inventory => exact Feed.Work.Prefix.Actual.selected_keeps_the_original_queries outcome candidate chosen

  | received inventory origin => exact Feed.Work.Prefix.Autonomous.selected_queries outcome candidate chosen

theorem selected_keeps_the_received_future (outcome : Outcome input prior original rebuilt past reference)
    (candidate : Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Global.Candidate
      (tariff := prior.recoveryPricing) (requested := prior.futureRequests)
      prior.model prior.domain prior.original past reference)
    (chosen : candidate? input prior original rebuilt past reference outcome = some candidate) :
    FutureProtection input prior past reference candidate := by
  cases input with
  | actual _inventory => trivial
  | received _inventory _origin => exact ⟨Feed.Work.Prefix.Autonomous.selected_future outcome candidate chosen,
      Feed.Work.Prefix.Autonomous.selected_ancestors outcome candidate chosen⟩

variable (candidate : Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Global.Candidate
  (tariff := prior.recoveryPricing) (requested := prior.futureRequests)
  prior.model prior.domain prior.original past reference)

theorem selected_has_its_actual_protection (outcome : Outcome input prior original rebuilt past reference)
    (chosen : candidate? input prior original rebuilt past reference outcome = some candidate) :
    Protection input prior past reference candidate := by
  cases input with
  | actual inventory => exact Feed.Work.Prefix.Actual.selected_has_its_actual_protection outcome candidate chosen

  | received inventory origin => exact Feed.Work.Prefix.Autonomous.selected_old_protection outcome candidate chosen

theorem protection_at_packet
    {actualLaw : RawLaw Bool Mandate.Financed.Good Mandate.Source.Port Unit Unit}
    {actualScope : Mandate.Scope (Party := Bool) (Good := Mandate.Financed.Good) (Port := Mandate.Source.Port)}
    (actualInput : TaskInput actualLaw actualScope)
    (actualTask : Owned.Task (Party := Bool) (Good := Mandate.Financed.Good) (Port := Mandate.Source.Port)
      (Technology := Unit) (Instrument := Unit))
    (actualPast : List (Rule actualTask.model.source.code))
    (actualReference : Whole.Program actualTask.model.source.code (horizon actualTask.domain))
    (actualCandidate : Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Global.Candidate
      (tariff := actualTask.recoveryPricing) (requested := actualTask.futureRequests)
      actualTask.model actualTask.domain actualTask.original actualPast actualReference) :
    Protection actualInput actualTask actualPast actualReference actualCandidate ↔
      actualTask.worldCurrent.isSome = true ∧
      TaskSource.Commitment.NoWorse actualTask actualInput.packet.2 actualPast actualReference actualCandidate.protocol := by
  cases actualInput with
  | actual inventory => rfl
  | received inventory _origin => rfl

end
end Work.Actual
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskInput
