import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskInput.Work.Prefix
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Recovery.Metering.Assessment.Relation.Feed.Work.Prefix.Reconstruction

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskInput.Work.Reconstruction
open Institutions.Capitalism.Universal.Source.Program
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole
open Computation.Search.Segmented.Publication.Learning.Paid
open Input.Recovery.Metering.Assessment.Relation
noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {law : RawLaw Party Good Port Technology Instrument}
  {scope : Mandate.Scope (Party := Party) (Good := Good) (Port := Port)}
  (input : TaskInput law scope)
  (prior : Owned.Task (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

def units : Nat := by
  cases input with
  | actual inventory => exact Feed.Work.Reconstruction.units prior

  | received inventory _origin => exact Feed.Work.Reconstruction.units prior

def OriginalBatch : Type := by
  cases input with
  | actual inventory =>
      exact Feed.Work.Batch prior.model prior.domain prior.original prior.futureRequests inventory prior.recoveryPricing

  | received inventory _origin =>
      exact Feed.Work.Batch prior.model prior.domain prior.original prior.futureRequests inventory prior.recoveryPricing

def executeOriginal : OriginalBatch input prior := by
  cases input with
  | actual inventory =>
      exact Feed.Work.execute prior.model prior.domain prior.original prior.futureRequests inventory prior.recoveryPricing

  | received inventory _origin =>
      exact Feed.Work.execute prior.model prior.domain prior.original prior.futureRequests inventory prior.recoveryPricing

variable (original : OriginalBatch input prior)

def Batch : Type := by
  cases input with
  | actual inventory => exact Feed.Work.Reconstruction.Batch prior inventory original

  | received inventory _origin => exact Feed.Work.Reconstruction.Batch prior inventory original

def execute : Batch input prior original := by
  cases input with
  | actual inventory => exact Feed.Work.Reconstruction.execute prior inventory original

  | received inventory _origin => exact Feed.Work.Reconstruction.execute prior inventory original

variable (rebuilt : Batch input prior original)
  (past : List (Rule prior.model.source.code))
  (reference : Whole.Program prior.model.source.code (horizon prior.domain))

def Outcome : Type := by
  cases input with
  | actual inventory => exact Feed.Work.Prefix.Reconstruction.Outcome prior inventory past reference original rebuilt

  | received inventory _origin => exact Feed.Work.Prefix.Reconstruction.Outcome prior inventory past reference original rebuilt

def compile : Outcome input prior original rebuilt past reference := by
  cases input with
  | actual inventory => exact Feed.Work.Prefix.Reconstruction.compile prior inventory past reference original rebuilt

  | received inventory _origin => exact Feed.Work.Prefix.Reconstruction.compile prior inventory past reference original rebuilt

def candidate? (outcome : Outcome input prior original rebuilt past reference) :
    Option (Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Global.Candidate
      (tariff := prior.recoveryPricing) (requested := prior.futureRequests)
      prior.model prior.domain prior.original past reference) := by
  cases input with
  | actual inventory => exact Feed.Work.Prefix.Reconstruction.candidate? outcome

  | received inventory _origin => exact Feed.Work.Prefix.Reconstruction.candidate? outcome

def Reviewed (outcome : Outcome input prior original rebuilt past reference) : Prop := by
  cases input with
  | actual inventory => exact Feed.Work.Prefix.Reconstruction.Reviewed outcome

  | received inventory _origin => exact Feed.Work.Prefix.Reconstruction.Reviewed outcome

theorem reviewed (outcome : Outcome input prior original rebuilt past reference) :
    Reviewed input prior original rebuilt past reference outcome := by
  cases input with
  | actual inventory => exact Feed.Work.Prefix.Reconstruction.reviewed outcome

  | received inventory _origin => exact Feed.Work.Prefix.Reconstruction.reviewed outcome

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskInput.Work.Reconstruction
