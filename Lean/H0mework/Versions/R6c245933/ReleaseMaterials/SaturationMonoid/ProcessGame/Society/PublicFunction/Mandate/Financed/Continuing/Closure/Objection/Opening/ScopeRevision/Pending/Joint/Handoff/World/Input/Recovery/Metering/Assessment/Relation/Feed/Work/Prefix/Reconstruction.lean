import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Recovery.Metering.Assessment.Relation.Feed.Work.Prefix
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Recovery.Metering.Assessment.Relation.Feed.Work.Reconstruction

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Recovery.Metering.Assessment.Relation.Feed.Work.Prefix.Reconstruction
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole
open Computation.Search.Segmented.Publication.Learning.Paid
noncomputable section
variable (prior : Owned.Task (Party := Bool) (Good := Good) (Port := Mandate.Source.Port)
  (Technology := Unit) (Instrument := Unit)) {epoch : Epoch} (inventory : Inventory epoch)
  (past : List (Rule prior.model.source.code))
  (reference : Whole.Program prior.model.source.code (horizon prior.domain))
  (original : Work.Batch prior.model prior.domain prior.original prior.futureRequests inventory prior.recoveryPricing)
  (rebuilt : Work.Reconstruction.Batch prior inventory original)

abbrev Previous := Feed.Prefix.Candidate inventory prior.model prior.domain prior.original past reference
  prior.recoveryPricing prior.futureRequests

def originalPool := Work.Prefix.candidates inventory prior.model prior.domain prior.original past reference
  prior.recoveryPricing prior.futureRequests original

structure Candidate where
  previous : Previous prior inventory past reference
  accepted : Work.Reconstruction.Accepts rebuilt reference previous.protocol

def refine (candidate : Previous prior inventory past reference) :
    Option (Candidate prior inventory past reference original rebuilt) :=
  if kept : Work.Reconstruction.Accepts rebuilt reference candidate.protocol then some ⟨candidate,kept⟩ else none

/-- Strengthen the original complete pool before its first candidate is chosen. -/
def candidates := (originalPool prior inventory past reference original).filterMap
  (refine prior inventory past reference original rebuilt)

theorem every_preserving_original_candidate_is_generated
    (candidate : Previous prior inventory past reference)
    (member : candidate ∈ originalPool prior inventory past reference original)
    (accepted : Work.Reconstruction.Accepts rebuilt reference candidate.protocol) :
    (⟨candidate,accepted⟩ : Candidate prior inventory past reference original rebuilt) ∈
      candidates prior inventory past reference original rebuilt :=
  List.mem_filterMap.mpr ⟨candidate,member,by simp only [refine,dif_pos accepted]⟩

inductive Outcome where
  | selected (candidate : Candidate prior inventory past reference original rebuilt)
  | blocked
      (previous : Feed.Prefix.Outcome inventory prior.model prior.domain prior.original past reference
        prior.recoveryPricing prior.futureRequests)
      (failed : ∀ candidate ∈ originalPool prior inventory past reference original,
        Work.Reconstruction.Rejection rebuilt reference candidate.protocol)

def compile : Outcome prior inventory past reference original rebuilt :=
  match found : (candidates prior inventory past reference original rebuilt).head? with
  | some candidate => .selected candidate
  | none => .blocked
      (Work.Prefix.compile inventory prior.model prior.domain prior.original past reference
        prior.recoveryPricing prior.futureRequests original)
      (fun candidate member => Work.Reconstruction.rejectionFrom rebuilt reference candidate.protocol (by
        intro accepted
        have included := every_preserving_original_candidate_is_generated prior inventory past reference original rebuilt
          candidate member accepted
        rw [List.head?_eq_none_iff.mp found] at included
        exact List.not_mem_nil included))

variable {prior inventory past reference original rebuilt}
def candidate? (outcome : Outcome prior inventory past reference original rebuilt) :
    Option (Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Global.Candidate
      (tariff := prior.recoveryPricing) (requested := prior.futureRequests)
      prior.model prior.domain prior.original past reference) :=
  match outcome with
  | .selected candidate => some candidate.previous.previous
  | .blocked .. => none

def Reviewed (outcome : Outcome prior inventory past reference original rebuilt) : Prop :=
  match outcome with
  | .selected candidate =>
      Selection.Restoration.verify (tariff := prior.recoveryPricing) (requested := prior.futureRequests)
        prior.model prior.domain prior.original reference candidate.previous.protocol = true ∧
        Feed.Selection.acceptable inventory prior.model prior.domain prior.original prior.recoveryPricing
          prior.futureRequests reference candidate.previous.protocol ∧
        Work.Reconstruction.Accepts rebuilt reference candidate.previous.protocol
  | .blocked previous _ => Feed.Prefix.review previous = true ∧
      ∀ candidate ∈ originalPool prior inventory past reference original,
        ¬ Work.Reconstruction.Accepts rebuilt reference candidate.protocol

theorem reviewed (outcome : Outcome prior inventory past reference original rebuilt) : Reviewed outcome := by
  cases outcome with
  | selected candidate => exact ⟨candidate.previous.previous.verified,candidate.previous.accepted,candidate.accepted⟩
  | blocked previous failed =>
      refine ⟨Feed.Prefix.every_generated_outcome_has_its_raw_source_review previous,?_⟩
      intro candidate member accepted
      have rejected := failed candidate member
      exact rejected.broken (accepted rejected.axis rejected.generated)

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Recovery.Metering.Assessment.Relation.Feed.Work.Prefix.Reconstruction
