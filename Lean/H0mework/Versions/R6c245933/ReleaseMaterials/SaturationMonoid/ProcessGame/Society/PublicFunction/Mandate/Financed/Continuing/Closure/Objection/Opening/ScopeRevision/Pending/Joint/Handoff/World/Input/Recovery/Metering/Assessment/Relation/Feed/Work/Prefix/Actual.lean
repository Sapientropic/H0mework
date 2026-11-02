import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Recovery.Metering.Assessment.Relation.Feed.Work.Prefix.Reconstruction
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Commitment.Requests

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Recovery.Metering.Assessment.Relation.Feed.Work.Prefix.Actual
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

abbrev Previous := Reconstruction.Candidate prior inventory past reference original rebuilt
def originalPool := Reconstruction.candidates prior inventory past reference original rebuilt

def Preserves (program : Whole.Program prior.model.source.code (horizon prior.domain)) : Prop :=
  TaskSource.Commitment.NoWorse prior inventory past reference program ∧
    TaskSource.Commitment.Requests.Accepts prior inventory past original reference program
      (TaskSource.Commitment.Requests.execute prior inventory past program)

instance (program : Whole.Program prior.model.source.code (horizon prior.domain)) :
    Decidable (Preserves prior inventory past reference original program) := by
  unfold Preserves
  infer_instance

inductive Rejection (program : Whole.Program prior.model.source.code (horizon prior.domain)) where
  | actual (fault : TaskSource.Commitment.Rejection prior inventory past reference program)
  | request (fault : TaskSource.Commitment.Requests.Rejection prior inventory past original reference program
      (TaskSource.Commitment.Requests.execute prior inventory past program))

def rejectionFrom (program : Whole.Program prior.model.source.code (horizon prior.domain))
    (failed : ¬ Preserves prior inventory past reference original program) :
    Rejection prior inventory past reference original program :=
  if kept : TaskSource.Commitment.NoWorse prior inventory past reference program then
    .request (TaskSource.Commitment.Requests.rejectionFrom prior inventory past original reference program
      (TaskSource.Commitment.Requests.execute prior inventory past program) (fun preserved => failed ⟨kept,preserved⟩))
  else .actual (TaskSource.Commitment.rejectionFrom prior inventory past reference program kept)

theorem Rejection.broken {program : Whole.Program prior.model.source.code (horizon prior.domain)}
    (fault : Rejection prior inventory past reference original program) :
    ¬ Preserves prior inventory past reference original program := by
  intro kept
  cases fault with
  | actual fault => exact fault.broken (kept.1 fault.test fault.generated)
  | request fault => exact fault.broken (kept.2 fault.query fault.generated)

structure Candidate where
  previous : Previous prior inventory past reference original rebuilt
  bound : prior.worldCurrent.isSome = true
  accepted : Preserves prior inventory past reference original previous.previous.protocol

def refine (bound : prior.worldCurrent.isSome = true)
    (previous : Previous prior inventory past reference original rebuilt) :
    Option (Candidate prior inventory past reference original rebuilt) :=
  if kept : Preserves prior inventory past reference original previous.previous.protocol then
    some ⟨previous,bound,kept⟩ else none

def candidates (bound : prior.worldCurrent.isSome = true) :=
  (originalPool prior inventory past reference original rebuilt).filterMap
    (refine prior inventory past reference original rebuilt bound)

theorem every_preserving_original_candidate_is_generated (bound : prior.worldCurrent.isSome = true)
    (previous : Previous prior inventory past reference original rebuilt)
    (member : previous ∈ originalPool prior inventory past reference original rebuilt)
    (accepted : Preserves prior inventory past reference original previous.previous.protocol) :
    (⟨previous,bound,accepted⟩ : Candidate prior inventory past reference original rebuilt) ∈
      candidates prior inventory past reference original rebuilt bound :=
  List.mem_filterMap.mpr ⟨previous,member,by simp only [refine,dif_pos accepted]⟩

inductive Outcome where
  | unbound (missing : prior.worldCurrent = none)
  | selected (candidate : Candidate prior inventory past reference original rebuilt)
  | blocked (previous : Reconstruction.Outcome prior inventory past reference original rebuilt)
      (failed : ∀ candidate ∈ originalPool prior inventory past reference original rebuilt,
        Rejection prior inventory past reference original candidate.previous.protocol)

def compile : Outcome prior inventory past reference original rebuilt :=
  match bound : prior.worldCurrent with
  | none => .unbound bound
  | some _ =>
      let present : prior.worldCurrent.isSome = true := by rw [bound];rfl
      match found : (candidates prior inventory past reference original rebuilt present).head? with
      | some candidate => .selected candidate
      | none => .blocked (Reconstruction.compile prior inventory past reference original rebuilt)
          (fun candidate member => rejectionFrom prior inventory past reference original
            candidate.previous.protocol (by
              intro accepted
              have included := every_preserving_original_candidate_is_generated prior inventory past reference
                original rebuilt present candidate member accepted
              rw [List.head?_eq_none_iff.mp found] at included
              exact List.not_mem_nil included))

variable {prior inventory past reference original rebuilt}
def candidate? : Outcome prior inventory past reference original rebuilt →
    Option (Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Global.Candidate
      (tariff := prior.recoveryPricing) (requested := prior.futureRequests)
      prior.model prior.domain prior.original past reference)
  | .selected candidate => some candidate.previous.previous.previous
  | .unbound _ | .blocked .. => none

def Reviewed (outcome : Outcome prior inventory past reference original rebuilt) : Prop :=
  match outcome with
  | .unbound _ => prior.worldCurrent = none
  | .selected candidate =>
      Reconstruction.Reviewed (.selected candidate.previous) ∧
      prior.worldCurrent.isSome = true ∧
      Preserves prior inventory past reference original candidate.previous.previous.protocol
  | .blocked previous _ => Reconstruction.Reviewed previous ∧
      ∀ candidate ∈ originalPool prior inventory past reference original rebuilt,
        ¬ Preserves prior inventory past reference original candidate.previous.protocol

theorem reviewed (outcome : Outcome prior inventory past reference original rebuilt) : Reviewed outcome := by
  cases outcome with
  | unbound missing => exact missing
  | selected candidate => exact ⟨Reconstruction.reviewed _,candidate.bound,candidate.accepted⟩
  | blocked previous failed =>
      refine ⟨Reconstruction.reviewed previous,?_⟩
      intro candidate member accepted
      have rejected := failed candidate member
      exact Rejection.broken prior inventory past reference original rejected accepted


theorem selected_has_its_actual_protection
    (outcome : Outcome prior inventory past reference original rebuilt)
    (candidate : Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Global.Candidate
      (tariff := prior.recoveryPricing) (requested := prior.futureRequests)
      prior.model prior.domain prior.original past reference)
    (chosen : candidate? outcome = some candidate) :
    prior.worldCurrent.isSome = true ∧
      TaskSource.Commitment.NoWorse prior inventory past reference candidate.protocol := by
  cases outcome with
  | unbound missing => cases chosen
  | blocked previous failed => cases chosen
  | selected selected =>
      cases Option.some.inj chosen
      exact ⟨selected.bound,selected.accepted.1⟩


theorem selected_keeps_the_original_queries
    (outcome : Outcome prior inventory past reference original rebuilt)
    (candidate : Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Global.Candidate
      (tariff := prior.recoveryPricing) (requested := prior.futureRequests)
      prior.model prior.domain prior.original past reference)
    (chosen : candidate? outcome = some candidate) :
    TaskSource.Commitment.Requests.Accepts prior inventory past original reference candidate.protocol
      (TaskSource.Commitment.Requests.execute prior inventory past candidate.protocol) := by
  cases outcome with
  | unbound missing => cases chosen
  | blocked previous failed => cases chosen
  | selected selected =>
      cases Option.some.inj chosen
      exact selected.accepted.2

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Recovery.Metering.Assessment.Relation.Feed.Work.Prefix.Actual
