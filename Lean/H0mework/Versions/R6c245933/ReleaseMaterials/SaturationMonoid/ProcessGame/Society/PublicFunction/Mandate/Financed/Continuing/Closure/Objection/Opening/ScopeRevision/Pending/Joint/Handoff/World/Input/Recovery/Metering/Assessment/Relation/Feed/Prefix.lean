import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Recovery.Metering.Assessment.Relation.Feed.Selection
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Global

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Recovery.Metering.Assessment.Relation.Feed.Prefix
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole
noncomputable section

variable {epoch : Epoch} (inventory : Inventory epoch)
  (model : Native.Authority.Bound (Party := Bool) (Good := Good) (Port := Mandate.Source.Port)
    (Technology := Unit) (Instrument := Unit))
  (domain : List (Continuation.Cursor model.source.code)) (original : Rule model.source.code)
  (past : List (Rule model.source.code)) (reference : Whole.Program model.source.code (horizon domain))
  (tariff : Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Restoration.Tariff
    (Party := Bool) (Good := Good) (Port := Mandate.Source.Port) (Technology := Unit) (Instrument := Unit))
  (requested : List (List Action))

structure Candidate where
  previous : Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Global.Candidate (tariff := tariff) (requested := requested)
    model domain original past reference
  accepted : Feed.Selection.acceptable inventory model domain original tariff requested reference previous.protocol

variable {inventory model domain original past reference tariff requested}
abbrev Candidate.protocol (candidate : Candidate inventory model domain original past reference tariff requested) :=
  candidate.previous.protocol
variable (inventory model domain original past reference tariff requested)

def refine (previous : Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Global.Candidate (tariff := tariff) (requested := requested)
    model domain original past reference) : Option (Candidate inventory model domain original past reference tariff requested) :=
  if accepted : Feed.Selection.acceptable inventory model domain original tariff requested reference previous.protocol then
    some ⟨previous,accepted⟩ else none

/-- The original paid-prefix pool is retained. Joint History admission is
performed before taking its first certified completion. -/
def candidates :=
  (Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Global.candidates (tariff := tariff) (requested := requested) model domain original past reference).filterMap
    (refine inventory model domain original past reference tariff requested)

theorem every_jointly_certified_completion_is_generated (tail : Complete.FiniteProgram model.source.code)
    (verified : Selection.Restoration.verify (tariff := tariff) (requested := requested) model domain original reference
      (Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Global.proposal model domain past tail) = true)
    (accepted : Feed.Selection.acceptable inventory model domain original tariff requested reference
      (Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Global.proposal model domain past tail)) :
    ∃ candidate ∈ candidates inventory model domain original past reference tariff requested,
      candidate.protocol = Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Global.proposal model domain past tail := by
  obtain ⟨previous,member,same⟩ := Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Global.every_certified_completion_is_generated
    model domain original past reference tail verified
  have keep : Feed.Selection.acceptable inventory model domain original tariff requested reference previous.protocol :=
    same.symm ▸ accepted
  refine ⟨⟨previous,keep⟩,List.mem_filterMap.mpr ⟨previous,member,?_⟩,same⟩
  simp only [refine,dif_pos keep]

inductive Failure (program : Whole.Program model.source.code (horizon domain)) where
  | original (failed : Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Global.Failure (tariff := tariff) (requested := requested)
      model domain original reference program)
  | history (failed : Feed.Selection.Rejection inventory model domain original tariff requested reference program)

inductive Outcome where
  | selected (candidate : Candidate inventory model domain original past reference tariff requested)
  | blocked (failed : ∀ tail : Complete.FiniteProgram model.source.code,
      Failure inventory model domain original reference tariff requested (Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Global.proposal model domain past tail))

def compile : Outcome inventory model domain original past reference tariff requested :=
  match found : (candidates inventory model domain original past reference tariff requested).head? with
  | some candidate => .selected candidate
  | none => .blocked fun tail =>
      if verified : Selection.Restoration.verify (tariff := tariff) (requested := requested) model domain original reference
          (Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Global.proposal model domain past tail) = true then
        .history (Feed.Selection.rejectionFrom inventory model domain original tariff requested reference
          (Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Global.proposal model domain past tail) (by
            intro accepted
            obtain ⟨candidate,member,_⟩ := every_jointly_certified_completion_is_generated
              inventory model domain original past reference tariff requested tail verified accepted
            rw [List.head?_eq_none_iff.mp found] at member
            exact List.not_mem_nil member))
      else .original (Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Global.failure (tariff := tariff) (requested := requested)
        (Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Global.proposal model domain past tail) verified)

namespace Candidate
variable {inventory model domain original past reference tariff requested}
  (candidate : Candidate inventory model domain original past reference tariff requested)

theorem committed_prefix (within : past.length ≤ horizon domain) :
    candidate.protocol.controls.take past.length = past := candidate.previous.committed_prefix within

theorem every_original_row_is_jointly_admitted (row : Feed.Selection.Row model domain) :
    Feed.Selection.holds inventory model domain original tariff requested reference candidate.protocol row :=
  candidate.accepted row (Selection.Restoration.every_row_is_generated _ _ _)

theorem original_full_policy_is_still_verified :
    Selection.Restoration.verify (tariff := tariff) (requested := requested) model domain original reference candidate.protocol = true :=
  candidate.previous.verified
end Candidate

variable {inventory model domain original past reference tariff requested}
def reviewFailure (program : Whole.Program model.source.code (horizon domain)) :
    Failure inventory model domain original reference tariff requested program → Bool
  | .original failed => Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Global.reviewFailure (tariff := tariff) (requested := requested) program failed
  | .history failed => !decide (Feed.Selection.holds inventory model domain original tariff requested reference program failed.row)

theorem every_failure_is_independently_replayable (program : Whole.Program model.source.code (horizon domain))
    (failed : Failure inventory model domain original reference tariff requested program) : reviewFailure program failed = true := by
  cases failed with
  | original failed => exact Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Global.every_failure_is_independently_replayable program failed
  | history failed =>
      simp only [reviewFailure,Bool.not_eq_true',decide_eq_false_iff_not]
      exact failed.broken

def verify (program : Whole.Program model.source.code (horizon domain)) : Bool :=
  Selection.Restoration.verify (tariff := tariff) (requested := requested) model domain original reference program &&
    decide (Feed.Selection.acceptable inventory model domain original tariff requested reference program)

def review (outcome : Outcome inventory model domain original past reference tariff requested) : Bool :=
  match outcome with
  | .selected candidate => verify (inventory := inventory) (original := original) (reference := reference)
      (tariff := tariff) (requested := requested) candidate.protocol
  | .blocked failed =>
      (Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Global.tailPool model domain past).all fun tail =>
        reviewFailure (Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Global.proposal model domain past ⟨_,tail⟩)
          (failed ⟨_,tail⟩)

theorem every_generated_outcome_has_its_raw_source_review
    (outcome : Outcome inventory model domain original past reference tariff requested) : review outcome = true := by
  cases outcome with
  | selected candidate =>
      simp only [review,verify,Bool.and_eq_true,decide_eq_true_eq]
      exact ⟨candidate.previous.verified,candidate.accepted⟩
  | blocked failed =>
      dsimp only [review]
      apply List.all_eq_true.mpr
      intro tail _
      exact every_failure_is_independently_replayable _ (failed ⟨_,tail⟩)
end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Recovery.Metering.Assessment.Relation.Feed.Prefix
