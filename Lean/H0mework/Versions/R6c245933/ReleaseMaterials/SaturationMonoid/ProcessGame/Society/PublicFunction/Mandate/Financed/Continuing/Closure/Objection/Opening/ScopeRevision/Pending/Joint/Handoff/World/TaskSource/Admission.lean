import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Task
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned.Source
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole
open Computation.Search.Segmented.Publication.Learning.Paid
noncomputable section
variable {epoch : Epoch} (inventory : Inventory epoch) (pending : List Action)

/-- Preserve the original source admission, including its exact rejected row.
No successful cache or feasibility witness is an input. -/
structure Admission where
  private mk ::
  result : Owned.Source.Seed (task inventory pending)
  generated : result = Owned.Source.seed (task inventory pending)

def admit : Admission inventory pending := ⟨Owned.Source.seed (task inventory pending),rfl⟩

namespace Admission
variable {inventory pending}
def passed (made : Admission inventory pending) : Bool :=
  match made.result with | .accepted .. => true | .rejected .. => false

abbrev Verified : Prop :=
  Selection.acceptable (task inventory pending).model (task inventory pending).domain
    (task inventory pending).original (task inventory pending).baseline (task inventory pending).baseline

abbrev Rejection := Selection.Rejection (task inventory pending).model (task inventory pending).domain
  (task inventory pending).original (task inventory pending).baseline (task inventory pending).baseline

theorem passed_iff (made : Admission inventory pending) : made.passed = true ↔
    Verified (inventory := inventory) (pending := pending) := by
  rcases made with ⟨result,generated⟩
  cases result with
  | rejected reason =>
      constructor
      · intro impossible;cases impossible
      · intro valid
        exact False.elim (reason.broken (valid reason.row reason.generated))
  | accepted cache _ programme _ =>
      have valid : Verified (inventory := inventory) (pending := pending) := by
        simpa only [programme] using cache.above
      exact ⟨fun _ => valid,fun _ => rfl⟩

def failure (made : Admission inventory pending) (refused : made.passed ≠ true) :
    Rejection (inventory := inventory) (pending := pending) :=
  match same : made.result with
  | .rejected reason => reason
  | .accepted .. => False.elim (refused (by simp only [passed,same]))

variable {otherEpoch : Epoch} {other : Inventory otherEpoch} {otherPending : List Action}
def NoWorse (made : Admission inventory pending) (old : Admission other otherPending) : Prop :=
  old.passed = true → made.passed = true
instance (made : Admission inventory pending) (old : Admission other otherPending) :
    Decidable (NoWorse made old) := by unfold NoWorse;infer_instance

theorem preserves_original_task_admission (made : Admission inventory pending)
    (old : Admission other otherPending) (kept : NoWorse made old)
    (valid : Verified (inventory := other) (pending := otherPending)) :
    Verified (inventory := inventory) (pending := pending) :=
  made.passed_iff.mp (kept (old.passed_iff.mpr valid))
end Admission
end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource
