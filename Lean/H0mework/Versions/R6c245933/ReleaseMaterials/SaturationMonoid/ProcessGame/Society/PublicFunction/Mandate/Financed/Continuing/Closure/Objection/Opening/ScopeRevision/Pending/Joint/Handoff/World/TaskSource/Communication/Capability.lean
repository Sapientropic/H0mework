import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Communication.Task.Core

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Communication.Capability
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole
open Computation.Search.Segmented.Publication.Learning.Paid
noncomputable section

variable (prior : Owned.Task (Party := Bool) (Good := Good) (Port := Mandate.Source.Port)
  (Technology := Unit) (Instrument := Unit))

abbrev OriginalProgram := Whole.Program prior.model.source.code (horizon prior.domain)
def catalogue := Whole.programs prior.model.source.code (horizon prior.domain)

theorem every_original_program_is_included (program : OriginalProgram prior) :
    program ∈ catalogue prior := Whole.every_bounded_program_is_source_generated _ _ program

variable {epoch : Epoch} (inventory : Inventory epoch) (pending : List Action)
  (old : Continuation.Cursor prior.model.source.code)

/-- The entire original control word is interpreted in the actual new Task.
The retained horizon pays its bound; no suffix is discarded. -/
def programme (original : OriginalProgram prior) :
    Whole.Program (task inventory pending prior old).model.source.code
      (horizon (task inventory pending prior old).domain) :=
  ⟨original.controls.map (rule inventory prior old),by
    change (original.controls.map (rule inventory prior old)).length ≤ horizon (domain inventory prior old)
    rw [List.length_map]
    exact original.bounded.trans (complete_original_horizon_is_retained inventory prior old)⟩

def Admissible (original : OriginalProgram prior) : Prop :=
  Selection.acceptable (task inventory pending prior old).model (task inventory pending prior old).domain
    (task inventory pending prior old).original (task inventory pending prior old).baseline
    (programme prior inventory pending old original)

instance (original : OriginalProgram prior) : Decidable (Admissible prior inventory pending old original) := by
  unfold Admissible;infer_instance

/-- The original source verdict and every original programme are computed from
this same generated Task, with their original finite positions retained. -/
structure Snapshot where
  private mk ::
  admission : Owned.Source.Seed (task inventory pending prior old)
  admission_generated : admission = Owned.Source.seed (task inventory pending prior old)
  capabilities : List Bool
  generated : capabilities = (catalogue prior).map fun program =>
    decide (Admissible prior inventory pending old program)

def generate : Snapshot prior inventory pending old :=
  ⟨Owned.Source.seed (task inventory pending prior old),rfl,
    (catalogue prior).map (fun program => decide (Admissible prior inventory pending old program)),rfl⟩

namespace Snapshot
variable {prior inventory pending old}
def passed (made : Snapshot prior inventory pending old) : Bool :=
  match made.admission with | .accepted .. => true | .rejected .. => false

def read (made : Snapshot prior inventory pending old) (index : Nat) : Bool :=
  made.capabilities[index]?.getD false

theorem every_position_is_its_original_full_relation (made : Snapshot prior inventory pending old)
    (index : Nat) (inside : index < (catalogue prior).length) :
    made.read index = decide (Admissible prior inventory pending old (catalogue prior)[index]) := by
  simp only [read,made.generated,List.getElem?_map,List.getElem?_eq_getElem inside,
    Option.map_some,Option.getD_some]

theorem every_original_position_is_retained (made : Snapshot prior inventory pending old) :
    made.capabilities.length = (catalogue prior).length := by rw [made.generated,List.length_map]
end Snapshot

variable {prior inventory pending old}
variable {otherEpoch : Epoch} {other : Inventory otherEpoch} {otherPending : List Action}
  {otherOld : Continuation.Cursor prior.model.source.code}

def NoWorse (made : Snapshot prior inventory pending old) (previous : Snapshot prior other otherPending otherOld) : Prop :=
  (previous.passed = true → made.passed = true) ∧
  ∀ index ∈ List.range (catalogue prior).length,previous.read index = true → made.read index = true

instance (made : Snapshot prior inventory pending old) (previous : Snapshot prior other otherPending otherOld) :
    Decidable (NoWorse made previous) := by unfold NoWorse;infer_instance

theorem noWorse_refl (made : Snapshot prior inventory pending old) : NoWorse made made :=
  ⟨fun yes => yes,fun _ _ yes => yes⟩

theorem every_old_admissible_program_is_still_admissible
    (made : Snapshot prior inventory pending old) (previous : Snapshot prior other otherPending otherOld)
    (kept : NoWorse made previous) (program : OriginalProgram prior)
    (valid : Admissible prior other otherPending otherOld program) :
    Admissible prior inventory pending old program := by
  obtain ⟨index,inside,same⟩ := List.mem_iff_getElem.mp (every_original_program_is_included prior program)
  have earlier : previous.read index = true := by
    rw [previous.every_position_is_its_original_full_relation index inside,same]
    exact decide_eq_true valid
  have retained := kept.2 index (List.mem_range.mpr inside) earlier
  rw [made.every_position_is_its_original_full_relation index inside,same] at retained
  exact of_decide_eq_true retained

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Communication.Capability
