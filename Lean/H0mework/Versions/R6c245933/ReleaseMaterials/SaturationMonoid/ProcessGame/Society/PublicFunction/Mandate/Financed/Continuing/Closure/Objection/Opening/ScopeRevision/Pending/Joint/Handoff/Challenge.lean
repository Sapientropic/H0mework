import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Source
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Challenge.ScopeProcess

/-! Every saved Challenge consumes the next scope's own actual boundaries.
Complete old states, actors, origins and residual snapshots remain in the
original vocabulary; new-scope Challenges have separate admissions. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Challenge

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
variable {oldScope : Mandate.Scope (Party := Bool) (Good := Good) (Port := Mandate.Source.Port)}
  {bound : BoundSource base oldScope} {inputs : List (List Action)} (fresh : Handoff.Ready bound inputs)
noncomputable section

def occurrence : Mandate.Challenge.ScopeBoundary.Source base := ⟨fresh.scope,newBound fresh,epochInputs fresh⟩
theorem laterWindow : oldScope.task.deadline < (occurrence fresh).scope.task.earliest :=
  fresh.new_window_is_after_the_actual_expired_scope
def receipts (count : Nat) := Mandate.Challenge.ScopeBoundary.receipts (occurrence fresh) 0 count

abbrev family := Mandate.Challenge.fromHistory bound
abbrev prior (record : Mandate.Challenge.Cross.Resident bound inputs) :=
  Mandate.Challenge.Cross.process (family (bound := bound)) record.original

def shape (record : Mandate.Challenge.Cross.Resident bound inputs) :
    Mandate.Challenge.ScopeProcess.Shape (family (bound := bound)) record.originInputs record.original record.history.state.current := by
  cases record.history with
  | pending target state slots => exact .pending (Mandate.Challenge.Cross.tracked _ target) slots rfl rfl rfl
  | closed state archive slots => exact .closed archive slots

def continued (record : Mandate.Challenge.Cross.Resident bound inputs) (count : Nat) :=
  (Mandate.Challenge.ScopeProcess.begin (family (bound := bound)) record.originInputs (occurrence fresh) (laterWindow fresh)
    (original := record.original) record.history.state).consume _ _ _ _ (shape record) (receipts fresh count)

def images (record : Mandate.Challenge.Cross.Resident bound inputs) (actual : List (Mandate.Challenge.ScopeBoundary.Receipt (occurrence fresh))) :
    List (LifecycleEvent (Mandate.Challenge.V (family (bound := bound)) record.originInputs)) :=
  match record.history with
  | .pending target _ _ => actual.map (Mandate.Challenge.ScopeProcess.image _ _ (occurrence fresh) (laterWindow fresh)
      (Mandate.Challenge.Cross.tracked _ target) rfl rfl)
  | .closed .. => []

theorem every_original_slot_admission_actor_and_residual_is_literal
    (record : Mandate.Challenge.Cross.Resident bound inputs) (count : Nat) :
    (continued fresh record count).state.current.slots = record.history.state.current.slots :=
  (continued fresh record count).slots

theorem complete_history_is_original_then_actual_boundary_images
    (record : Mandate.Challenge.Cross.Resident bound inputs) (count : Nat) :
    (continued fresh record count).state.current.history = record.history.state.current.history ++ images fresh record (receipts fresh count) := by
  rcases record with ⟨originInputs,original,history,within⟩
  cases history with
  | pending target state slots => exact Mandate.Challenge.ScopeProcess.Thread.consume_history _ _ _ _ _ slots rfl rfl rfl _ _
  | closed state archive slots =>
    change ((Mandate.Challenge.ScopeProcess.begin _ originInputs (occurrence fresh) (laterWindow fresh) (original := original) state).consume
      _ _ _ _ (.closed archive slots) (receipts fresh count)).state.current.history = state.current.history ++ []
    rw [Mandate.Challenge.ScopeProcess.Thread.closed_is_literal]
    exact (List.append_nil _).symm

theorem complete_native_run_is_original_then_actual_boundary_images
    (record : Mandate.Challenge.Cross.Resident bound inputs) (count : Nat) :
    (continued fresh record count).state.generated.events = record.history.state.generated.events ++ images fresh record (receipts fresh count) := by
  rw [← NativeResponsibilityProcess.GeneratedState.history_eq,complete_history_is_original_then_actual_boundary_images,
    record.history.state.history_eq]

theorem terminal_state_is_literal (record : Mandate.Challenge.Cross.Resident bound inputs)
    (closed : record.history.isPending = false) (count : Nat) :
    (continued fresh record count).state.current = record.history.state.current := by
  rcases record with ⟨originInputs,original,history,within⟩
  cases history with
  | pending target state slots => cases closed
  | closed state archive slots =>
    change ((Mandate.Challenge.ScopeProcess.begin _ originInputs (occurrence fresh) (laterWindow fresh) (original := original) state).consume
      _ _ _ _ (.closed archive slots) (receipts fresh count)).state.current = state.current
    rw [Mandate.Challenge.ScopeProcess.Thread.closed_is_literal]
    rfl

def expectedTrace (record : Mandate.Challenge.Cross.Resident bound inputs) (count : Nat) :=
  if record.history.isPending then receipts fresh count else []

theorem complete_actual_trace_is_the_whole_new_receipt_sequence_for_pending
    (record : Mandate.Challenge.Cross.Resident bound inputs) (count : Nat) :
    Mandate.Challenge.ScopeProcess.actualTrace (family (bound := bound)) record.originInputs (occurrence fresh) (laterWindow fresh)
      (prior record) record.original (continued fresh record count).state.generated = expectedTrace fresh record count := by
  rcases record with ⟨originInputs,original,history,within⟩
  cases history with
  | pending target state slots =>
    change Mandate.Challenge.ScopeProcess.actualTrace _ originInputs (occurrence fresh) (laterWindow fresh) _ original
      ((Mandate.Challenge.ScopeProcess.begin _ originInputs (occurrence fresh) (laterWindow fresh) (original := original) state).consume
        _ _ _ _ (.pending (Mandate.Challenge.Cross.tracked _ target) slots rfl rfl rfl) (receipts fresh count)).state.generated = receipts fresh count
    exact Mandate.Challenge.ScopeProcess.begin_trace _ originInputs (occurrence fresh) (laterWindow fresh)
      state _ slots rfl rfl rfl (receipts fresh count)
  | closed state archive slots =>
    change Mandate.Challenge.ScopeProcess.actualTrace _ originInputs (occurrence fresh) (laterWindow fresh) _ original
      ((Mandate.Challenge.ScopeProcess.begin _ originInputs (occurrence fresh) (laterWindow fresh) (original := original) state).consume
        _ _ _ _ (.closed archive slots) (receipts fresh count)).state.generated = []
    rw [Mandate.Challenge.ScopeProcess.Thread.closed_is_literal]
    change Mandate.Challenge.ScopeProcess.actualTrace _ _ _ _ _ _ (Mandate.Challenge.ScopeProcess.inheritRun _ _ _ _ _ _ state.generated) = []
    exact Mandate.Challenge.ScopeProcess.inheritRun_trace _ _ _ _ _ _ _

structure Entry (count : Nat) where
  private mk ::
  original : Mandate.Challenge.Cross.Resident bound inputs
  continuation : Mandate.Challenge.ScopeProcess.Thread (family (bound := bound)) original.originInputs (occurrence fresh) (laterWindow fresh)
    (original := original.original) original.history.state
  exact : continuation = continued fresh original count

def entry (record : Mandate.Challenge.Cross.Resident bound inputs) (count : Nat) : Entry fresh count :=
  ⟨record,continued fresh record count,rfl⟩
def inventory (records : List (Mandate.Challenge.Cross.Resident bound inputs)) (count : Nat) := records.map (fun record => entry fresh record count)

theorem inventory_preserves_every_original_in_order_with_multiplicity
    (records : List (Mandate.Challenge.Cross.Resident bound inputs)) (count : Nat) :
    (inventory fresh records count).map Entry.original = records := by
  simp only [inventory,List.map_map]
  exact List.map_id _

theorem every_original_record_is_actually_continued (records : List (Mandate.Challenge.Cross.Resident bound inputs))
    (record : Mandate.Challenge.Cross.Resident bound inputs) (inside : record ∈ records) (count : Nat) :
    entry fresh record count ∈ inventory fresh records count := List.mem_map.mpr ⟨record,inside,rfl⟩

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Challenge
