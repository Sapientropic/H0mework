import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.SelfDeviation.Comparison.Preference
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Funding

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.SelfDeviation.Comparison.Appraisal
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
open Future.Expiry.Progress
noncomputable section

/-- Financial slots and events already enter the complete quoted-net account. -/
def nonfinancial {packet : Packet} : Responsibility.Row packet → Bool
  | .finance => false
  | _ => true

def rows {first : Packet} (observed : Observation first) :=
  (Responsibility.census observed.packet).filter nonfinancial

structure Slot {first : Packet} (observed : Observation first) where
  row : Responsibility.Row observed.packet
  index : Fin row.state.slots.length

structure HistoryItem {first : Packet} (observed : Observation first) where
  row : Responsibility.Row observed.packet
  index : Fin row.state.history.length

namespace Slot
variable {first : Packet} {observed : Observation first}
def origin (item : Slot observed) := item.row.origin
def value (item : Slot observed) : ObligationSlot item.origin.V := item.row.state.slots.get item.index
end Slot
namespace HistoryItem
variable {first : Packet} {observed : Observation first}
def origin (item : HistoryItem observed) := item.row.origin
def value (item : HistoryItem observed) : LifecycleEvent item.origin.V := item.row.state.history.get item.index
end HistoryItem

def slots {first : Packet} (observed : Observation first) : List (Slot observed) :=
  (rows observed).flatMap fun row => (List.finRange row.state.slots.length).map fun index => ⟨row,index⟩
def events {first : Packet} (observed : Observation first) : List (HistoryItem observed) :=
  (rows observed).flatMap fun row => (List.finRange row.state.history.length).map fun index => ⟨row,index⟩

theorem every_nonfinancial_slot_is_generated {first : Packet} (observed : Observation first)
    (row : Responsibility.Row observed.packet) (kept : nonfinancial row = true) (index : Fin row.state.slots.length) :
    (⟨row,index⟩ : Slot observed) ∈ slots observed := by
  refine List.mem_flatMap.mpr ⟨row,List.mem_filter.mpr ⟨Responsibility.every_original_row_is_in_the_census row,kept⟩,?_⟩
  exact List.mem_map.mpr ⟨index,List.mem_finRange _,rfl⟩

theorem every_nonfinancial_event_is_generated {first : Packet} (observed : Observation first)
    (row : Responsibility.Row observed.packet) (kept : nonfinancial row = true) (index : Fin row.state.history.length) :
    (⟨row,index⟩ : HistoryItem observed) ∈ events observed := by
  refine List.mem_flatMap.mpr ⟨row,List.mem_filter.mpr ⟨Responsibility.every_original_row_is_in_the_census row,kept⟩,?_⟩
  exact List.mem_map.mpr ⟨index,List.mem_finRange _,rfl⟩

theorem generated_slots_exclude_the_financial_account {first : Packet} (observed : Observation first)
    (item : Slot observed) (listed : item ∈ slots observed) : nonfinancial item.row = true := by
  obtain ⟨row,kept,inside⟩ := List.mem_flatMap.mp listed
  obtain ⟨index,_,same⟩ := List.mem_map.mp inside
  cases same
  exact (List.mem_filter.mp kept).2

theorem generated_events_exclude_the_financial_account {first : Packet} (observed : Observation first)
    (item : HistoryItem observed) (listed : item ∈ events observed) : nonfinancial item.row = true := by
  obtain ⟨row,kept,inside⟩ := List.mem_flatMap.mp listed
  obtain ⟨index,_,same⟩ := List.mem_map.mp inside
  cases same
  exact (List.mem_filter.mp kept).2

theorem every_generated_slot_retains_its_original_native_run {first : Packet} (observed : Observation first)
    (item : Slot observed) (_listed : item ∈ slots observed) :
    Nonempty (item.row.native.Run item.row.initial item.row.state) := ⟨item.row.complete⟩

def alternatives {epoch : Epoch} (inventory : Inventory epoch) (intent : Input.Intent) (actor : Bool) : List Input.Method :=
  (SelfDeviation.permits inventory intent actor).map fun permit => permit.choice.val.method

structure Agency where
  scope : World.Scope
  technology : State Bool Unit
  kind : World.ContinuationKind
  clock : ℚ
  standing : Bool → Bool
  eligible : Input.Intent → Bool
  available : Input.Intent → Bool → List Input.Method
  exitMaterial : Bool

def agency {first : Packet} (observed : Observation first) : Agency where
  scope := observed.packet.1.scope
  technology := (current observed.packet.1 observed.packet.2.inputs).technology
  kind := observed.kind
  clock := observed.clock
  standing := fun actor => decide (actor ∈ Delegation.members observed.packet.1.scope.task)
  eligible := fun intent => decide (Input.Eligible observed.packet.1 intent (current observed.packet.1 observed.packet.2.inputs))
  available := alternatives observed.packet.2
  exitMaterial := decide (Input.ExitCapacity.Envelope (current observed.packet.1 observed.packet.2.inputs))

theorem every_listed_current_method_has_an_actual_local_permit {first : Packet} (observed : Observation first)
    (intent : Input.Intent) (actor : Bool) (method : Input.Method)
    (listed : method ∈ (agency observed).available intent actor) :
    ∃ permit ∈ SelfDeviation.permits observed.packet.2 intent actor,
      permit.choice.val.method = method ∧ Input.Legal observed.packet.1 intent
        (current observed.packet.1 observed.packet.2.inputs) permit.choice.val ∧
        SelfDeviation.LocalWord actor (SelfDeviation.word observed.packet.2 intent permit.choice) := by
  obtain ⟨permit,inside,same⟩ := List.mem_map.mp listed
  exact ⟨permit,inside,same,permit.legal,permit.controlled⟩

def serviceWindow {first : Packet} (observed : Observation first) :=
  (observed.packet.1.scope.task.earliest,observed.packet.1.scope.task.deadline)

def sameServiceWindow {first : Packet} (old new : Observation first) : Bool :=
  decide (Compatible .paidWindow old new ∧ serviceWindow old = serviceWindow new)

theorem same_service_window_is_checked_from_both_actual_sources {first : Packet} (old new : Observation first) :
    sameServiceWindow old new = true ↔ Compatible .paidWindow old new ∧ serviceWindow old = serviceWindow new := by
  simp only [sameServiceWindow,decide_eq_true_eq]

/-- Each original good is counted once. This list does not supply an exchange. -/
def goods : List Good := [.feedstock,.service]
theorem every_good_is_generated (good : Good) : good ∈ goods := by cases good <;> simp [goods]

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.SelfDeviation.Comparison.Appraisal
