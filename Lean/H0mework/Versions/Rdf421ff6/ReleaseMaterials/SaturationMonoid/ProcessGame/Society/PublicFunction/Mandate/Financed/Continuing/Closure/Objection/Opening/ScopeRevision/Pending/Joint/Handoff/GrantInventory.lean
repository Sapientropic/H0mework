import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Grant

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Grant

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
open Mandate.Lifecycle
variable {oldScope : Mandate.Scope (Party := Bool) (Good := Good) (Port := Mandate.Source.Port)}
  {bound : BoundSource base oldScope} {inputs : List (List Action)} (fresh : Handoff.Ready bound inputs)
noncomputable section

abbrev prior (record : Mandate.Challenge.Cross.GrantResident bound inputs) :=
  Observed.process (base := base) (scope := oldScope)
    (currentAt := Mandate.Challenge.Cross.grantCurrent bound inputs) (wordAt := Mandate.Challenge.Cross.grantWord bound inputs)
    (birth := record.birth.val) (grant := record.grant)

def continued (record : Mandate.Challenge.Cross.GrantResident bound inputs) (count : Nat) :=
  (Thread.begin (fresh := fresh) (prior := prior record) record.history.state record.history.obligation record.history.slots).consume
    (receipts fresh 0 count)

def fullRun (record : Mandate.Challenge.Cross.GrantResident bound inputs) (count : Nat) :
    (process fresh (prior record)).Run
      (Observed.initialState base oldScope (Mandate.Challenge.Cross.grantCurrent bound inputs)
        (Mandate.Challenge.Cross.grantWord bound inputs) record.birth.val record.grant)
      (continued fresh record count).state :=
  (inheritRun fresh (prior record) record.history.generated).concatRuns _ (continued fresh record count).crossing

theorem complete_original_state_is_the_actual_start (record : Mandate.Challenge.Cross.GrantResident bound inputs) :
    (continued fresh record 0).state = record.history.state := rfl

theorem every_original_slot_and_admission_is_literal (record : Mandate.Challenge.Cross.GrantResident bound inputs) (count : Nat) :
    (continued fresh record count).state.slots = record.history.state.slots :=
  (continued fresh record count).slots.trans record.history.slots.symm

theorem complete_history_is_original_then_actual_new_receipts
    (record : Mandate.Challenge.Cross.GrantResident bound inputs) (count : Nat) :
    (continued fresh record count).state.history = record.history.state.history ++
      (receipts fresh 0 count).map (Receipt.image fresh record.history.obligation) := Thread.consume_history _ _

theorem complete_native_run_is_preserved_before_each_actual_new_event
    (record : Mandate.Challenge.Cross.GrantResident bound inputs) (count : Nat) :
    (fullRun fresh record count).events = record.history.generated.events ++
      (receipts fresh 0 count).map (Receipt.image fresh record.history.obligation) := by
  rw [fullRun,NativeResponsibilityProcess.Run.events_concatRuns,inheritRun_events]
  exact congrArg (List.append record.history.generated.events) (actual_run_events _ _ _ _)

structure Entry (count : Nat) where
  private mk ::
  original : Mandate.Challenge.Cross.GrantResident bound inputs
  continuation : Thread fresh (prior original) original.history.state original.history.obligation
  exact : continuation = continued fresh original count
  entire : (process fresh (prior original)).Run
    (Observed.initialState base oldScope (Mandate.Challenge.Cross.grantCurrent bound inputs)
      (Mandate.Challenge.Cross.grantWord bound inputs) original.birth.val original.grant) continuation.state

def entry (record : Mandate.Challenge.Cross.GrantResident bound inputs) (count : Nat) : Entry fresh count :=
  ⟨record,continued fresh record count,rfl,fullRun fresh record count⟩

def inventory (records : List (Mandate.Challenge.Cross.GrantResident bound inputs)) (count : Nat) :=
  records.map (fun record => entry fresh record count)

theorem every_old_record_is_actually_continued (records : List (Mandate.Challenge.Cross.GrantResident bound inputs))
    (record : Mandate.Challenge.Cross.GrantResident bound inputs) (inside : record ∈ records) (count : Nat) :
    entry fresh record count ∈ inventory fresh records count := List.mem_map.mpr ⟨record,inside,rfl⟩

theorem complete_inventory_keeps_order_and_multiplicity (records : List (Mandate.Challenge.Cross.GrantResident bound inputs)) (count : Nat) :
    (inventory fresh records count).map Entry.original = records := by
  simp only [inventory,List.map_map]
  exact List.map_id _

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Grant
