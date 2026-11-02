import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Registered.Loss.Runtime
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Registered.Responsibility
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Responsibility.Transport

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Registered.Loss.Responsibility
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
noncomputable section
abbrev Origin := Registered.Responsibility.Origin
abbrev Snapshot := Registered.Responsibility.Snapshot

variable {fuel : ℚ} {old : Followup.Joint.Inventory fuel} (authority : ScopeRevision.Ready old)
  {originInputs : List (List Action)} (inventory : Pending.Joint.Inventory authority originInputs)
  (fresh : Handoff.Ready (Pending.B authority) (Future.advance authority inventory .revision).inputs)
  (original : List Action) (saved : Continuation.Inventory authority inventory fresh original)

private def admitted {V : Vocabulary} (initial : ResponsibilityState V) : List (AdmittedObligation V) :=
  initial.slots.map fun slot => match slot with
    | .live obligation => obligation
    | .terminal archive => archive.obligation

def grantSnapshot (entry : Sigma fun record : Mandate.Challenge.Cross.GrantResident (Pending.B authority) (legacy authority inventory).inputs => Handoff.Continuation.Grant.Saved fresh record) : Snapshot :=
  let record := entry.1
  let initial := Handoff.Continuation.Grant.origin record
  let occurrence : World.Input.Event.Future.Expiry.Progress.Responsibility.GrantOccurrence :=
    ⟨authority.scope,Pending.B authority,(legacy authority inventory).inputs.take record.birth.val,record.birth.val,
      Mandate.Challenge.Cross.grantWord (Pending.B authority) (legacy authority inventory).inputs record.birth.val,
      record.grant.proposal.item.val,record.grant.acceptance.item.val,record.grant.candidate⟩
  let saved := entry.2
  ⟨⟨Handoff.Continuation.Grant.V,initial,admitted initial,some occurrence⟩,saved.native,saved.state,saved.entire⟩

def challengeSnapshot (entry : Sigma fun record : Mandate.Challenge.Cross.Resident (Pending.B authority) (legacy authority inventory).inputs => Handoff.Continuation.Challenge.Saved fresh record) : Snapshot :=
  let record := entry.1
  let saved := entry.2
  ⟨⟨Mandate.Challenge.V (Mandate.Challenge.fromHistory (Pending.B authority)) record.originInputs,.empty _,
    [Mandate.Challenge.obligation (Mandate.Challenge.fromHistory (Pending.B authority)) record.originInputs record.original],none⟩,
    saved.native,saved.state.current,saved.state.generated⟩

def serviceSnapshot (index : (Pending.B authority).source.Slot) : Snapshot :=
  let saved := saved.oldServices index
  ⟨⟨OutstandingSource.History.NativeService.V (Pending.B authority).source originInputs,.empty _,
    [OutstandingSource.History.NativeService.obligation (Pending.B authority).source originInputs index],none⟩,
    OutstandingSource.History.NativeService.Expired.process (Pending.B authority).source originInputs,
    saved.state.current,saved.state.generated⟩

def bornGrantSnapshot (record : Mandate.Challenge.Cross.GrantResident (newBound fresh) saved.inputs) : Snapshot :=
  let initial := Mandate.Lifecycle.Observed.initialState base fresh.scope
    (Mandate.Challenge.Cross.grantCurrent (newBound fresh) saved.inputs)
    (Mandate.Challenge.Cross.grantWord (newBound fresh) saved.inputs) record.birth.val record.grant
  let occurrence : World.Input.Event.Future.Expiry.Progress.Responsibility.GrantOccurrence :=
    ⟨fresh.scope,newBound fresh,saved.inputs.take record.birth.val,record.birth.val,
      Mandate.Challenge.Cross.grantWord (newBound fresh) saved.inputs record.birth.val,
      record.grant.proposal.item.val,record.grant.acceptance.item.val,record.grant.candidate⟩
  ⟨⟨Handoff.Continuation.Grant.V,initial,admitted initial,some occurrence⟩,
    Mandate.Lifecycle.Observed.process (base := base) (scope := fresh.scope)
      (currentAt := Mandate.Challenge.Cross.grantCurrent (newBound fresh) saved.inputs)
      (wordAt := Mandate.Challenge.Cross.grantWord (newBound fresh) saved.inputs)
      (birth := record.birth.val) (grant := record.grant),record.history.state,record.history.generated⟩

def bornChallengeSnapshot (record : Mandate.Challenge.Cross.Resident (newBound fresh) saved.inputs) : Snapshot :=
  ⟨⟨Mandate.Challenge.V (Mandate.Challenge.fromHistory (newBound fresh)) record.originInputs,.empty _,
    [Mandate.Challenge.obligation (Mandate.Challenge.fromHistory (newBound fresh)) record.originInputs record.original],none⟩,
    Mandate.Challenge.Cross.process (Mandate.Challenge.fromHistory (newBound fresh)) record.original,
    record.history.state.current,record.history.state.generated⟩

def bornServiceSnapshot (index : (source fresh).Slot) : Snapshot :=
  let saved := saved.services index
  ⟨⟨OutstandingSource.History.NativeService.V (source fresh) (Registered.inputs authority inventory fresh original),.empty _,
    [OutstandingSource.History.NativeService.obligation (source fresh) (Registered.inputs authority inventory fresh original) index],none⟩,
    OutstandingSource.History.NativeService.threadProcess (source fresh) (Registered.inputs authority inventory fresh original),
    saved.state.current,saved.state.generated⟩

def census : List Snapshot :=
  saved.oldGrants.map (grantSnapshot authority inventory fresh) ++
  saved.oldChallenges.map (challengeSnapshot authority inventory fresh) ++
  (List.finRange (Pending.B authority).source.seed.task.slots.length).map (serviceSnapshot authority inventory fresh original saved) ++
  saved.grants.map (bornGrantSnapshot authority inventory fresh original saved) ++
  saved.objections.map (bornChallengeSnapshot authority inventory fresh original saved) ++
  (List.finRange (source fresh).seed.task.slots.length).map (bornServiceSnapshot authority inventory fresh original saved)

abbrev Row := Fin (census authority inventory fresh original saved).length
variable {authority inventory fresh original saved}
def Row.snapshot (row : Row authority inventory fresh original saved) : Snapshot := (census authority inventory fresh original saved).get row
def Row.origin (row : Row authority inventory fresh original saved) := row.snapshot.origin
def Row.native (row : Row authority inventory fresh original saved) := row.snapshot.native
def Row.state (row : Row authority inventory fresh original saved) := row.snapshot.state
def Row.complete (row : Row authority inventory fresh original saved) := row.snapshot.complete
variable (authority inventory fresh original saved)

structure Slot where
  row : Row authority inventory fresh original saved
  index : Fin row.state.slots.length
structure Event where
  row : Row authority inventory fresh original saved
  index : Fin row.state.history.length
variable {authority inventory fresh original saved}
def Slot.origin (item : Slot authority inventory fresh original saved) := item.row.origin
def Slot.value (item : Slot authority inventory fresh original saved) : ObligationSlot item.origin.V := item.row.state.slots.get item.index
def Event.origin (item : Event authority inventory fresh original saved) := item.row.origin
def Event.value (item : Event authority inventory fresh original saved) : LifecycleEvent item.origin.V := item.row.state.history.get item.index
variable (authority inventory fresh original saved)
def slots : List (Slot authority inventory fresh original saved) :=
  (List.finRange (census authority inventory fresh original saved).length).flatMap fun row =>
    (List.finRange (Row.state row).slots.length).map fun index => ⟨row,index⟩
def events : List (Event authority inventory fresh original saved) :=
  (List.finRange (census authority inventory fresh original saved).length).flatMap fun row =>
    (List.finRange (Row.state row).history.length).map fun index => ⟨row,index⟩

theorem every_current_slot_is_generated (row : Row authority inventory fresh original saved) (index : Fin row.state.slots.length) :
    (⟨row,index⟩ : Slot authority inventory fresh original saved) ∈ slots authority inventory fresh original saved := by
  exact List.mem_flatMap.mpr ⟨row,List.mem_finRange _,List.mem_map.mpr ⟨index,List.mem_finRange _,rfl⟩⟩
theorem every_actual_history_item_is_generated (row : Row authority inventory fresh original saved) (index : Fin row.state.history.length) :
    (⟨row,index⟩ : Event authority inventory fresh original saved) ∈ events authority inventory fresh original saved := by
  exact List.mem_flatMap.mpr ⟨row,List.mem_finRange _,List.mem_map.mpr ⟨index,List.mem_finRange _,rfl⟩⟩

theorem all_current_native_states_have_their_original_run (row : Row authority inventory fresh original saved) :
    Nonempty (row.native.Run row.origin.initial row.state) := ⟨row.complete⟩

theorem all_six_current_source_families_keep_multiplicity :
    (census authority inventory fresh original saved).length =
      saved.oldGrants.length + saved.oldChallenges.length + (Pending.B authority).source.seed.task.slots.length +
      saved.grants.length + saved.objections.length + (source fresh).seed.task.slots.length := by
  simp only [census,List.length_append,List.length_map,List.length_finRange]
end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Registered.Loss.Responsibility
