import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Registered.Finance
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Responsibility.Transport

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Registered.Responsibility
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
noncomputable section
abbrev Origin := World.Input.Event.Future.Expiry.Progress.Responsibility.Origin

structure Snapshot where
  origin : Origin
  native : NativeResponsibilityProcess origin.V
  state : ResponsibilityState origin.V
  complete : native.Run origin.initial state

variable {fuel : ℚ} {old : Followup.Joint.Inventory fuel} (authority : ScopeRevision.Ready old)
  {originInputs : List (List Action)} (inventory : Pending.Joint.Inventory authority originInputs)
  (fresh : Handoff.Ready (Pending.B authority) (Future.advance authority inventory .revision).inputs)
  (word : List Action)

private def admitted {V : Vocabulary} (initial : ResponsibilityState V) : List (AdmittedObligation V) :=
  initial.slots.map fun slot => match slot with
    | .live obligation => obligation
    | .terminal archive => archive.obligation

def grantSnapshot (record : Mandate.Challenge.Cross.GrantResident (Pending.B authority) (legacy authority inventory).inputs) : Snapshot :=
  let initial := Continuation.Grant.origin record
  let occurrence : World.Input.Event.Future.Expiry.Progress.Responsibility.GrantOccurrence :=
    ⟨authority.scope,Pending.B authority,(legacy authority inventory).inputs.take record.birth.val,record.birth.val,
      Mandate.Challenge.Cross.grantWord (Pending.B authority) (legacy authority inventory).inputs record.birth.val,
      record.grant.proposal.item.val,record.grant.acceptance.item.val,record.grant.candidate⟩
  let saved := oldGrant authority inventory fresh word record
  ⟨⟨Continuation.Grant.V,initial,admitted initial,some occurrence⟩,saved.native,saved.state,saved.entire⟩

def challengeSnapshot (record : Mandate.Challenge.Cross.Resident (Pending.B authority) (legacy authority inventory).inputs) : Snapshot :=
  let saved := oldChallenge authority inventory fresh word record
  ⟨⟨Mandate.Challenge.V (Mandate.Challenge.fromHistory (Pending.B authority)) record.originInputs,.empty _,
    [Mandate.Challenge.obligation (Mandate.Challenge.fromHistory (Pending.B authority)) record.originInputs record.original],none⟩,
    saved.native,saved.state.current,saved.state.generated⟩

def serviceSnapshot (index : (Pending.B authority).source.Slot) : Snapshot :=
  let saved := oldService authority inventory fresh word index
  ⟨⟨OutstandingSource.History.NativeService.V (Pending.B authority).source originInputs,.empty _,
    [OutstandingSource.History.NativeService.obligation (Pending.B authority).source originInputs index],none⟩,
    OutstandingSource.History.NativeService.Expired.process (Pending.B authority).source originInputs,
    saved.state.current,saved.state.generated⟩

def bornGrantSnapshot (record : Mandate.Challenge.Cross.GrantResident (newBound fresh) (inputs authority inventory fresh word)) : Snapshot :=
  let initial := Mandate.Lifecycle.Observed.initialState base fresh.scope
    (Mandate.Challenge.Cross.grantCurrent (newBound fresh) (inputs authority inventory fresh word))
    (Mandate.Challenge.Cross.grantWord (newBound fresh) (inputs authority inventory fresh word)) record.birth.val record.grant
  let occurrence : World.Input.Event.Future.Expiry.Progress.Responsibility.GrantOccurrence :=
    ⟨fresh.scope,newBound fresh,(inputs authority inventory fresh word).take record.birth.val,record.birth.val,
      Mandate.Challenge.Cross.grantWord (newBound fresh) (inputs authority inventory fresh word) record.birth.val,
      record.grant.proposal.item.val,record.grant.acceptance.item.val,record.grant.candidate⟩
  ⟨⟨Continuation.Grant.V,initial,admitted initial,some occurrence⟩,
    Mandate.Lifecycle.Observed.process (base := base) (scope := fresh.scope)
      (currentAt := Mandate.Challenge.Cross.grantCurrent (newBound fresh) (inputs authority inventory fresh word))
      (wordAt := Mandate.Challenge.Cross.grantWord (newBound fresh) (inputs authority inventory fresh word))
      (birth := record.birth.val) (grant := record.grant),record.history.state,record.history.generated⟩

def bornChallengeSnapshot (record : Mandate.Challenge.Cross.Resident (newBound fresh) (inputs authority inventory fresh word)) : Snapshot :=
  ⟨⟨Mandate.Challenge.V (Mandate.Challenge.fromHistory (newBound fresh)) record.originInputs,.empty _,
    [Mandate.Challenge.obligation (Mandate.Challenge.fromHistory (newBound fresh)) record.originInputs record.original],none⟩,
    Mandate.Challenge.Cross.process (Mandate.Challenge.fromHistory (newBound fresh)) record.original,
    record.history.state.current,record.history.state.generated⟩

def bornServiceSnapshot (index : (source fresh).Slot) : Snapshot :=
  let saved := newServices authority inventory fresh word index
  ⟨⟨OutstandingSource.History.NativeService.V (source fresh) (inputs authority inventory fresh word),.empty _,
    [OutstandingSource.History.NativeService.obligation (source fresh) (inputs authority inventory fresh word) index],none⟩,
    OutstandingSource.History.NativeService.threadProcess (source fresh) (inputs authority inventory fresh word),
    saved.state.current,saved.state.generated⟩

/-- Separate data from indexing: the six original source lists are not evaluated
while elaborating a row's vocabulary. Repeated entries remain repeated. -/
def census : List Snapshot :=
  (legacy authority inventory).grants.map (grantSnapshot authority inventory fresh word) ++
  (legacy authority inventory).objections.map (challengeSnapshot authority inventory fresh word) ++
  (List.finRange (Pending.B authority).source.seed.task.slots.length).map (serviceSnapshot authority inventory fresh word) ++
  (newGrants authority inventory fresh word).map (bornGrantSnapshot authority inventory fresh word) ++
  (newChallenges authority inventory fresh word).map (bornChallengeSnapshot authority inventory fresh word) ++
  (List.finRange (source fresh).seed.task.slots.length).map (bornServiceSnapshot authority inventory fresh word)

abbrev Row := Fin (census authority inventory fresh word).length
variable {authority inventory fresh word}
def Row.snapshot (row : Row authority inventory fresh word) : Snapshot := (census authority inventory fresh word).get row
def Row.origin (row : Row authority inventory fresh word) := row.snapshot.origin
def Row.native (row : Row authority inventory fresh word) := row.snapshot.native
def Row.state (row : Row authority inventory fresh word) := row.snapshot.state
def Row.complete (row : Row authority inventory fresh word) := row.snapshot.complete
variable (authority inventory fresh word)

structure Slot where
  row : Row authority inventory fresh word
  index : Fin row.state.slots.length
structure Event where
  row : Row authority inventory fresh word
  index : Fin row.state.history.length
variable {authority inventory fresh word}
def Slot.origin (item : Slot authority inventory fresh word) := item.row.origin
def Slot.value (item : Slot authority inventory fresh word) : ObligationSlot item.origin.V := item.row.state.slots.get item.index
def Event.origin (item : Event authority inventory fresh word) := item.row.origin
def Event.value (item : Event authority inventory fresh word) : LifecycleEvent item.origin.V := item.row.state.history.get item.index
variable (authority inventory fresh word)
def slots : List (Slot authority inventory fresh word) :=
  (List.finRange (census authority inventory fresh word).length).flatMap fun row =>
    (List.finRange (Row.state row).slots.length).map fun index => ⟨row,index⟩
def events : List (Event authority inventory fresh word) :=
  (List.finRange (census authority inventory fresh word).length).flatMap fun row =>
    (List.finRange (Row.state row).history.length).map fun index => ⟨row,index⟩

theorem every_original_slot_is_generated (row : Row authority inventory fresh word) (index : Fin row.state.slots.length) :
    (⟨row,index⟩ : Slot authority inventory fresh word) ∈ slots authority inventory fresh word := by
  exact List.mem_flatMap.mpr ⟨row,List.mem_finRange _,List.mem_map.mpr ⟨index,List.mem_finRange _,rfl⟩⟩
theorem every_original_history_item_is_generated (row : Row authority inventory fresh word) (index : Fin row.state.history.length) :
    (⟨row,index⟩ : Event authority inventory fresh word) ∈ events authority inventory fresh word := by
  exact List.mem_flatMap.mpr ⟨row,List.mem_finRange _,List.mem_map.mpr ⟨index,List.mem_finRange _,rfl⟩⟩

theorem all_original_slots_and_histories_have_their_own_native_source (row : Row authority inventory fresh word) :
    Nonempty (row.native.Run row.origin.initial row.state) := ⟨row.complete⟩

theorem all_six_source_families_keep_their_original_multiplicity :
    (census authority inventory fresh word).length =
      (legacy authority inventory).grants.length + (legacy authority inventory).objections.length +
      (Pending.B authority).source.seed.task.slots.length + (newGrants authority inventory fresh word).length +
      (newChallenges authority inventory fresh word).length + (source fresh).seed.task.slots.length := by
  simp only [census,List.length_append,List.length_map,List.length_finRange]
end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Registered.Responsibility
