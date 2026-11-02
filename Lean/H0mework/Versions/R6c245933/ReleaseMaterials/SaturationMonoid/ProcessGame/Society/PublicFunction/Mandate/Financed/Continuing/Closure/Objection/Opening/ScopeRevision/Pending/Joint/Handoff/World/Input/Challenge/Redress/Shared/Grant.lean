import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Challenge.Redress.Shared.Newborn
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Challenge.Cross.Release

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Challenge.Redress.Shared.Grant
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
noncomputable section
variable {epoch : Epoch} (inventory : Inventory epoch)

abbrev Record := Mandate.Challenge.Cross.GrantResident epoch.bound inventory.inputs
abbrev sourceCurrent := Mandate.Challenge.Cross.grantCurrent epoch.bound (Inputs inventory)
abbrev sourceWord := Mandate.Challenge.Cross.grantWord epoch.bound (Inputs inventory)
abbrev sourceItems := Mandate.Lifecycle.Observed.Release.items (base := base) (scope := epoch.scope)
  (currentAt := sourceCurrent inventory) (wordAt := sourceWord inventory) (inventory.inputs.length+1)

theorem source_current_is_the_same_saved_cut : sourceCurrent inventory (inventory.inputs.length+1) = current epoch inventory.inputs :=
  Mandate.Challenge.Cross.emitted_word_uses_actual_cut epoch.bound inventory.inputs (word inventory)

theorem source_word_is_the_same_shared_word : sourceWord inventory (inventory.inputs.length+1) = word inventory :=
  Mandate.Challenge.Cross.emitted_word_is_actual epoch.bound inventory.inputs (word inventory)

theorem source_items_are_the_same_actual_items : (sourceItems inventory).map Subtype.val = items inventory := by
  simp only [sourceItems,Mandate.Lifecycle.Observed.Release.items,List.attach_map_subtype_val]
  rw [source_current_is_the_same_saved_cut,source_word_is_the_same_shared_word]
  change _ = (Mandate.law base epoch.scope).rawItems (actual inventory).before (actual inventory).submitted
  rw [(actual_word_and_saved_cut inventory).1,(actual_word_and_saved_cut inventory).2]

variable (active : Mandate.Response.Active (current epoch inventory.inputs))

def index : Mandate.Challenge.Cross.GrantResident.ReleaseIndex epoch.bound (inputs := inventory.inputs) (word inventory) :=
  ⟨(actors inventory).length,by
    change (actors inventory).length < (sourceItems inventory).length
    rw [← List.length_map (f := Subtype.val),source_items_are_the_same_actual_items,items_exact inventory active]
    simp⟩

def sourceItem := (sourceItems inventory).get (index inventory active)

theorem source_item_is_the_same_actual_revoke : (sourceItem inventory active).val =
    ⟨(actors inventory).length,current epoch inventory.inputs,
      Mandate.request epoch.scope (current epoch inventory.inputs) (withdrawalActor inventory active) .revoke⟩ := by
  have same := congrArg (fun list => list[(actors inventory).length]?) (source_items_are_the_same_actual_items inventory)
  have sourceBound : (actors inventory).length < (sourceItems inventory).length := (index inventory active).isLt
  have targetBound : (actors inventory).length < (items inventory).length := (withdrawalPosition inventory active).index.isLt
  rw [List.getElem?_map,List.getElem?_eq_getElem sourceBound,List.getElem?_eq_getElem targetBound,Option.map_some] at same
  have sameItem : (sourceItem inventory active).val = (withdrawalPosition inventory active).item _ _ := Option.some.inj same
  exact sameItem.trans (withdrawal_item inventory active)

variable (paid : (Mandate.law base epoch.scope).Valid (current epoch inventory.inputs)
  (Mandate.request epoch.scope (current epoch inventory.inputs) (withdrawalActor inventory active) .revoke))

def command : Mandate.ActualCommand base epoch.scope
    (sourceCurrent inventory (inventory.inputs.length+1)) (sourceWord inventory (inventory.inputs.length+1)) :=
  (Mandate.recognize base epoch.scope _ _ (sourceItem inventory active)).get (by
    have accepted : (Mandate.law base epoch.scope).Valid (sourceItem inventory active).val.before (sourceItem inventory active).val.request := by
      rw [source_item_is_the_same_actual_revoke]
      exact paid
    have expected : (sourceItem inventory active).val.request.operation =
        Operation.revise (withdrawalActor inventory active) (Mandate.advance epoch.scope (current epoch inventory.inputs) .revoke) := by
      rw [source_item_is_the_same_actual_revoke]
      rfl
    unfold Mandate.recognize
    split
    · rename_i operator target operation
      have sameTarget := (Operation.revise.inj (expected.symm.trans operation)).2
      have targetMarked : target.last = some (.revoke : Mandate.Command Bool) := by rw [← sameTarget]; rfl
      split
      · rename_i absent
        rw [targetMarked] at absent
        cases absent
      · simp only [dif_pos accepted,Option.isSome_some]
    · rename_i notRevise
      exact False.elim (notRevise _ _ expected))

private theorem recognize_item
    (event : Mandate.ActualCommand base epoch.scope
      (sourceCurrent inventory (inventory.inputs.length+1)) (sourceWord inventory (inventory.inputs.length+1)))
    (found : Mandate.recognize base epoch.scope _ _ (sourceItem inventory active) = some event) :
    event.item = sourceItem inventory active := by
  unfold Mandate.recognize at found
  split at found
  · split at found
    · cases found
    · split at found
      · cases Option.some.inj found; rfl
      · cases found
  · cases found

theorem command_has_the_actual_item : (command inventory active paid).item = sourceItem inventory active :=
  recognize_item inventory active (command inventory active paid) (Option.some_get _).symm

theorem command_is_the_actual_revoke : (command inventory active paid).command = .revoke := by
  have operation := (command inventory active paid).operation
  have marked := (command inventory active paid).marked
  rw [command_has_the_actual_item,source_item_is_the_same_actual_revoke] at operation
  change Operation.revise (withdrawalActor inventory active) (Mandate.advance epoch.scope (current epoch inventory.inputs) .revoke) = _ at operation
  have target := (Operation.revise.inj operation).2
  rw [← target,Mandate.advance_last] at marked
  exact (Option.some.inj marked).symm


omit paid in
theorem signature_prefix_keeps_the_complete_original_history (record : Record inventory) :
    Mandate.Lifecycle.Observed.Release.before (record.releaseBefore epoch.bound (word inventory))
      (inventory.inputs.length+1) (index inventory active) = record.releaseBefore epoch.bound (word inventory) := by
  apply Mandate.Lifecycle.Observed.History.foldl_consume_eq_of_not_revise
  intro item member operator target operation
  have plain : item.val ∈ ((sourceItems inventory).take (actors inventory).length).map Subtype.val :=
    List.mem_map.mpr ⟨item,member,rfl⟩
  have prefixItems : ((sourceItems inventory).take (actors inventory).length).map Subtype.val =
      (actors inventory).zipIdx.map (fun pair =>
        (⟨pair.2,current epoch inventory.inputs,Input.signature epoch pair.1⟩ : ExecutionItem Bool Good Mandate.Source.Port (Mandate.State Bool Unit) Unit)) := by
    rw [List.map_take,source_items_are_the_same_actual_items,items_exact inventory active]
    have length : ((actors inventory).zipIdx.map (fun pair =>
        (⟨pair.2,current epoch inventory.inputs,Input.signature epoch pair.1⟩ : ExecutionItem Bool Good Mandate.Source.Port (Mandate.State Bool Unit) Unit))).length = (actors inventory).length := by simp
    rw [← length,List.take_left]
  rw [prefixItems] at plain
  obtain ⟨pair,_,same⟩ := List.mem_map.mp plain
  rw [← same] at operation
  cases operation

variable (record : Record inventory)

private theorem actual_boundary_with_holder_loss_is_read
    (event : Mandate.ActualCommand base epoch.scope
      (sourceCurrent inventory (inventory.inputs.length+1)) (sourceWord inventory (inventory.inputs.length+1)))
    (sameItem : event.item = (sourceItems inventory).get (index inventory active))
    (boundary : Mandate.Lifecycle.IsBoundary event.command)
    (held : event.item.val.before.technology.holder = some
      (Mandate.Lifecycle.Observed.Release.before (record.releaseBefore epoch.bound (word inventory))
        (inventory.inputs.length+1) (index inventory active)).obligation.bearer)
    (ended : event.after.technology.holder ≠ some
      (Mandate.Lifecycle.Observed.Release.before (record.releaseBefore epoch.bound (word inventory))
        (inventory.inputs.length+1) (index inventory active)).obligation.bearer) :
    (Mandate.Lifecycle.Observed.Release.read (record.releaseBefore epoch.bound (word inventory))
      (inventory.inputs.length+1) (index inventory active)).isSome = true := by
  have follows : Mandate.Lifecycle.Later base epoch.scope (sourceCurrent inventory) (sourceWord inventory)
      record.birth.val (Mandate.Challenge.Cross.transportGrant epoch.bound inventory.inputs (word inventory) record.birth record.grant)
      (inventory.inputs.length+1) event.item.val.index := Or.inl record.birth.isLt
  have released := And.intro held ended
  rw [Mandate.Lifecycle.Observed.Release.read_isSome_iff]
  rw [show Mandate.Lifecycle.Observed.readEvent
      (Mandate.Lifecycle.Observed.Release.before (record.releaseBefore epoch.bound (word inventory))
        (inventory.inputs.length+1) (index inventory active)).obligation
      (Mandate.Lifecycle.Observed.Release.before (record.releaseBefore epoch.bound (word inventory))
        (inventory.inputs.length+1) (index inventory active)).origin (inventory.inputs.length+1)
      ((sourceItems inventory).get (index inventory active)) =
    Mandate.Lifecycle.Observed.readEvent
      (Mandate.Lifecycle.Observed.Release.before (record.releaseBefore epoch.bound (word inventory))
        (inventory.inputs.length+1) (index inventory active)).obligation
      (Mandate.Lifecycle.Observed.Release.before (record.releaseBefore epoch.bound (word inventory))
        (inventory.inputs.length+1) (index inventory active)).origin (inventory.inputs.length+1) event.item from congrArg _ sameItem.symm]
  simp only [Mandate.Lifecycle.Observed.readEvent,event.recognize_complete,Mandate.Lifecycle.readEvent,
    dif_pos follows,dif_pos boundary,Option.map_some]
  simp only [Mandate.Lifecycle.Observed.Release.isRelease,Mandate.Lifecycle.Observed.Event.disposition,
    Mandate.Lifecycle.Observed.acceptedDisposition]
  split_ifs with condition
  · rfl
  · exact False.elim (condition released)

include paid in
theorem the_same_paid_revoke_generates_the_original_native_release
    (held : (current epoch inventory.inputs).technology.holder = some record.history.obligation.bearer) :
    (Mandate.Lifecycle.Observed.Release.read (record.releaseBefore epoch.bound (word inventory))
      (inventory.inputs.length+1) (index inventory active)).isSome = true := by
  apply actual_boundary_with_holder_loss_is_read inventory active record (command inventory active paid)
    (command_has_the_actual_item inventory active paid)
  · rw [command_is_the_actual_revoke]
    trivial
  · rw [command_has_the_actual_item,source_item_is_the_same_actual_revoke,
      signature_prefix_keeps_the_complete_original_history,
      record.release_before_keeps_the_same_original_obligation]
    exact held
  · rw [(command inventory active paid).actual_effect.1,command_is_the_actual_revoke]
    change (none : Option Bool) ≠ some _
    intro impossible
    cases impossible

def nativeRelease
    (held : (current epoch inventory.inputs).technology.holder = some record.history.obligation.bearer) :
    record.ReleaseReceipt epoch.bound (word inventory) :=
  ⟨index inventory active,
    (Mandate.Lifecycle.Observed.Release.read (record.releaseBefore epoch.bound (word inventory))
      (inventory.inputs.length+1) (index inventory active)).get
      (the_same_paid_revoke_generates_the_original_native_release inventory active paid record held)⟩

theorem the_native_release_is_in_the_exact_actual_original_census
    (held : (current epoch inventory.inputs).technology.holder = some record.history.obligation.bearer) :
    nativeRelease inventory active paid record held ∈ record.releaseReceipts epoch.bound (word inventory) :=
  record.every_read_release_is_retained epoch.bound _ _ _ (Option.some_get _).symm


omit paid active in
def receipts := record.releaseReceipts epoch.bound (word inventory)

omit paid active in
def actualEvent (receipt : record.ReleaseReceipt epoch.bound (word inventory)) :=
  ((Mandate.Lifecycle.Observed.Release.before (record.releaseBefore epoch.bound (word inventory))
    (inventory.inputs.length+1) receipt.1).edge receipt.2.event).lifecycleEvent

omit paid active in
theorem every_receipt_is_recorded_in_the_original_actual_advance
    (receipt : record.ReleaseReceipt epoch.bound (word inventory)) :
    actualEvent inventory record receipt ∈ (record.advance epoch.bound (word inventory)).history.state.history ∧
    (actualEvent inventory record receipt).kind = .bearerRelease ∧
    (record.advance epoch.bound (word inventory)).history.state.LiveAt 0 :=
  record.release_is_in_the_original_advance epoch.bound (word inventory) receipt

omit paid active in
inductive Disposition where
  | private inactive (absent : ¬ Mandate.Response.Active (current epoch inventory.inputs))
      (empty : word inventory = [])
      (live : (record.advance epoch.bound (word inventory)).history.state.LiveAt 0)
  | private unheld (active : Mandate.Response.Active (current epoch inventory.inputs))
      (different : (current epoch inventory.inputs).technology.holder ≠ some record.history.obligation.bearer)
      (live : (record.advance epoch.bound (word inventory)).history.state.LiveAt 0)
  | private refused (active : Mandate.Response.Active (current epoch inventory.inputs))
      (held : (current epoch inventory.inputs).technology.holder = some record.history.obligation.bearer)
      (refused : ¬ (Mandate.law base epoch.scope).Valid (current epoch inventory.inputs)
        (Mandate.request epoch.scope (current epoch inventory.inputs) (withdrawalActor inventory active) .revoke))
      (coverage : ∀ actor ∈ Delegation.members epoch.scope.task,
        ¬ (Mandate.law base epoch.scope).Valid (current epoch inventory.inputs)
          (Mandate.request epoch.scope (current epoch inventory.inputs) actor .revoke))
      (live : (record.advance epoch.bound (word inventory)).history.state.LiveAt 0)
  | private released (active : Mandate.Response.Active (current epoch inventory.inputs))
      (held : (current epoch inventory.inputs).technology.holder = some record.history.obligation.bearer)
      (paid : (Mandate.law base epoch.scope).Valid (current epoch inventory.inputs)
        (Mandate.request epoch.scope (current epoch inventory.inputs) (withdrawalActor inventory active) .revoke))
      (certificate : record.ReleaseReceipt epoch.bound (word inventory))
      (exact : certificate = nativeRelease inventory active paid record held)
      (listed : certificate ∈ receipts inventory record)
      (recorded : actualEvent inventory record certificate ∈ (record.advance epoch.bound (word inventory)).history.state.history)
      (kind : (actualEvent inventory record certificate).kind = .bearerRelease)
      (live : (record.advance epoch.bound (word inventory)).history.state.LiveAt 0)

omit paid active in
def receive : Disposition inventory record := by
  have live := (record.advance epoch.bound (word inventory)).history.responsibility_remains_live
  by_cases active : Mandate.Response.Active (current epoch inventory.inputs)
  · letI : Decidable ((current epoch inventory.inputs).technology.holder = some record.history.obligation.bearer) :=
      (inferInstance : DecidableEq (Option Bool)) _ _
    by_cases held : (current epoch inventory.inputs).technology.holder = some record.history.obligation.bearer
    · by_cases paid : (Mandate.law base epoch.scope).Valid (current epoch inventory.inputs)
        (Mandate.request epoch.scope (current epoch inventory.inputs) (withdrawalActor inventory active) .revoke)
      · let certificate := nativeRelease inventory active paid record held
        have recorded := every_receipt_is_recorded_in_the_original_actual_advance inventory record certificate
        exact .released active held paid certificate rfl
          (the_native_release_is_in_the_exact_actual_original_census inventory active paid record held) recorded.1 recorded.2.1 live
      · exact .refused active held paid
          (Redress.an_actual_refused_attempt_covers_exactly_current_member_revocations inventory active paid) live
    · exact .unheld active held live
  · exact .inactive active (by simp [word,active]) live

omit paid active record in
inductive Kind where
  | inactive | unheld | refused | released
  deriving DecidableEq

omit paid active in
def Disposition.kind : Disposition inventory record → Kind
  | .inactive .. => .inactive | .unheld .. => .unheld
  | .refused .. => .refused | .released .. => .released

omit paid active record in
def allOriginalGrants : List (Sigma fun original : {record : Record inventory // record ∈ inventory.grants} =>
    Disposition inventory original.val) :=
  inventory.grants.attach.map fun record => ⟨record,receive inventory record.val⟩

omit paid active in
theorem every_original_has_its_source_selected_disposition (member : record ∈ inventory.grants) :
    (⟨⟨record,member⟩,receive inventory record⟩ : Sigma fun original : {record : Record inventory // record ∈ inventory.grants} =>
      Disposition inventory original.val) ∈ allOriginalGrants inventory :=
  List.mem_map.mpr ⟨⟨record,member⟩,List.mem_attach _ _,rfl⟩

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Challenge.Redress.Shared.Grant
