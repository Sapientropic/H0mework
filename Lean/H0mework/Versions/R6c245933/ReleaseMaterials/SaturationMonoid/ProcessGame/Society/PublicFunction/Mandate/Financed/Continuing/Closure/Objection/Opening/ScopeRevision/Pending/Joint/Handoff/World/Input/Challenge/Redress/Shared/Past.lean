import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Challenge.Redress.Shared.Execution
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Challenge.Redress.Shared.Residual
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.ChallengeLine.Finality

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Challenge.Redress.Shared.Past
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
open Input.Event Input.Event.Future.Expiry.Progress.Responsibility
noncomputable section
variable {epoch : Epoch} (inventory : Inventory epoch)

abbrev source := boundarySource epoch (inventory.inputs ++ [word inventory])
abbrev receipts := World.receipts inventory (word inventory)

def grantAfter (entry : GrantCohort) := entry.advance (source inventory) (receipts inventory)

theorem every_past_grant_receipt_is_in_its_original_final_history
    (entry : GrantCohort) (member : entry ∈ inventory.pastGrants)
    (receipt : Mandate.Challenge.ScopeBoundary.Receipt (source inventory))
    (present : receipt ∈ receipts inventory) :
    Continuation.Grant.image (source inventory) entry.origin.2.history.obligation receipt ∈
      (Runtime.originalRow inventory (.pastGrant entry member)).state.history := by
  let row : Input.Event.Future.Expiry.Progress.Responsibility.Row ⟨epoch,inventory⟩ := .pastGrant entry member
  let position : Located row.origin ⟨epoch,inventory⟩ := ⟨row,rfl⟩
  have retained : (grantAfter inventory entry).saved.state.history <+:
      (Runtime.originalRow inventory (.pastGrant entry member)).state.history :=
    follow_retains_the_complete_original_history (Dispatch.native (after inventory)) (position.submit (word inventory))
  apply retained.subset
  change _ ∈ (entry.saved.consume (source inventory) (receipts inventory)).state.history
  rw [Continuation.Grant.Saved.consume_history]
  exact List.mem_append_right _ (List.mem_map.mpr ⟨receipt,present,rfl⟩)

structure GrantReceipt (entry : GrantCohort) (member : entry ∈ inventory.pastGrants) where
  private mk ::
  actual : (grantAfter inventory entry).saved.state.history = entry.saved.state.history ++
    (receipts inventory).map (Continuation.Grant.image (source inventory) entry.origin.2.history.obligation)
  live : (grantAfter inventory entry).saved.state.slots = [.live entry.origin.2.history.obligation]
  recorded : ∀ receipt ∈ receipts inventory,
    Continuation.Grant.image (source inventory) entry.origin.2.history.obligation receipt ∈
      (Runtime.originalRow inventory (.pastGrant entry member)).state.history

theorem grant (entry : GrantCohort) (member : entry ∈ inventory.pastGrants) : GrantReceipt inventory entry member :=
  ⟨Continuation.Grant.Saved.consume_history entry.saved _ _,(grantAfter inventory entry).saved.slots,
    every_past_grant_receipt_is_in_its_original_final_history inventory entry member⟩

def observations (entry : ServiceCohort epoch.source.seed.initial.clock) :=
  entry.observations (source inventory) (inventory.inputs.length+1) 1

def serviceAfter (entry : ServiceCohort epoch.source.seed.initial.clock) :=
  entry.advance (source inventory) (le_refl _) (inventory.inputs.length+1) 1

abbrev serviceImage (entry : ServiceCohort epoch.source.seed.initial.clock) :=
  OutstandingSource.History.NativeService.Expired.image entry.origin.source entry.origin.originInputs entry.origin.index

theorem every_expired_service_observation_is_the_actual_visit
    (entry : ServiceCohort epoch.source.seed.initial.clock) :
    (observations inventory entry).map OutstandingSource.History.NativeService.ExpiredInput.depth = [inventory.inputs.length+1] := by
  simpa only [observations,List.range_succ,List.range_zero,List.nil_append,List.map_cons,List.map_nil,Nat.add_zero] using entry.every_actual_visit_is_present (source inventory) (le_refl _) (inventory.inputs.length+1) 1

theorem every_live_past_service_event_is_in_its_original_final_history
    (entry : ServiceCohort epoch.source.seed.initial.clock) (member : entry ∈ inventory.pastServices)
    (live : entry.origin.original.state.current.slots =
      [.live (OutstandingSource.History.NativeService.obligation entry.origin.source entry.origin.originInputs entry.origin.index)])
    (input : OutstandingSource.History.NativeService.ExpiredInput entry.origin.source)
    (present : input ∈ observations inventory entry) :
    serviceImage entry input ∈ (Runtime.originalRow inventory (.pastService entry member)).state.history := by
  let row : Input.Event.Future.Expiry.Progress.Responsibility.Row ⟨epoch,inventory⟩ := .pastService entry member
  let position : Located row.origin ⟨epoch,inventory⟩ := ⟨row,rfl⟩
  have retained : (serviceAfter inventory entry).saved.state.current.history <+:
      (Runtime.originalRow inventory (.pastService entry member)).state.history :=
    follow_retains_the_complete_original_history (Dispatch.native (after inventory)) (position.submit (word inventory))
  apply retained.subset
  change _ ∈ (entry.saved.consume entry.origin.source (observations inventory entry)).state.current.history
  rw [OutstandingSource.History.NativeService.Expired.Continuation.consume_history _ _ live]
  exact List.mem_append_right _ (List.mem_map.mpr ⟨input,present,rfl⟩)

inductive ServiceDisposition (entry : ServiceCohort epoch.source.seed.initial.clock) where
  | private archived (terminal : entry.origin.original.state.current.TerminalAt 0)
      (literal : (serviceAfter inventory entry).saved.state = entry.saved.state)
  | private live (slots : entry.origin.original.state.current.slots =
        [.live (OutstandingSource.History.NativeService.obligation entry.origin.source entry.origin.originInputs entry.origin.index)])
      (history : (serviceAfter inventory entry).saved.state.current.history = entry.saved.state.current.history ++
        (observations inventory entry).map (serviceImage entry))

def serviceDisposition (entry : ServiceCohort epoch.source.seed.initial.clock) : ServiceDisposition inventory entry := by
  cases entry.origin.original.shape with
  | live unpaid slots =>
    exact .live slots (OutstandingSource.History.NativeService.Expired.Continuation.consume_history _ _ slots _)
  | terminal archive paid recorded original_eq slots =>
    have terminal : entry.origin.original.state.current.TerminalAt 0 := ⟨archive,by simp [slots]⟩
    exact .archived terminal (OutstandingSource.History.NativeService.Expired.Continuation.terminal_state_is_literal _ _ terminal _)

structure ServiceReceipt (entry : ServiceCohort epoch.source.seed.initial.clock) (member : entry ∈ inventory.pastServices) where
  private mk ::
  disposition : ServiceDisposition inventory entry
  exact : disposition = serviceDisposition inventory entry
  depth : (observations inventory entry).map OutstandingSource.History.NativeService.ExpiredInput.depth = [inventory.inputs.length+1]
  recorded : entry.origin.original.state.current.slots =
      [.live (OutstandingSource.History.NativeService.obligation entry.origin.source entry.origin.originInputs entry.origin.index)] →
    ∀ input ∈ observations inventory entry,
      serviceImage entry input ∈ (Runtime.originalRow inventory (.pastService entry member)).state.history

def service (entry : ServiceCohort epoch.source.seed.initial.clock) (member : entry ∈ inventory.pastServices) : ServiceReceipt inventory entry member :=
  ⟨serviceDisposition inventory entry,rfl,every_expired_service_observation_is_the_actual_visit inventory entry,
    every_live_past_service_event_is_in_its_original_final_history inventory entry member⟩

def finalChallenge (entry : ChallengeCohort epoch.scope) (member : entry ∈ inventory.pastChallenges) :=
  (Runtime.native inventory).challenge entry member

def challengePosition (entry : ChallengeCohort epoch.scope) (member : entry ∈ inventory.pastChallenges) :=
  let final := finalChallenge inventory entry member
  let row : Future.ChallengeLine.Row (Runtime.answer inventory).packet := .past final.row final.member
  (⟨row,rfl⟩ : Future.ChallengeLine.Located row.origin (Runtime.answer inventory).packet)

def challenge (entry : ChallengeCohort epoch.scope) (member : entry ∈ inventory.pastChallenges) :=
  Future.ChallengeLine.Finality.readRow _ (challengePosition inventory entry member)

structure Receipt where
  private mk ::
  grants : ∀ (entry : GrantCohort) (member : entry ∈ inventory.pastGrants), GrantReceipt inventory entry member
  challenges : ∀ (entry : ChallengeCohort epoch.scope) (member : entry ∈ inventory.pastChallenges),
    Future.ChallengeLine.Finality.SlotDisposition _ (challengePosition inventory entry member)
  services : ∀ (entry : ServiceCohort epoch.source.seed.initial.clock) (member : entry ∈ inventory.pastServices), ServiceReceipt inventory entry member

def produce : Receipt inventory := ⟨grant inventory,challenge inventory,service inventory⟩
end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Challenge.Redress.Shared.Past

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Challenge.Redress.Shared.Past.Native
variable {epoch : Epoch} (inventory : Inventory epoch)
def produce : Receipt inventory := ⟨Past.grant inventory,Past.challenge inventory,Past.service inventory⟩
theorem produce_exact : produce inventory = Past.produce inventory := rfl
@[csimp] theorem produce_codegen : @Past.produce = @produce := rfl
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Challenge.Redress.Shared.Past.Native
