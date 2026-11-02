import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Challenge.Redress

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Challenge.Redress
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
noncomputable section
variable {epoch : Epoch} (inventory : Inventory epoch) (record : Record inventory)
  (pending : record.history.isPending = true)
  (active : Mandate.Response.Active (current epoch inventory.inputs))
include pending active

theorem actual_history_is_the_same_signed_pair :
    (original inventory record).history =
      ((record.beforeAppend epoch.bound (word inventory record)).receive (Bound (epoch := epoch))
        (first inventory record pending active)).receive (Bound (epoch := epoch)) (second inventory record pending active) := by
  change record.afterAppend epoch.bound (word inventory record) = _
  unfold Mandate.Challenge.Cross.Resident.afterAppend
  rw [emitted_positions inventory record pending active]
  rfl

omit active in
theorem before_pending : ∃ state slots,
    record.beforeAppend epoch.bound (word inventory record) =
      Mandate.Challenge.Cross.History.pending (transported inventory record pending) state slots := by
  rcases record with ⟨originInputs,claim,history,within⟩
  cases history with
  | pending target state slots => exact ⟨_,_,rfl⟩
  | closed state archive slots => cases pending

omit pending active in
private theorem receive_reconfirmation_pending
    (target : Mandate.Challenge.Cross.Target (Bound (epoch := epoch)) record.original
      (Mandate.Challenge.Cross.nextInputs inventory.inputs (word inventory record)))
    (state : (Mandate.Challenge.Cross.process (Bound (epoch := epoch)) record.original).GeneratedState)
    (slots : state.current.slots = [.live (Mandate.Challenge.Cross.tracked _ target)])
    (position : Mandate.Challenge.Position (Bound (epoch := epoch))
      (Mandate.Challenge.Cross.nextInputs inventory.inputs (word inventory record)))
    (receipt : Mandate.Challenge.Cross.Reconfirmation (Bound (epoch := epoch)) target)
    (decoded : Mandate.Challenge.Cross.readReconfirmation (Bound (epoch := epoch)) target position = some receipt) :
    ∃ next nextSlots, (Mandate.Challenge.Cross.History.pending target state slots).receive (Bound (epoch := epoch)) position =
      Mandate.Challenge.Cross.History.pending (receipt.target _) next nextSlots := by
  simp only [Mandate.Challenge.Cross.History.receive,decoded]
  refine ⟨_,?_,rfl⟩
  simp [NativeResponsibilityProcess.GeneratedState.step,NativeResponsibilityProcess.Edge.target,
    Mandate.Challenge.Cross.process,Mandate.Challenge.Cross.disposition,slots,
    BoundaryDisposition.targetSlot,ActiveCarryDisposition.target,Mandate.Challenge.Cross.tracked]

omit pending active in
private theorem receive_attempt_status
    (target : Mandate.Challenge.Cross.Target (Bound (epoch := epoch)) record.original
      (Mandate.Challenge.Cross.nextInputs inventory.inputs (word inventory record)))
    (state : (Mandate.Challenge.Cross.process (Bound (epoch := epoch)) record.original).GeneratedState)
    (slots : state.current.slots = [.live (Mandate.Challenge.Cross.tracked _ target)])
    (position : Mandate.Challenge.Position (Bound (epoch := epoch))
      (Mandate.Challenge.Cross.nextInputs inventory.inputs (word inventory record)))
    (receipt : Mandate.Challenge.Attempt (Bound (epoch := epoch))
      (Mandate.Challenge.Cross.nextInputs inventory.inputs (word inventory record)) target.claim)
    (absent : Mandate.Challenge.Cross.readReconfirmation (Bound (epoch := epoch)) target position = none)
    (decoded : Mandate.Challenge.readAttempt (Bound (epoch := epoch))
      (Mandate.Challenge.Cross.nextInputs inventory.inputs (word inventory record)) target.claim position = some receipt) :
    ((Mandate.Challenge.Cross.History.pending target state slots).receive (Bound (epoch := epoch)) position).isPending =
      if (Mandate.law base epoch.scope).Valid (receipt.position.item _ _).before (receipt.position.item _ _).request
      then false else true := by
  simp only [Mandate.Challenge.Cross.History.receive,absent,decoded]
  split <;> rfl

theorem actual_native_status :
    (original inventory record).history.isPending =
      if (Mandate.law base epoch.scope).Valid (current epoch inventory.inputs)
        (Mandate.request epoch.scope (current epoch inventory.inputs) (withdrawalActor inventory active) .revoke)
      then false else true := by
  obtain ⟨state,slots,saved⟩ := before_pending inventory record pending
  rw [actual_history_is_the_same_signed_pair inventory record pending active,saved]
  have decoded : Mandate.Challenge.Cross.readReconfirmation (Bound (epoch := epoch))
      (transported inventory record pending) (first inventory record pending active) =
        some (renewed inventory record pending active) := (Option.some_get _).symm
  obtain ⟨next,nextSlots,firstDone⟩ := receive_reconfirmation_pending inventory record _ state slots _ _ decoded
  rw [firstDone]
  have attempted : Mandate.Challenge.readAttempt (Bound (epoch := epoch))
      (Mandate.Challenge.Cross.nextInputs inventory.inputs (word inventory record))
      ((renewed inventory record pending active).target _).claim (second inventory record pending active) =
        some (withdrawal inventory record pending active) := (Option.some_get _).symm
  have status := receive_attempt_status inventory record _ next nextSlots _ _
    (second_cannot_reconfirm inventory record pending active) attempted
  rw [withdrawal_position inventory record pending active,second_item inventory record pending active] at status
  exact status

omit pending active in
theorem an_empty_word_preserves_the_complete_original_native_state (empty : word inventory record = []) :
    (original inventory record).history.state = record.history.state := by
  have noItems : items inventory record = [] := by
    change (Mandate.law base epoch.scope).rawItems (actual inventory record).before (actual inventory record).submitted = []
    rw [(actual_word_and_saved_cut inventory record).1,(actual_word_and_saved_cut inventory record).2,empty]
    rfl
  have noPositions : Mandate.Challenge.positionsAt (Bound (epoch := epoch))
      (Mandate.Challenge.Cross.nextInputs inventory.inputs (word inventory record)) (inventory.inputs.length+2) = [] := by
    apply List.eq_nil_iff_length_eq_zero.mpr
    simp only [Mandate.Challenge.positionsAt,List.length_map,List.length_finRange]
    change (items inventory record).length = 0
    rw [noItems]
    rfl
  change (record.afterAppend epoch.bound (word inventory record)).state = _
  rw [Mandate.Challenge.Cross.Resident.afterAppend,noPositions]
  exact record.old_entire_state_is_the_actual_continuation_start epoch.bound (word inventory record)

theorem accepted_attempt_is_the_actual_withdrawal
    (paid : (Mandate.law base epoch.scope).Valid (current epoch inventory.inputs)
      (Mandate.request epoch.scope (current epoch inventory.inputs) (withdrawalActor inventory active) .revoke)) :
    (actual inventory record).after.technology.holder = none ∧
    (actual inventory record).after.technology.offered = none ∧
    (actual inventory record).after.technology.version = (current epoch inventory.inputs).technology.version+1 := by
  have actualPaid : (Mandate.law base epoch.scope).Valid
      ((withdrawal inventory record pending active).position.item _ _).before
      ((withdrawal inventory record pending active).position.item _ _).request := by
    rw [withdrawal_position,second_item]
    exact paid
  have withdrawn := (withdrawal inventory record pending active).actual_withdrawal _ _ _ actualPaid
  rw [withdrawal_position,second_item] at withdrawn
  change _ ∧ _ ∧ _ = (((renewed inventory record pending active).target _).snapshot _).version+1 at withdrawn
  rw [renewed_snapshot] at withdrawn
  rw [(actual inventory record).after_exact,(actual_word_and_saved_cut inventory record).1,
    (actual_word_and_saved_cut inventory record).2]
  change ((Mandate.law base epoch.scope).next (current epoch inventory.inputs) (word inventory record)).technology.holder = none ∧
    ((Mandate.law base epoch.scope).next (current epoch inventory.inputs) (word inventory record)).technology.offered = none ∧
    ((Mandate.law base epoch.scope).next (current epoch inventory.inputs) (word inventory record)).technology.version =
      (current epoch inventory.inputs).technology.version+1
  rw [pending_active_word inventory record pending active]
  simpa only [RawLaw.next,RawLaw.execute,signature_preserves_the_entire_current] using withdrawn

omit pending in
theorem an_actual_refused_attempt_covers_exactly_current_member_revocations
    (refused : ¬ (Mandate.law base epoch.scope).Valid (current epoch inventory.inputs)
      (Mandate.request epoch.scope (current epoch inventory.inputs) (withdrawalActor inventory active) .revoke)) :
    ∀ actor ∈ Delegation.members epoch.scope.task,
      ¬ (Mandate.law base epoch.scope).Valid (current epoch inventory.inputs)
        (Mandate.request epoch.scope (current epoch inventory.inputs) actor .revoke) := by
  rcases (decision inventory).actual_disposition with inactive | ⟨actor,member,emitted,paid | blocked⟩
  · exact False.elim (inactive.1 active)
  · have same := congrArg (fun word => word.map Request.signer) (emitted.symm.trans (active_decision_word inventory active))
    have actors : actor = withdrawalActor inventory active := by simpa only [List.map_cons,List.map_nil,Mandate.request,List.cons.injEq,and_true] using same
    rw [actors] at paid
    exact False.elim (refused paid.1)
  · exact blocked.2.2

omit pending active in
inductive Disposition where
  | private archived (already : record.history.isPending = false)
      (empty : word inventory record = [])
      (preserved : (original inventory record).history.state = record.history.state)
  | private inactive (live : record.history.isPending = true)
      (absent : ¬ Mandate.Response.Active (current epoch inventory.inputs))
      (empty : word inventory record = [])
      (preserved : (original inventory record).history.state = record.history.state)
  | private fulfilled (live : record.history.isPending = true)
      (active : Mandate.Response.Active (current epoch inventory.inputs))
      (paid : (Mandate.law base epoch.scope).Valid (current epoch inventory.inputs)
        (Mandate.request epoch.scope (current epoch inventory.inputs) (withdrawalActor inventory active) .revoke))
      (closed : (original inventory record).history.isPending = false)
      (withdrawn : (actual inventory record).after.technology.holder = none ∧
        (actual inventory record).after.technology.offered = none ∧
        (actual inventory record).after.technology.version = (current epoch inventory.inputs).technology.version+1)
  | private deferred (live : record.history.isPending = true)
      (active : Mandate.Response.Active (current epoch inventory.inputs))
      (refused : ¬ (Mandate.law base epoch.scope).Valid (current epoch inventory.inputs)
        (Mandate.request epoch.scope (current epoch inventory.inputs) (withdrawalActor inventory active) .revoke))
      (coverage : ∀ actor ∈ Delegation.members epoch.scope.task,
        ¬ (Mandate.law base epoch.scope).Valid (current epoch inventory.inputs)
          (Mandate.request epoch.scope (current epoch inventory.inputs) actor .revoke))
      (retained : (original inventory record).history.isPending = true)

omit pending active in
def produce : Disposition inventory record := by
  by_cases live : record.history.isPending = true
  · by_cases active : Mandate.Response.Active (current epoch inventory.inputs)
    · by_cases paid : (Mandate.law base epoch.scope).Valid (current epoch inventory.inputs)
        (Mandate.request epoch.scope (current epoch inventory.inputs) (withdrawalActor inventory active) .revoke)
      · exact .fulfilled live active paid (by rw [actual_native_status inventory record live active,if_pos paid])
          (accepted_attempt_is_the_actual_withdrawal inventory record live active paid)
      · exact .deferred live active paid
          (an_actual_refused_attempt_covers_exactly_current_member_revocations inventory active paid)
          (by rw [actual_native_status inventory record live active,if_neg paid])
    · have empty : word inventory record = [] := by simp [word,active]
      exact .inactive live active empty (an_empty_word_preserves_the_complete_original_native_state inventory record empty)
  · have archived : record.history.isPending = false := Bool.eq_false_iff.mpr live
    have empty : word inventory record = [] := by simp [word,archived]
    exact .archived archived empty (an_empty_word_preserves_the_complete_original_native_state inventory record empty)

inductive Kind where
  | archived | inactive | fulfilled | deferred
  deriving DecidableEq

def Disposition.kind : Disposition inventory record → Kind
  | .archived .. => .archived | .inactive .. => .inactive
  | .fulfilled .. => .fulfilled | .deferred .. => .deferred

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Challenge.Redress
