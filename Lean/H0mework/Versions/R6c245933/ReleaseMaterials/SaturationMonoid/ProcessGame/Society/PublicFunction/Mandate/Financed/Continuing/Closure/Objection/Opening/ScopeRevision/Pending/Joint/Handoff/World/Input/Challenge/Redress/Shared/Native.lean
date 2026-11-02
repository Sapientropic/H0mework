import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Challenge.Redress.Shared

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Challenge.Redress.Shared
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
noncomputable section
variable {epoch : Epoch} (inventory : Inventory epoch)

abbrev Inputs := Mandate.Challenge.Cross.nextInputs inventory.inputs (word inventory)
abbrev Position := Mandate.Challenge.Position (Bound (epoch := epoch)) (Inputs inventory)

variable (record : Record inventory) (pending : record.history.isPending = true)

def transported := Mandate.Challenge.Cross.transportTarget epoch.bound (word inventory)
  (Redress.target inventory record pending) (Redress.target_within inventory record pending)

theorem transported_signer : (transported inventory record pending).claim.signer _ _ = claimant inventory record := by
  have same := (Mandate.Challenge.Cross.replacement_same_item_and_snapshot epoch.bound inventory.inputs
    (word inventory) (Redress.target inventory record pending).claim (Redress.target_within inventory record pending)).2.2.1
  refine same.trans ?_
  rcases record with ⟨originInputs,claim,history,within⟩
  cases history with
  | pending target state slots => rfl
  | closed state archive slots => cases pending

theorem before_pending : ∃ state slots,
    record.beforeAppend epoch.bound (word inventory) =
      Mandate.Challenge.Cross.History.pending (transported inventory record pending) state slots := by
  rcases record with ⟨originInputs,claim,history,within⟩
  cases history with
  | pending target state slots => exact ⟨_,_,rfl⟩
  | closed state archive slots => cases pending

omit record pending in
private theorem no_present_attempt
    (claim : Mandate.Challenge.Claim (Bound (epoch := epoch)) (Inputs inventory))
    (position : Position inventory) (actor : Bool) (n : Nat)
    (item : position.item _ _ = ⟨n,current epoch inventory.inputs,Input.signature epoch actor⟩) :
    Mandate.Challenge.readAttempt (Bound (epoch := epoch)) (Inputs inventory) claim position = none := by
  have absent : ¬ Mandate.Challenge.Withdrawal (scope := epoch.scope) (position.item _ _).before (position.item _ _).request := by
    rw [item]
    simp [Mandate.Challenge.Withdrawal,Input.signature]
  unfold Mandate.Challenge.readAttempt
  rw [dif_neg (by intro checked; exact absent checked.2.1)]

omit pending in
private theorem skip_other_signature
    (target : Mandate.Challenge.Cross.Target (Bound (epoch := epoch)) record.original (Inputs inventory))
    (state : (Mandate.Challenge.Cross.process (Bound (epoch := epoch)) record.original).GeneratedState)
    (slots : state.current.slots = [.live (Mandate.Challenge.Cross.tracked _ target)])
    (active : Mandate.Response.Active (current epoch inventory.inputs))
    (index : Fin (actors inventory).length)
    (different : (actors inventory)[index.val] ≠ target.claim.signer _ _) :
    (Mandate.Challenge.Cross.History.pending target state slots).receive (Bound (epoch := epoch)) (signing inventory active index) =
      Mandate.Challenge.Cross.History.pending target state slots := by
  have absent : Mandate.Challenge.Cross.readReconfirmation (Bound (epoch := epoch)) target (signing inventory active index) = none := by
    unfold Mandate.Challenge.Cross.readReconfirmation
    cases decoded : Mandate.Challenge.read (Bound (epoch := epoch)) (Inputs inventory) (signing inventory active index) with
    | none => rfl
    | some claim =>
      have signer : claim.signer _ _ = (actors inventory)[index.val] := by
        unfold Mandate.Challenge.Claim.signer
        rw [Mandate.Challenge.read_position _ _ _ _ decoded,signing_item]
        rfl
      dsimp only
      rw [dif_neg (by intro checked; exact different (signer.symm.trans checked.2))]
  have attempted := no_present_attempt inventory target.claim _ _ _ (signing_item inventory active index)
  simp only [Mandate.Challenge.Cross.History.receive,absent,attempted]

section Own
variable (active : Mandate.Response.Active (current epoch inventory.inputs))
  (index : Fin (actors inventory).length)
  (sameActor : (actors inventory)[index.val] = claimant inventory record)
include sameActor

theorem own_claim_exists :
    (Mandate.Challenge.read (Bound (epoch := epoch)) (Inputs inventory) (signing inventory active index)).isSome = true := by
  unfold Mandate.Challenge.read
  have signed : Mandate.Challenge.Submission (scope := epoch.scope) ((signing inventory active index).item _ _).request := by
    rw [signing_item,sameActor]
    exact ⟨claimant_has_original_standing inventory record,rfl,rfl,rfl,True.intro⟩
  have accepted : (Mandate.law base epoch.scope).Valid
      ((signing inventory active index).item _ _).before ((signing inventory active index).item _ _).request := by
    rw [signing_item,sameActor]
    exact Input.signature_valid epoch _ _ (claimant_has_original_standing inventory record)
  have activeAt : Mandate.Response.Active ((signing inventory active index).item _ _).before := by
    rw [signing_item]; exact active
  dsimp only [Mandate.Response.Active] at activeAt
  rw [dif_pos signed,dif_pos accepted,dif_pos activeAt]
  rfl

def freshClaim := (Mandate.Challenge.read (Bound (epoch := epoch)) (Inputs inventory) (signing inventory active index)).get
  (own_claim_exists inventory record active index sameActor)

theorem fresh_position : (freshClaim inventory record active index sameActor).position = signing inventory active index :=
  Mandate.Challenge.read_position _ _ _ _ (Option.some_get _).symm

theorem reconfirmation_exists :
    (Mandate.Challenge.Cross.readReconfirmation (Bound (epoch := epoch)) (transported inventory record pending)
      (signing inventory active index)).isSome = true := by
  have decoded : Mandate.Challenge.read (Bound (epoch := epoch)) (Inputs inventory) (signing inventory active index) =
      some (freshClaim inventory record active index sameActor) := (Option.some_get _).symm
  unfold Mandate.Challenge.Cross.readReconfirmation
  rw [decoded]
  dsimp only
  have later : Mandate.Challenge.Later (Bound (epoch := epoch)) (Inputs inventory)
      (transported inventory record pending).claim.position (freshClaim inventory record active index sameActor).position := by
    apply Or.inl
    rw [fresh_position]
    have ordinal := (Mandate.Challenge.Cross.replacement_same_item_and_snapshot epoch.bound inventory.inputs
      (word inventory) (Redress.target inventory record pending).claim (Redress.target_within inventory record pending)).2.2.2.1
    change (Mandate.Challenge.Cross.replacement epoch.bound inventory.inputs (word inventory)
      (Redress.target inventory record pending).claim (Redress.target_within inventory record pending)).position.ordinal < _
    rw [ordinal]
    exact Redress.target_within inventory record pending
  have signer : (freshClaim inventory record active index sameActor).signer _ _ =
      (transported inventory record pending).claim.signer _ _ := by
    unfold Mandate.Challenge.Claim.signer
    rw [fresh_position,signing_item]
    exact sameActor.trans (transported_signer inventory record pending).symm
  rw [dif_pos ⟨later,signer⟩]
  rfl

def renewed := (Mandate.Challenge.Cross.readReconfirmation (Bound (epoch := epoch)) (transported inventory record pending)
  (signing inventory active index)).get (reconfirmation_exists inventory record pending active index sameActor)

theorem renewed_position : (renewed inventory record pending active index sameActor).claim.position = signing inventory active index := by
  have decoded : Mandate.Challenge.Cross.readReconfirmation (Bound (epoch := epoch)) (transported inventory record pending)
      (signing inventory active index) = some (renewed inventory record pending active index sameActor) := (Option.some_get _).symm
  unfold Mandate.Challenge.Cross.readReconfirmation at decoded
  split at decoded
  · cases decoded
  · rename_i claim found
    split at decoded
    · have same := congrArg (fun result => result.map (fun receipt => receipt.claim.position)) decoded
      simp only [Option.map_some,Option.some.injEq] at same
      exact same.symm.trans (Mandate.Challenge.read_position _ _ _ _ found)
    · cases decoded

theorem renewed_signer : ((renewed inventory record pending active index sameActor).target _).claim.signer _ _ = claimant inventory record :=
  (renewed inventory record pending active index sameActor).signer.trans (transported_signer inventory record pending)

theorem withdrawal_exists :
    (Mandate.Challenge.readAttempt (Bound (epoch := epoch)) (Inputs inventory)
      ((renewed inventory record pending active index sameActor).target _).claim (withdrawalPosition inventory active)).isSome = true := by
  unfold Mandate.Challenge.readAttempt
  have later : Mandate.Challenge.Later (Bound (epoch := epoch)) (Inputs inventory)
      ((renewed inventory record pending active index sameActor).target _).claim.position (withdrawalPosition inventory active) := by
    apply Or.inr
    rw [show ((renewed inventory record pending active index sameActor).target _).claim =
      (renewed inventory record pending active index sameActor).claim from rfl,renewed_position]
    exact ⟨rfl,index.isLt⟩
  have signed : Mandate.Challenge.Withdrawal (scope := epoch.scope)
      ((withdrawalPosition inventory active).item _ _).before ((withdrawalPosition inventory active).item _ _).request := by
    rw [withdrawal_item]
    exact ⟨rfl,rfl,rfl,rfl,Or.inl ⟨withdrawal_actor_has_actual_standing inventory active,rfl⟩⟩
  have snapshot : ((withdrawalPosition inventory active).item _ _).before.technology =
      ((renewed inventory record pending active index sameActor).target _).claim.snapshot _ _ := by
    change _ = ((renewed inventory record pending active index sameActor).claim.position.item _ _).before.technology
    rw [renewed_position,signing_item,withdrawal_item]
  rw [dif_pos ⟨later,signed,snapshot⟩]
  rfl

end Own


omit pending in
private theorem skip_other_signatures
    (target : Mandate.Challenge.Cross.Target (Bound (epoch := epoch)) record.original (Inputs inventory))
    (state : (Mandate.Challenge.Cross.process (Bound (epoch := epoch)) record.original).GeneratedState)
    (slots : state.current.slots = [.live (Mandate.Challenge.Cross.tracked _ target)])
    (active : Mandate.Response.Active (current epoch inventory.inputs))
    (indices : List (Fin (actors inventory).length))
    (different : ∀ index ∈ indices, (actors inventory)[index.val] ≠ target.claim.signer _ _) :
    ((indices.map (signing inventory active)).foldl (Mandate.Challenge.Cross.History.receive (Bound (epoch := epoch)))
      (Mandate.Challenge.Cross.History.pending target state slots)) = Mandate.Challenge.Cross.History.pending target state slots := by
  induction indices with
  | nil => rfl
  | cons index tail ih =>
    simp only [List.map_cons,List.foldl_cons]
    rw [skip_other_signature inventory record target state slots active index (different _ (by simp))]
    exact ih (fun next member => different next (by simp [member]))

omit pending in
private theorem reaffirm_pending
    (target : Mandate.Challenge.Cross.Target (Bound (epoch := epoch)) record.original (Inputs inventory))
    (state : (Mandate.Challenge.Cross.process (Bound (epoch := epoch)) record.original).GeneratedState)
    (slots : state.current.slots = [.live (Mandate.Challenge.Cross.tracked _ target)])
    (position : Position inventory)
    (receipt : Mandate.Challenge.Cross.Reconfirmation (Bound (epoch := epoch)) target)
    (decoded : Mandate.Challenge.Cross.readReconfirmation (Bound (epoch := epoch)) target position = some receipt) :
    ∃ next nextSlots, (Mandate.Challenge.Cross.History.pending target state slots).receive (Bound (epoch := epoch)) position =
      Mandate.Challenge.Cross.History.pending (receipt.target _) next nextSlots := by
  simp only [Mandate.Challenge.Cross.History.receive,decoded]
  refine ⟨_,?_,rfl⟩
  simp [NativeResponsibilityProcess.GeneratedState.step,NativeResponsibilityProcess.Edge.target,
    Mandate.Challenge.Cross.process,Mandate.Challenge.Cross.disposition,slots,
    BoundaryDisposition.targetSlot,ActiveCarryDisposition.target,Mandate.Challenge.Cross.tracked]

omit pending in
private theorem withdrawal_status
    (target : Mandate.Challenge.Cross.Target (Bound (epoch := epoch)) record.original (Inputs inventory))
    (state : (Mandate.Challenge.Cross.process (Bound (epoch := epoch)) record.original).GeneratedState)
    (slots : state.current.slots = [.live (Mandate.Challenge.Cross.tracked _ target)])
    (active : Mandate.Response.Active (current epoch inventory.inputs))
    (available : (Mandate.Challenge.readAttempt (Bound (epoch := epoch)) (Inputs inventory)
      target.claim (withdrawalPosition inventory active)).isSome = true) :
    ((Mandate.Challenge.Cross.History.pending target state slots).receive (Bound (epoch := epoch))
      (withdrawalPosition inventory active)).isPending =
      if (Mandate.law base epoch.scope).Valid (current epoch inventory.inputs)
        (Mandate.request epoch.scope (current epoch inventory.inputs) (withdrawalActor inventory active) .revoke)
      then false else true := by
  let receipt := (Mandate.Challenge.readAttempt (Bound (epoch := epoch)) (Inputs inventory)
    target.claim (withdrawalPosition inventory active)).get available
  have decoded : Mandate.Challenge.readAttempt (Bound (epoch := epoch)) (Inputs inventory)
      target.claim (withdrawalPosition inventory active) = some receipt := (Option.some_get _).symm
  have receiptPosition : receipt.position = withdrawalPosition inventory active := by
    unfold Mandate.Challenge.readAttempt at decoded
    split at decoded
    · have same := congrArg (fun result => result.map (fun receipt => receipt.position)) decoded
      simpa only [Option.map_some,Option.some.injEq] using same.symm
    · cases decoded
  have absent : Mandate.Challenge.Cross.readReconfirmation (Bound (epoch := epoch)) target (withdrawalPosition inventory active) = none := by
    have unsigned : ¬ Mandate.Challenge.Submission (scope := epoch.scope) ((withdrawalPosition inventory active).item _ _).request := by
      rw [withdrawal_item]
      simp [Mandate.Challenge.Submission,Mandate.request]
    simp only [Mandate.Challenge.Cross.readReconfirmation,Mandate.Challenge.read,dif_neg unsigned]
  have status : ((Mandate.Challenge.Cross.History.pending target state slots).receive (Bound (epoch := epoch))
      (withdrawalPosition inventory active)).isPending =
      if (Mandate.law base epoch.scope).Valid (receipt.position.item _ _).before (receipt.position.item _ _).request
      then false else true := by
    simp only [Mandate.Challenge.Cross.History.receive,absent,decoded]
    split <;> rfl
  rw [receiptPosition,withdrawal_item] at status
  exact status

omit record pending in
theorem actors_have_no_duplicate_signatures : (actors inventory).Nodup := by
  exact List.Nodup.filter _ (by decide : ([false,true] : List Bool).Nodup)

include pending

private theorem native_status_at
    (active : Mandate.Response.Active (current epoch inventory.inputs))
    (own : Fin (actors inventory).length)
    (sameActor : (actors inventory)[own.val] = claimant inventory record) :
    (original inventory record).history.isPending =
      if (Mandate.law base epoch.scope).Valid (current epoch inventory.inputs)
        (Mandate.request epoch.scope (current epoch inventory.inputs) (withdrawalActor inventory active) .revoke)
      then false else true := by
  obtain ⟨frontIndices,backIndices,split⟩ := List.mem_iff_append.mp (List.mem_finRange own)
  have distinct := List.nodup_finRange (actors inventory).length
  rw [split] at distinct
  have notBefore : own ∉ frontIndices := by
    intro member
    exact (List.nodup_append.mp distinct).2.2 _ member _ (by simp) rfl
  have notAfter : own ∉ backIndices := (List.nodup_cons.mp (List.nodup_append.mp distinct).2.1).1
  have unequal (indices : List (Fin (actors inventory).length)) (absent : own ∉ indices) :
      ∀ index ∈ indices, (actors inventory)[index.val] ≠ claimant inventory record := by
    intro index member equal
    have sameIndex : index = own := Fin.ext ((List.getElem_inj (actors_have_no_duplicate_signatures inventory)).mp (equal.trans sameActor.symm))
    exact absent (sameIndex ▸ member)
  obtain ⟨state,slots,saved⟩ := before_pending inventory record pending
  change (record.afterAppend epoch.bound (word inventory)).isPending = _
  rw [Mandate.Challenge.Cross.Resident.afterAppend,emitted_positions inventory active,split]
  simp only [List.map_append,List.map_cons,List.foldl_append,List.foldl_cons,List.foldl_nil]
  rw [saved]
  have prefixDifferent : ∀ index ∈ frontIndices, (actors inventory)[index.val] ≠ (transported inventory record pending).claim.signer _ _ := by
    rw [transported_signer]
    exact unequal frontIndices notBefore
  rw [skip_other_signatures inventory record _ state slots active frontIndices prefixDifferent]
  have decoded : Mandate.Challenge.Cross.readReconfirmation (Bound (epoch := epoch)) (transported inventory record pending)
      (signing inventory active own) = some (renewed inventory record pending active own sameActor) := (Option.some_get _).symm
  obtain ⟨next,nextSlots,affirmed⟩ := reaffirm_pending inventory record _ state slots _ _ decoded
  rw [affirmed]
  have suffixDifferent : ∀ index ∈ backIndices, (actors inventory)[index.val] ≠
      ((renewed inventory record pending active own sameActor).target _).claim.signer _ _ := by
    rw [renewed_signer]
    exact unequal backIndices notAfter
  rw [skip_other_signatures inventory record _ next nextSlots active backIndices suffixDifferent]
  exact withdrawal_status inventory record _ next nextSlots active (withdrawal_exists inventory record pending active own sameActor)

theorem every_pending_original_has_its_actual_native_disposition
    (member : record ∈ inventory.objections)
    (active : Mandate.Response.Active (current epoch inventory.inputs)) :
    (original inventory record).history.isPending =
      if (Mandate.law base epoch.scope).Valid (current epoch inventory.inputs)
        (Mandate.request epoch.scope (current epoch inventory.inputs) (withdrawalActor inventory active) .revoke)
      then false else true := by
  have included := every_pending_original_is_covered inventory record member pending
  let own : Fin (actors inventory).length := ⟨(actors inventory).idxOf (claimant inventory record),List.idxOf_lt_length_of_mem included⟩
  exact native_status_at inventory record pending active own (List.getElem_idxOf own.isLt)


omit pending in
theorem archived_original_preserves_its_entire_native_state (archived : record.history.isPending = false) :
    (original inventory record).history.state = record.history.state := by
  rcases record with ⟨originInputs,claim,history,within⟩
  cases history with
  | pending target state slots => cases archived
  | closed state archive slots =>
    change ((Mandate.Challenge.positionsAt (Bound (epoch := epoch)) (Inputs inventory) (inventory.inputs.length+2)).foldl
      (Mandate.Challenge.Cross.History.receive (Bound (epoch := epoch))) (.closed state archive slots)).state = state
    generalize Mandate.Challenge.positionsAt (Bound (epoch := epoch)) (Inputs inventory) (inventory.inputs.length+2) = positions
    induction positions with
    | nil => rfl
    | cons position rest ih => exact ih

omit pending in
theorem empty_word_preserves_the_complete_original_native_state (empty : word inventory = []) :
    (original inventory record).history.state = record.history.state := by
  have noItems : items inventory = [] := by
    change (Mandate.law base epoch.scope).rawItems (actual inventory).before (actual inventory).submitted = []
    rw [(actual_word_and_saved_cut inventory).1,(actual_word_and_saved_cut inventory).2,empty]
    rfl
  have noPositions : Mandate.Challenge.positionsAt (Bound (epoch := epoch)) (Inputs inventory) (inventory.inputs.length+2) = [] := by
    apply List.eq_nil_iff_length_eq_zero.mpr
    simp only [Mandate.Challenge.positionsAt,List.length_map,List.length_finRange]
    change (items inventory).length = 0
    rw [noItems]
    rfl
  change (record.afterAppend epoch.bound (word inventory)).state = _
  rw [Mandate.Challenge.Cross.Resident.afterAppend,noPositions]
  exact record.old_entire_state_is_the_actual_continuation_start epoch.bound (word inventory)

omit record pending in
theorem accepted_shared_attempt_is_the_actual_withdrawal
    (active : Mandate.Response.Active (current epoch inventory.inputs))
    (paid : (Mandate.law base epoch.scope).Valid (current epoch inventory.inputs)
      (Mandate.request epoch.scope (current epoch inventory.inputs) (withdrawalActor inventory active) .revoke)) :
    (actual inventory).after.technology.holder = none ∧
    (actual inventory).after.technology.offered = none ∧
    (actual inventory).after.technology.version = (current epoch inventory.inputs).technology.version+1 := by
  rw [(actual inventory).after_exact,(actual_word_and_saved_cut inventory).1,(actual_word_and_saved_cut inventory).2]
  change ((Mandate.law base epoch.scope).next (current epoch inventory.inputs) (word inventory)).technology.holder = none ∧
    ((Mandate.law base epoch.scope).next (current epoch inventory.inputs) (word inventory)).technology.offered = none ∧
    ((Mandate.law base epoch.scope).next (current epoch inventory.inputs) (word inventory)).technology.version = _
  rw [active_word inventory active]
  simp only [RawLaw.next,RawLaw.execute_append]
  rw [show signatures inventory = (actors inventory).map (Input.signature epoch) from rfl,
    signature_prefix_preserves_current]
  simp only [RawLaw.execute,RawLaw.step,if_pos paid]
  simp only [RawLaw.paidStep,Mandate.request,Mandate.advance,and_self]

omit record pending in
inductive Disposition where
  | private inactive (absent : ¬ Mandate.Response.Active (current epoch inventory.inputs))
      (empty : word inventory = [])
      (preserved : ∀ record : Record inventory, (original inventory record).history.state = record.history.state)
  | private fulfilled (active : Mandate.Response.Active (current epoch inventory.inputs))
      (paid : (Mandate.law base epoch.scope).Valid (current epoch inventory.inputs)
        (Mandate.request epoch.scope (current epoch inventory.inputs) (withdrawalActor inventory active) .revoke))
      (closed : ∀ record ∈ inventory.objections, record.history.isPending = true → (original inventory record).history.isPending = false)
      (withdrawn : (actual inventory).after.technology.holder = none ∧ (actual inventory).after.technology.offered = none ∧
        (actual inventory).after.technology.version = (current epoch inventory.inputs).technology.version+1)
  | private deferred (active : Mandate.Response.Active (current epoch inventory.inputs))
      (refused : ¬ (Mandate.law base epoch.scope).Valid (current epoch inventory.inputs)
        (Mandate.request epoch.scope (current epoch inventory.inputs) (withdrawalActor inventory active) .revoke))
      (coverage : ∀ actor ∈ Delegation.members epoch.scope.task,
        ¬ (Mandate.law base epoch.scope).Valid (current epoch inventory.inputs)
          (Mandate.request epoch.scope (current epoch inventory.inputs) actor .revoke))
      (retained : ∀ record ∈ inventory.objections, record.history.isPending = true → (original inventory record).history.isPending = true)

omit record pending in
def produce : Disposition inventory := by
  by_cases active : Mandate.Response.Active (current epoch inventory.inputs)
  · by_cases paid : (Mandate.law base epoch.scope).Valid (current epoch inventory.inputs)
      (Mandate.request epoch.scope (current epoch inventory.inputs) (withdrawalActor inventory active) .revoke)
    · exact .fulfilled active paid (fun record member live => by
        rw [every_pending_original_has_its_actual_native_disposition inventory record live member active,if_pos paid])
        (accepted_shared_attempt_is_the_actual_withdrawal inventory active paid)
    · exact .deferred active paid
        (Redress.an_actual_refused_attempt_covers_exactly_current_member_revocations inventory active paid)
        (fun record member live => by
          rw [every_pending_original_has_its_actual_native_disposition inventory record live member active,if_neg paid])
  · have empty : word inventory = [] := by simp [word,active]
    exact .inactive active empty (fun record => empty_word_preserves_the_complete_original_native_state inventory record empty)

omit record pending in
inductive Kind where
  | inactive | fulfilled | deferred
  deriving DecidableEq

omit record pending in
def Disposition.kind : Disposition inventory → Kind
  | .inactive .. => .inactive | .fulfilled .. => .fulfilled | .deferred .. => .deferred

omit record pending in
theorem all_originals_and_only_actual_newborns_are_in_the_actual_inventory :
    (after inventory).objections = inventory.objections.map (original inventory) ++
      Mandate.Challenge.Cross.newborn epoch.bound (word inventory) := rfl

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Challenge.Redress.Shared
