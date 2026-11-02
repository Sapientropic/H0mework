import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Challenge

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Challenge.Redress
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
open Institutions.Capitalism.Universal.Source.ProgrammeFace
noncomputable section
variable {epoch : Epoch} (inventory : Inventory epoch)
abbrev Bound := Mandate.Challenge.fromHistory epoch.bound
abbrev Record := Mandate.Challenge.Cross.Resident epoch.bound inventory.inputs

def claimant (record : Record inventory) : Bool :=
  match record.history with
  | .pending target _ _ => target.claim.signer _ _
  | .closed .. => record.original.signer _ _

theorem claimant_has_original_standing (record : Record inventory) :
    claimant inventory record ∈ Delegation.members epoch.scope.task := by
  cases history : record.history with
  | pending target state slots =>
    simpa only [claimant,history] using target.claim.signed.1
  | closed state archive slots =>
    simpa only [claimant,history] using record.original.signed.1

def decision := Mandate.Response.produce base epoch.scope (current epoch inventory.inputs)

/-- The original claimant renews its own snapshot before withdrawal is tried.
The source checks the withdrawal under this same actual current. -/
def word (record : Record inventory) : List Action :=
  if record.history.isPending && decide (Mandate.Response.Active (current epoch inventory.inputs)) then
    Input.signature epoch (claimant inventory record) :: (decision inventory).word
  else []

def after (record : Record inventory) := World.submit inventory (word inventory record)
def actual (record : Record inventory) := World.actual inventory (word inventory record)
def original (record : Record inventory) := record.advance epoch.bound (word inventory record)
def native (record : Record inventory) := record.responseRun epoch.bound (word inventory record)

theorem actual_word_and_saved_cut (record : Record inventory) :
    (actual inventory record).submitted = word inventory record ∧
    (actual inventory record).before = current epoch inventory.inputs := World.actual_word_and_cut _ _

theorem signature_preserves_the_entire_current (record : Record inventory) :
    (Mandate.law base epoch.scope).step (current epoch inventory.inputs)
      (Input.signature epoch (claimant inventory record)) = current epoch inventory.inputs := by
  rw [RawLaw.step, if_pos (Input.signature_valid epoch _ _ (claimant_has_original_standing inventory record))]
  apply RawCurrent.ext <;> simp [RawLaw.paidStep, RawLaw.debit, RawLaw.credit, RawLaw.nextClaims, Input.signature]

theorem a_pending_active_original_generates_its_own_actual_attempt (record : Record inventory)
    (pending : record.history.isPending = true)
    (active : Mandate.Response.Active (current epoch inventory.inputs)) :
    ∃ actor ∈ Delegation.members epoch.scope.task,
      word inventory record = [Input.signature epoch (claimant inventory record),
        Mandate.request epoch.scope (current epoch inventory.inputs) actor .revoke] := by
  obtain ⟨actor, member, emitted⟩ := (decision inventory).active_emits_an_actual_attempt active
  refine ⟨actor,member,?_⟩
  simp only [word,pending,decide_eq_true active,Bool.and_self,ite_true,emitted]

def withdrawalActor (_active : Mandate.Response.Active (current epoch inventory.inputs)) : Bool :=
  (((decision inventory).word.head?).map Institutions.Capitalism.Universal.Source.Program.Request.signer).getD (Input.sponsor epoch)

theorem withdrawal_actor_has_actual_standing (active : Mandate.Response.Active (current epoch inventory.inputs)) :
    withdrawalActor inventory active ∈ Delegation.members epoch.scope.task := by
  obtain ⟨actor,member,emitted⟩ := (decision inventory).active_emits_an_actual_attempt active
  simpa only [withdrawalActor,emitted,List.head?_cons,Option.map_some,Option.getD_some,Mandate.request] using member

theorem active_decision_word (active : Mandate.Response.Active (current epoch inventory.inputs)) :
    (decision inventory).word = [Mandate.request epoch.scope (current epoch inventory.inputs)
      (withdrawalActor inventory active) .revoke] := by
  obtain ⟨actor,member,emitted⟩ := (decision inventory).active_emits_an_actual_attempt active
  simp only [withdrawalActor,emitted,List.head?_cons,Option.map_some,Option.getD_some,Mandate.request]

theorem pending_active_word (record : Record inventory)
    (pending : record.history.isPending = true)
    (active : Mandate.Response.Active (current epoch inventory.inputs)) :
    word inventory record = [Input.signature epoch (claimant inventory record),
      Mandate.request epoch.scope (current epoch inventory.inputs) (withdrawalActor inventory active) .revoke] := by
  simp only [word,pending,decide_eq_true active,Bool.and_self,ite_true,active_decision_word inventory active]

section Active
variable (record : Record inventory) (pending : record.history.isPending = true)
  (active : Mandate.Response.Active (current epoch inventory.inputs))
include pending

def items := Registered.traceItems
  (Mandate.Challenge.I (Bound (epoch := epoch)) (Mandate.Challenge.Cross.nextInputs inventory.inputs (word inventory record)))
  (ProgrammeHistory.visitAt (Mandate.Challenge.I (Bound (epoch := epoch)) (Mandate.Challenge.Cross.nextInputs inventory.inputs (word inventory record)))
    (inventory.inputs.length+2)).current

theorem items_exact : items inventory record =
    [⟨0,current epoch inventory.inputs,Input.signature epoch (claimant inventory record)⟩,
     ⟨1,current epoch inventory.inputs,Mandate.request epoch.scope (current epoch inventory.inputs)
       (withdrawalActor inventory active) .revoke⟩] := by
  change (Mandate.law base epoch.scope).rawItems (actual inventory record).before
    (actual inventory record).submitted = _
  rw [(actual_word_and_saved_cut inventory record).1,(actual_word_and_saved_cut inventory record).2,
    pending_active_word inventory record pending active]
  simp only [RawLaw.rawItems,RawLaw.execute,signature_preserves_the_entire_current]

def position (index : Fin 2) : Mandate.Challenge.Position (Bound (epoch := epoch)) (Mandate.Challenge.Cross.nextInputs inventory.inputs (word inventory record)) :=
  ⟨inventory.inputs.length+2,⟨index.val,by
    change index.val < (items inventory record).length
    rw [items_exact inventory record pending active]
    exact index.isLt⟩⟩

def first := position inventory record pending active ⟨0,by decide⟩
def second := position inventory record pending active ⟨1,by decide⟩

theorem first_item : (first inventory record pending active).item _ _ =
    ⟨0,current epoch inventory.inputs,Input.signature epoch (claimant inventory record)⟩ := by
  have same := congrArg (fun items => items[0]?) (items_exact inventory record pending active)
  have bound : 0 < (items inventory record).length := (first inventory record pending active).index.isLt
  rw [List.getElem?_eq_getElem bound] at same
  exact Option.some.inj same

theorem second_item : (second inventory record pending active).item _ _ =
    ⟨1,current epoch inventory.inputs,Mandate.request epoch.scope (current epoch inventory.inputs)
      (withdrawalActor inventory active) .revoke⟩ := by
  have same := congrArg (fun items => items[1]?) (items_exact inventory record pending active)
  have bound : 1 < (items inventory record).length := (second inventory record pending active).index.isLt
  rw [List.getElem?_eq_getElem bound] at same
  exact Option.some.inj same

def targetAt {originInputs : List (List Action)}
    {claim : Mandate.Challenge.Claim (Bound (epoch := epoch)) originInputs}
    (history : Mandate.Challenge.Cross.History (Bound (epoch := epoch)) claim inventory.inputs) :
    history.isPending = true → Mandate.Challenge.Cross.Target (Bound (epoch := epoch)) claim inventory.inputs :=
  match history with
  | .pending target _ _ => fun _ => target
  | .closed .. => fun impossible => Bool.noConfusion impossible

def target := targetAt inventory record.history pending

theorem target_within : (target inventory record pending).claim.position.ordinal < inventory.inputs.length+2 := by
  rcases record with ⟨originInputs,claim,history,within⟩
  cases history with
  | pending target state slots => exact within
  | closed state archive slots => cases pending

def transported := Mandate.Challenge.Cross.transportTarget epoch.bound (word inventory record)
  (target inventory record pending) (target_within inventory record pending)

theorem transported_signer : (transported inventory record pending).claim.signer _ _ = claimant inventory record := by
  have same := (Mandate.Challenge.Cross.replacement_same_item_and_snapshot epoch.bound inventory.inputs
    (word inventory record) (target inventory record pending).claim (target_within inventory record pending)).2.2.1
  refine same.trans ?_
  rcases record with ⟨originInputs,claim,history,within⟩
  cases history with
  | pending target state slots => rfl
  | closed state archive slots => cases pending

theorem first_claim_exists :
    (Mandate.Challenge.read (Bound (epoch := epoch)) (Mandate.Challenge.Cross.nextInputs inventory.inputs (word inventory record))
      (first inventory record pending active)).isSome = true := by
  unfold Mandate.Challenge.read
  have signed : Mandate.Challenge.Submission (scope := epoch.scope)
      ((first inventory record pending active).item _ _).request := by
    rw [first_item inventory record pending active]
    exact ⟨claimant_has_original_standing inventory record,rfl,rfl,rfl,True.intro⟩
  have accepted : (Mandate.law base epoch.scope).Valid
      ((first inventory record pending active).item _ _).before
      ((first inventory record pending active).item _ _).request := by
    rw [first_item inventory record pending active]
    exact Input.signature_valid epoch _ _ (claimant_has_original_standing inventory record)
  have activeAt : Mandate.Response.Active ((first inventory record pending active).item _ _).before := by
    rw [first_item inventory record pending active]; exact active
  dsimp only [Mandate.Response.Active] at activeAt
  rw [dif_pos signed,dif_pos accepted,dif_pos activeAt]
  rfl

def freshClaim := (Mandate.Challenge.read (Bound (epoch := epoch)) (Mandate.Challenge.Cross.nextInputs inventory.inputs (word inventory record))
  (first inventory record pending active)).get (first_claim_exists inventory record pending active)

theorem fresh_claim_position : (freshClaim inventory record pending active).position = first inventory record pending active :=
  Mandate.Challenge.read_position _ _ _ _ (Option.some_get _).symm

theorem actual_reconfirmation_exists :
    (Mandate.Challenge.Cross.readReconfirmation (Bound (epoch := epoch)) (transported inventory record pending)
      (first inventory record pending active)).isSome = true := by
  have decoded : Mandate.Challenge.read (Bound (epoch := epoch)) (Mandate.Challenge.Cross.nextInputs inventory.inputs (word inventory record))
      (first inventory record pending active) = some (freshClaim inventory record pending active) := (Option.some_get _).symm
  unfold Mandate.Challenge.Cross.readReconfirmation
  rw [decoded]
  dsimp only
  have later : Mandate.Challenge.Later (Bound (epoch := epoch)) (Mandate.Challenge.Cross.nextInputs inventory.inputs (word inventory record))
      (transported inventory record pending).claim.position (freshClaim inventory record pending active).position := by
    apply Or.inl
    rw [fresh_claim_position]
    have same := (Mandate.Challenge.Cross.replacement_same_item_and_snapshot epoch.bound inventory.inputs
      (word inventory record) (target inventory record pending).claim (target_within inventory record pending)).2.2.2.1
    change (Mandate.Challenge.Cross.replacement epoch.bound inventory.inputs (word inventory record)
      (target inventory record pending).claim (target_within inventory record pending)).position.ordinal < _
    rw [same]
    exact target_within inventory record pending
  have signer : (freshClaim inventory record pending active).signer _ _ =
      (transported inventory record pending).claim.signer _ _ := by
    unfold Mandate.Challenge.Claim.signer
    rw [fresh_claim_position,first_item]
    exact (transported_signer inventory record pending).symm
  rw [dif_pos ⟨later,signer⟩]
  rfl
def renewed := (Mandate.Challenge.Cross.readReconfirmation (Bound (epoch := epoch))
  (transported inventory record pending) (first inventory record pending active)).get
    (actual_reconfirmation_exists inventory record pending active)

theorem renewed_claim_position : (renewed inventory record pending active).claim.position = first inventory record pending active := by
  have decoded : Mandate.Challenge.Cross.readReconfirmation (Bound (epoch := epoch))
      (transported inventory record pending) (first inventory record pending active) =
        some (renewed inventory record pending active) := (Option.some_get _).symm
  unfold Mandate.Challenge.Cross.readReconfirmation at decoded
  split at decoded
  · cases decoded
  · rename_i claim found
    split at decoded
    · have same := congrArg (fun result => result.map (fun receipt => receipt.claim.position)) decoded
      simp only [Option.map_some,Option.some.injEq] at same
      exact same.symm.trans (Mandate.Challenge.read_position _ _ _ _ found)
    · cases decoded

theorem renewed_snapshot : ((renewed inventory record pending active).target _).snapshot _ =
    (current epoch inventory.inputs).technology := by
  change ((renewed inventory record pending active).claim.position.item _ _).before.technology = _
  rw [renewed_claim_position,first_item]

theorem actual_withdrawal_receipt_exists :
    (Mandate.Challenge.readAttempt (Bound (epoch := epoch)) (Mandate.Challenge.Cross.nextInputs inventory.inputs (word inventory record))
      ((renewed inventory record pending active).target _).claim (second inventory record pending active)).isSome = true := by
  unfold Mandate.Challenge.readAttempt
  have later : Mandate.Challenge.Later (Bound (epoch := epoch)) (Mandate.Challenge.Cross.nextInputs inventory.inputs (word inventory record))
      ((renewed inventory record pending active).target _).claim.position (second inventory record pending active) := by
    apply Or.inr
    rw [show ((renewed inventory record pending active).target _).claim = (renewed inventory record pending active).claim from rfl,
      renewed_claim_position]
    exact ⟨rfl,by change 0 < 1; decide⟩
  have signed : Mandate.Challenge.Withdrawal (scope := epoch.scope)
      ((second inventory record pending active).item _ _).before
      ((second inventory record pending active).item _ _).request := by
    rw [second_item]
    exact ⟨rfl,rfl,rfl,rfl,Or.inl ⟨withdrawal_actor_has_actual_standing inventory active,rfl⟩⟩
  have snapshot : ((second inventory record pending active).item _ _).before.technology =
      ((renewed inventory record pending active).target _).claim.snapshot _ _ := by
    rw [second_item]
    exact (renewed_snapshot inventory record pending active).symm
  rw [dif_pos ⟨later,signed,snapshot⟩]
  rfl

def withdrawal := (Mandate.Challenge.readAttempt (Bound (epoch := epoch)) (Mandate.Challenge.Cross.nextInputs inventory.inputs (word inventory record))
  ((renewed inventory record pending active).target _).claim (second inventory record pending active)).get
    (actual_withdrawal_receipt_exists inventory record pending active)

theorem withdrawal_position : (withdrawal inventory record pending active).position = second inventory record pending active := by
  have decoded : Mandate.Challenge.readAttempt (Bound (epoch := epoch)) (Mandate.Challenge.Cross.nextInputs inventory.inputs (word inventory record))
      ((renewed inventory record pending active).target _).claim (second inventory record pending active) =
        some (withdrawal inventory record pending active) := (Option.some_get _).symm
  unfold Mandate.Challenge.readAttempt at decoded
  split at decoded
  · have same := congrArg (fun result => result.map (fun receipt => receipt.position)) decoded
    simpa only [Option.map_some,Option.some.injEq] using same.symm
  · cases decoded

theorem second_cannot_reconfirm :
    Mandate.Challenge.Cross.readReconfirmation (Bound (epoch := epoch))
      ((renewed inventory record pending active).target _) (second inventory record pending active) = none := by
  have absent : ¬ Mandate.Challenge.Submission (scope := epoch.scope)
      ((second inventory record pending active).item _ _).request := by
    rw [second_item]
    simp [Mandate.Challenge.Submission,Mandate.request]
  simp only [Mandate.Challenge.Cross.readReconfirmation,Mandate.Challenge.read,dif_neg absent]

theorem emitted_positions :
    Mandate.Challenge.positionsAt (Bound (epoch := epoch)) (Mandate.Challenge.Cross.nextInputs inventory.inputs (word inventory record)) (inventory.inputs.length+2) =
      [first inventory record pending active,second inventory record pending active] := by
  apply List.ext_getElem
  · simp only [Mandate.Challenge.positionsAt,List.length_map,List.length_finRange]
    change (items inventory record).length = 2
    rw [items_exact inventory record pending active]
    rfl
  · intro index left right
    have less : index < 2 := by simpa using right
    have values : index = 0 ∨ index = 1 := by omega
    rcases values with rfl | rfl <;>
      simp [Mandate.Challenge.positionsAt,first,second,position,List.getElem_finRange]

end Active

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Challenge.Redress
