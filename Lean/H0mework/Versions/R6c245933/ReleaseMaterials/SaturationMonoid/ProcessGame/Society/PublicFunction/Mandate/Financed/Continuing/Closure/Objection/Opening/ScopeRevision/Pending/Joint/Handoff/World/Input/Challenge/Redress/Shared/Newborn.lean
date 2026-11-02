import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Challenge.Redress.Shared.Native

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Challenge.Redress.Shared.Newborn
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
noncomputable section
variable {epoch : Epoch} (inventory : Inventory epoch)

abbrev Claim := Mandate.Challenge.Claim (Bound (epoch := epoch)) (Inputs inventory)
abbrev Position := Mandate.Challenge.Position (Bound (epoch := epoch)) (Inputs inventory)

private theorem initial_receive_not_later (claim : Claim inventory) (position : Position inventory)
    (notLater : ¬ Mandate.Challenge.Later (Bound (epoch := epoch)) (Inputs inventory) claim.position position) :
    (Mandate.Challenge.History.initial (Bound (epoch := epoch)) (Inputs inventory) claim).receive _ _ position =
      Mandate.Challenge.History.initial (Bound (epoch := epoch)) (Inputs inventory) claim := by
  have absent : Mandate.Challenge.readReconfirmation (Bound (epoch := epoch)) (Inputs inventory) claim position = none := by
    unfold Mandate.Challenge.readReconfirmation
    cases decoded : Mandate.Challenge.read (Bound (epoch := epoch)) (Inputs inventory) position with
    | none => rfl
    | some fresh =>
      dsimp only
      rw [dif_neg (by
        intro checked
        rw [Mandate.Challenge.read_position _ _ _ _ decoded] at checked
        exact notLater checked.1)]
  have noAttempt : Mandate.Challenge.readAttempt (Bound (epoch := epoch)) (Inputs inventory) claim position = none := by
    unfold Mandate.Challenge.readAttempt
    rw [dif_neg (by intro checked; exact notLater checked.1)]
  simp only [Mandate.Challenge.History.initial,Mandate.Challenge.History.receive,absent,
    Mandate.Challenge.Target.claim,noAttempt]

private theorem fold_initial (claim : Claim inventory) (positions : List (Position inventory))
    (unchanged : ∀ position ∈ positions,
      (Mandate.Challenge.History.initial (Bound (epoch := epoch)) (Inputs inventory) claim).receive _ _ position =
        Mandate.Challenge.History.initial (Bound (epoch := epoch)) (Inputs inventory) claim) :
    positions.foldl (Mandate.Challenge.History.receive (Bound (epoch := epoch)) (Inputs inventory))
      (Mandate.Challenge.History.initial (Bound (epoch := epoch)) (Inputs inventory) claim) =
        Mandate.Challenge.History.initial (Bound (epoch := epoch)) (Inputs inventory) claim := by
  induction positions with
  | nil => rfl
  | cons position rest ih =>
    rw [List.foldl_cons,unchanged _ (by simp)]
    exact ih (fun next member => unchanged next (by simp [member]))

private theorem through_before_birth (claim : Claim inventory) (count : Nat) (before : count ≤ claim.position.ordinal) :
    Mandate.Challenge.through (Bound (epoch := epoch)) (Inputs inventory) claim count =
      Mandate.Challenge.History.initial (Bound (epoch := epoch)) (Inputs inventory) claim := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [Mandate.Challenge.through,ih (by omega)]
    apply fold_initial
    intro position member
    apply initial_receive_not_later
    obtain ⟨index,_,same⟩ := List.mem_map.mp member
    cases same
    intro later
    change claim.position.ordinal < count ∨ (claim.position.ordinal = count ∧ _) at later
    omega

variable (active : Mandate.Response.Active (current epoch inventory.inputs))

private theorem withdrawal_cannot_birth : Mandate.Challenge.read (Bound (epoch := epoch)) (Inputs inventory)
    (withdrawalPosition inventory active) = none := by
  have unsigned : ¬ Mandate.Challenge.Submission (scope := epoch.scope)
      ((withdrawalPosition inventory active).item _ _).request := by
    rw [withdrawal_item]
    simp [Mandate.Challenge.Submission,Mandate.request]
  simp only [Mandate.Challenge.read,dif_neg unsigned]

theorem every_actual_new_claim_has_its_own_signature_position (claim : Claim inventory)
    (born : claim ∈ Mandate.Challenge.claimsAt (Bound (epoch := epoch)) (Inputs inventory) (inventory.inputs.length+2)) :
    ∃ index : Fin (actors inventory).length, claim.position = signing inventory active index := by
  obtain ⟨position,listed,decoded⟩ := List.mem_filterMap.mp born
  rw [emitted_positions inventory active] at listed
  rcases List.mem_append.mp listed with signed | withdrawn
  · obtain ⟨index,_,same⟩ := List.mem_map.mp signed
    exact ⟨index,(Mandate.Challenge.read_position _ _ _ _ decoded).trans same.symm⟩
  · cases List.mem_singleton.mp withdrawn
    rw [withdrawal_cannot_birth inventory active] at decoded
    cases decoded

private theorem other_signature_is_noop (claim : Claim inventory)
    (own : Fin (actors inventory).length) (actual : claim.position = signing inventory active own)
    (index : Fin (actors inventory).length) :
    (Mandate.Challenge.History.initial (Bound (epoch := epoch)) (Inputs inventory) claim).receive _ _ (signing inventory active index) =
      Mandate.Challenge.History.initial (Bound (epoch := epoch)) (Inputs inventory) claim := by
  by_cases same : index = own
  · subst index
    apply initial_receive_not_later
    rw [actual]
    simp [Mandate.Challenge.Later]
  · have different : (actors inventory)[index.val] ≠ claim.signer _ _ := by
      intro equal
      have ownSigner : claim.signer _ _ = (actors inventory)[own.val] := by
        unfold Mandate.Challenge.Claim.signer
        rw [actual,signing_item]
        rfl
      exact same (Fin.ext ((List.getElem_inj (actors_have_no_duplicate_signatures inventory)).mp (equal.trans ownSigner)))
    have absent : Mandate.Challenge.readReconfirmation (Bound (epoch := epoch)) (Inputs inventory) claim (signing inventory active index) = none := by
      unfold Mandate.Challenge.readReconfirmation
      cases decoded : Mandate.Challenge.read (Bound (epoch := epoch)) (Inputs inventory) (signing inventory active index) with
      | none => rfl
      | some fresh =>
        have signer : fresh.signer _ _ = (actors inventory)[index.val] := by
          unfold Mandate.Challenge.Claim.signer
          rw [Mandate.Challenge.read_position _ _ _ _ decoded,signing_item]
          rfl
        dsimp only
        rw [dif_neg (by intro checked; exact different (signer.symm.trans checked.2))]
    have noAttempt : Mandate.Challenge.readAttempt (Bound (epoch := epoch)) (Inputs inventory) claim (signing inventory active index) = none := by
      have unsigned : ¬ Mandate.Challenge.Withdrawal (scope := epoch.scope)
          ((signing inventory active index).item _ _).before ((signing inventory active index).item _ _).request := by
        rw [signing_item]
        simp [Mandate.Challenge.Withdrawal,Input.signature]
      unfold Mandate.Challenge.readAttempt
      rw [dif_neg (by intro checked; exact unsigned checked.2.1)]
    simp only [Mandate.Challenge.History.initial,Mandate.Challenge.History.receive,absent,
      Mandate.Challenge.Target.claim,noAttempt]

theorem actual_new_history_is_its_birth_then_the_same_withdrawal (claim : Claim inventory)
    (born : claim ∈ Mandate.Challenge.claimsAt (Bound (epoch := epoch)) (Inputs inventory) (inventory.inputs.length+2)) :
    Mandate.Challenge.through (Bound (epoch := epoch)) (Inputs inventory) claim ((Inputs inventory).length+2) =
      (Mandate.Challenge.History.initial (Bound (epoch := epoch)) (Inputs inventory) claim).receive _ _
        (withdrawalPosition inventory active) := by
  obtain ⟨own,actual⟩ := every_actual_new_claim_has_its_own_signature_position inventory active claim born
  have ordinal : claim.position.ordinal = inventory.inputs.length+2 := by rw [actual]; rfl
  have count : (Inputs inventory).length+2 = (inventory.inputs.length+2)+1 := by
    simp [Inputs,Mandate.Challenge.Cross.nextInputs]
  rw [count,Mandate.Challenge.through,through_before_birth inventory claim _ (by omega),emitted_positions inventory active,
    List.foldl_append]
  have signatures : ((List.finRange (actors inventory).length).map (signing inventory active)).foldl
      (Mandate.Challenge.History.receive (Bound (epoch := epoch)) (Inputs inventory))
      (Mandate.Challenge.History.initial (Bound (epoch := epoch)) (Inputs inventory) claim) =
        Mandate.Challenge.History.initial (Bound (epoch := epoch)) (Inputs inventory) claim := by
    apply fold_initial
    intro position member
    obtain ⟨index,_,same⟩ := List.mem_map.mp member
    cases same
    exact other_signature_is_noop inventory active claim own actual index
  rw [signatures]
  rfl


private theorem new_claim_attempt_exists (claim : Claim inventory)
    (born : claim ∈ Mandate.Challenge.claimsAt (Bound (epoch := epoch)) (Inputs inventory) (inventory.inputs.length+2)) :
    (Mandate.Challenge.readAttempt (Bound (epoch := epoch)) (Inputs inventory) claim (withdrawalPosition inventory active)).isSome = true := by
  obtain ⟨own,actual⟩ := every_actual_new_claim_has_its_own_signature_position inventory active claim born
  have later : Mandate.Challenge.Later (Bound (epoch := epoch)) (Inputs inventory) claim.position (withdrawalPosition inventory active) := by
    rw [actual]
    exact Or.inr ⟨rfl,own.isLt⟩
  have signed : Mandate.Challenge.Withdrawal (scope := epoch.scope)
      ((withdrawalPosition inventory active).item _ _).before ((withdrawalPosition inventory active).item _ _).request := by
    rw [withdrawal_item]
    exact ⟨rfl,rfl,rfl,rfl,Or.inl ⟨withdrawal_actor_has_actual_standing inventory active,rfl⟩⟩
  have snapshot : ((withdrawalPosition inventory active).item _ _).before.technology = claim.snapshot _ _ := by
    change _ = (claim.position.item _ _).before.technology
    rw [actual,signing_item,withdrawal_item]
  unfold Mandate.Challenge.readAttempt
  rw [dif_pos ⟨later,signed,snapshot⟩]
  rfl

theorem actual_new_claim_status (claim : Claim inventory)
    (born : claim ∈ Mandate.Challenge.claimsAt (Bound (epoch := epoch)) (Inputs inventory) (inventory.inputs.length+2)) :
    (Mandate.Challenge.through (Bound (epoch := epoch)) (Inputs inventory) claim ((Inputs inventory).length+2)).isPending =
      if (Mandate.law base epoch.scope).Valid (current epoch inventory.inputs)
        (Mandate.request epoch.scope (current epoch inventory.inputs) (withdrawalActor inventory active) .revoke)
      then false else true := by
  rw [actual_new_history_is_its_birth_then_the_same_withdrawal inventory active claim born]
  let attempt := (Mandate.Challenge.readAttempt (Bound (epoch := epoch)) (Inputs inventory) claim
    (withdrawalPosition inventory active)).get (new_claim_attempt_exists inventory active claim born)
  have decoded : Mandate.Challenge.readAttempt (Bound (epoch := epoch)) (Inputs inventory) claim
      (withdrawalPosition inventory active) = some attempt := (Option.some_get _).symm
  have actualPosition : attempt.position = withdrawalPosition inventory active := by
    unfold Mandate.Challenge.readAttempt at decoded
    split at decoded
    · have same := congrArg (fun result => result.map (fun attempt => attempt.position)) decoded
      simpa only [Option.map_some,Option.some.injEq] using same.symm
    · cases decoded
  have noReaffirm : Mandate.Challenge.readReconfirmation (Bound (epoch := epoch)) (Inputs inventory) claim
      (withdrawalPosition inventory active) = none := by
    simp only [Mandate.Challenge.readReconfirmation,withdrawal_cannot_birth inventory active]
  have status : ((Mandate.Challenge.History.initial (Bound (epoch := epoch)) (Inputs inventory) claim).receive _ _
      (withdrawalPosition inventory active)).isPending =
      if (Mandate.law base epoch.scope).Valid (attempt.position.item _ _).before (attempt.position.item _ _).request
      then false else true := by
    simp only [Mandate.Challenge.History.initial,Mandate.Challenge.History.receive,noReaffirm,
      Mandate.Challenge.Target.claim,decoded]
    split <;> rfl
  rw [actualPosition,withdrawal_item] at status
  exact status

omit active in
private theorem inherit_status (claim : Claim inventory)
    (history : Mandate.Challenge.History (Bound (epoch := epoch)) (Inputs inventory) claim) :
    (Mandate.Challenge.Cross.History.inherit (Bound (epoch := epoch)) history).isPending = history.isPending := by
  cases history with
  | pending target state slots => cases target <;> rfl
  | closed state archive slots => rfl

theorem every_actual_newborn_has_its_native_disposition
    (resident : Mandate.Challenge.Cross.Resident epoch.bound (Inputs inventory))
    (born : resident ∈ Mandate.Challenge.Cross.newborn epoch.bound (inputs := inventory.inputs) (word inventory)) :
    resident.history.isPending =
      if (Mandate.law base epoch.scope).Valid (current epoch inventory.inputs)
        (Mandate.request epoch.scope (current epoch inventory.inputs) (withdrawalActor inventory active) .revoke)
      then false else true := by
  obtain ⟨claim,_,same⟩ := List.mem_map.mp born
  cases same
  change (Mandate.Challenge.Cross.History.inherit (Bound (epoch := epoch))
    (Mandate.Challenge.through (Bound (epoch := epoch)) (Inputs inventory) claim.val ((Inputs inventory).length+2))).isPending = _
  rw [inherit_status]
  exact actual_new_claim_status inventory active claim.val claim.property

omit active in
private theorem archived_original_is_closed (record : Record inventory) (archived : record.history.isPending = false) :
    (original inventory record).history.isPending = false := by
  rcases record with ⟨originInputs,claim,history,within⟩
  cases history with
  | pending target state slots => cases archived
  | closed state archive slots =>
    change ((Mandate.Challenge.positionsAt (Bound (epoch := epoch)) (Inputs inventory) (inventory.inputs.length+2)).foldl
      (Mandate.Challenge.Cross.History.receive (Bound (epoch := epoch))) (.closed state archive slots)).isPending = false
    generalize Mandate.Challenge.positionsAt (Bound (epoch := epoch)) (Inputs inventory) (inventory.inputs.length+2) = positions
    induction positions with
    | nil => rfl
    | cons position rest ih => exact ih

theorem paid_shared_withdrawal_closes_the_entire_actual_census
    (paid : (Mandate.law base epoch.scope).Valid (current epoch inventory.inputs)
      (Mandate.request epoch.scope (current epoch inventory.inputs) (withdrawalActor inventory active) .revoke)) :
    ∀ resident ∈ (after inventory).objections, resident.history.isPending = false := by
  intro resident member
  rw [all_originals_and_only_actual_newborns_are_in_the_actual_inventory] at member
  rcases List.mem_append.mp member with old | born
  · obtain ⟨record,oldMember,same⟩ := List.mem_map.mp old
    cases same
    cases status : record.history.isPending with
    | false => exact archived_original_is_closed inventory record status
    | true =>
      have result := every_pending_original_has_its_actual_native_disposition inventory record status oldMember active
      rw [if_pos paid] at result
      exact result
  · have status := every_actual_newborn_has_its_native_disposition inventory active resident born
    rw [if_pos paid] at status
    exact status

theorem refused_shared_withdrawal_preserves_every_original_pending_status
    (refused : ¬ (Mandate.law base epoch.scope).Valid (current epoch inventory.inputs)
      (Mandate.request epoch.scope (current epoch inventory.inputs) (withdrawalActor inventory active) .revoke)) :
    ∀ record ∈ inventory.objections, (original inventory record).history.isPending = record.history.isPending := by
  intro record member
  cases status : record.history.isPending with
  | false => exact archived_original_is_closed inventory record status
  | true => rw [every_pending_original_has_its_actual_native_disposition inventory record status member active,if_neg refused]

omit active in
theorem an_empty_actual_word_has_no_newborn (empty : word inventory = []) :
    Mandate.Challenge.Cross.newborn epoch.bound (inputs := inventory.inputs) (word inventory) = [] := by
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
  change Mandate.Challenge.positionsAt (Mandate.Challenge.fromHistory epoch.bound)
    (Mandate.Challenge.Cross.nextInputs inventory.inputs (word inventory)) (inventory.inputs.length+2) = [] at noPositions
  apply List.eq_nil_iff_length_eq_zero.mpr
  simp only [Mandate.Challenge.Cross.newborn,List.length_map,List.length_attach]
  unfold Mandate.Challenge.claimsAt
  rw [noPositions]
  rfl

omit active in
inductive CensusReceipt where
  | private inactive (absent : ¬ Mandate.Response.Active (current epoch inventory.inputs))
      (empty : word inventory = [])
      (noBirth : Mandate.Challenge.Cross.newborn epoch.bound (inputs := inventory.inputs) (word inventory) = [])
      (preserved : ∀ record : Record inventory, (original inventory record).history.state = record.history.state)
  | private fulfilled (active : Mandate.Response.Active (current epoch inventory.inputs))
      (paid : (Mandate.law base epoch.scope).Valid (current epoch inventory.inputs)
        (Mandate.request epoch.scope (current epoch inventory.inputs) (withdrawalActor inventory active) .revoke))
      (closed : ∀ resident ∈ (after inventory).objections, resident.history.isPending = false)
      (withdrawn : (actual inventory).after.technology.holder = none ∧ (actual inventory).after.technology.offered = none ∧
        (actual inventory).after.technology.version = (current epoch inventory.inputs).technology.version+1)
  | private deferred (active : Mandate.Response.Active (current epoch inventory.inputs))
      (refused : ¬ (Mandate.law base epoch.scope).Valid (current epoch inventory.inputs)
        (Mandate.request epoch.scope (current epoch inventory.inputs) (withdrawalActor inventory active) .revoke))
      (coverage : ∀ actor ∈ Delegation.members epoch.scope.task,
        ¬ (Mandate.law base epoch.scope).Valid (current epoch inventory.inputs)
          (Mandate.request epoch.scope (current epoch inventory.inputs) actor .revoke))
      (oldStatus : ∀ record ∈ inventory.objections, (original inventory record).history.isPending = record.history.isPending)
      (newStatus : ∀ resident ∈ Mandate.Challenge.Cross.newborn epoch.bound (inputs := inventory.inputs) (word inventory), resident.history.isPending = true)

omit active in
def receipt : CensusReceipt inventory := by
  by_cases active : Mandate.Response.Active (current epoch inventory.inputs)
  · by_cases paid : (Mandate.law base epoch.scope).Valid (current epoch inventory.inputs)
      (Mandate.request epoch.scope (current epoch inventory.inputs) (withdrawalActor inventory active) .revoke)
    · exact .fulfilled active paid (paid_shared_withdrawal_closes_the_entire_actual_census inventory active paid)
        (accepted_shared_attempt_is_the_actual_withdrawal inventory active paid)
    · exact .deferred active paid (Redress.an_actual_refused_attempt_covers_exactly_current_member_revocations inventory active paid)
        (refused_shared_withdrawal_preserves_every_original_pending_status inventory active paid)
        (fun resident born => by rw [every_actual_newborn_has_its_native_disposition inventory active resident born,if_neg paid])
  · have empty : word inventory = [] := by simp [word,active]
    exact .inactive active empty (an_empty_actual_word_has_no_newborn inventory empty)
      (fun record => empty_word_preserves_the_complete_original_native_state inventory record empty)

omit active in
def CensusReceipt.kind : CensusReceipt inventory → Kind
  | .inactive .. => .inactive | .fulfilled .. => .fulfilled | .deferred .. => .deferred

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Challenge.Redress.Shared.Newborn
