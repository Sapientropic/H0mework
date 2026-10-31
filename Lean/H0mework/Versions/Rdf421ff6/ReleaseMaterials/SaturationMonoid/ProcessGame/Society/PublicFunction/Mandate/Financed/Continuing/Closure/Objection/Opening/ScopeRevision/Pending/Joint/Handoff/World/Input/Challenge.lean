import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Standing

/-! Active authority admits a real signed native challenge at every epoch,
including zero-stock capture; the claim belongs to the actual newborn census. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle
open Institutions.Capitalism.Universal.Source.ProgrammeFace Followup
noncomputable section
variable (epoch : Epoch)

theorem signature_valid (before : Current) (actor : Bool) (member : actor ∈ Delegation.members epoch.scope.task) :
    (Mandate.law base epoch.scope).Valid before (signature epoch actor) := by
  change actor ∈ Delegation.members epoch.fresh.task at member
  simp [Mandate.law, signature, RawLaw.Valid, RawLaw.SignerMatches,
    RawLaw.operationAllowed, RawPolicy.eval, eraseCurrent, eraseRequest, eraseOperation,
    base, RawLaw.requiredPorts, RawLaw.debit, RawLaw.credit, RawLaw.ClaimGuard,
    TaskUse, Epoch.scope, Handoff.Ready.scope, NonnegativeBundle, member]

theorem every_challenge_choice_uses_the_actual_counterparty (before : Current) (choice : Choice)
    (listed : choice ∈ menu epoch .challenge before) : choice.actor = challengeActor epoch before := by
  rcases List.mem_append.mp listed with generated | fallback
  · obtain ⟨method, _, selected⟩ := List.mem_flatMap.mp generated
    obtain ⟨actor, member, same⟩ := List.mem_map.mp selected
    cases same
    have same := List.mem_singleton.mp member
    rw [same]
  · have same := List.mem_singleton.mp fallback
    rw [same]
    rfl

theorem every_challenge_choice_is_a_real_member (before : Current) (choice : Choice)
    (listed : choice ∈ menu epoch .challenge before) : choice.actor ∈ Delegation.members epoch.scope.task := by
  rw [every_challenge_choice_uses_the_actual_counterparty epoch before choice listed]
  exact challenge_actor_has_actual_standing epoch before

theorem an_active_cut_always_generates_a_valid_challenge (before : Current)
    (active : Mandate.Response.Active before) : (choose epoch .challenge before).isSome = true := by
  have accepted : Legal epoch .challenge before ⟨challengeActor epoch before, .direct⟩ := by
    refine ⟨active, ?_⟩
    intro item member
    change item ∈ [⟨0, before, signature epoch (challengeActor epoch before)⟩] at member
    cases List.mem_singleton.mp member
    exact signature_valid epoch before _ (challenge_actor_has_actual_standing epoch before)
  cases found : choose epoch .challenge before with
  | some paid => rfl
  | none => exact False.elim (no_selected_choice_has_escaped_its_actual_check epoch .challenge before found
      ⟨challengeActor epoch before, .direct⟩ (by simp [menu, actors, List.flatMap]) accepted)

variable {epoch} (inventory : Inventory epoch)
  (active : Mandate.Response.Active (current epoch inventory.inputs))

def challengePayment : Paid epoch .challenge (current epoch inventory.inputs) :=
  (choose epoch .challenge (current epoch inventory.inputs)).get (an_active_cut_always_generates_a_valid_challenge epoch _ active)

def challenger := (challengePayment inventory active).choice.actor

theorem challenger_is_the_actual_generated_counterparty :
    challenger inventory active = challengeActor epoch (current epoch inventory.inputs) :=
  every_challenge_choice_uses_the_actual_counterparty epoch _ _ (challengePayment inventory active).listed

theorem the_actual_challenger_is_independent_of_the_holder (members : BothMembers epoch.scope)
    (holder : Bool) (held : (current epoch inventory.inputs).technology.holder = some holder) :
    challenger inventory active = !holder ∧ challenger inventory active ≠ holder := by
  rw [challenger_is_the_actual_generated_counterparty]
  simp only [challengeActor, held, counterpart, if_pos (members (!holder))]
  exact ⟨True.intro, by cases holder <;> decide⟩

theorem the_actual_challenger_is_independent_of_the_offer (members : BothMembers epoch.scope)
    (holder : Bool) (unheld : (current epoch inventory.inputs).technology.holder = none)
    (offered : (current epoch inventory.inputs).technology.offered = some holder) :
    challenger inventory active = !holder ∧ challenger inventory active ≠ holder := by
  rw [challenger_is_the_actual_generated_counterparty]
  simp only [challengeActor, unheld, offered, counterpart, if_pos (members (!holder))]
  exact ⟨True.intro, by cases holder <;> decide⟩

theorem challenge_word_is_one_original_signature :
    emit inventory .challenge = [signature epoch (challenger inventory active)] := by
  have chosen := (Option.some_get (an_active_cut_always_generates_a_valid_challenge epoch (current epoch inventory.inputs) active)).symm
  change choose epoch .challenge (current epoch inventory.inputs) = some (challengePayment inventory active) at chosen
  rw [emit, paid_word_is_the_actual_selected_candidate epoch _ _ _ chosen]
  rfl

def challengeItems := Registered.traceItems
  (Mandate.Challenge.I (Mandate.Challenge.fromHistory epoch.bound) (staged inventory .challenge).inputs)
  (ProgrammeHistory.visitAt (Mandate.Challenge.I (Mandate.Challenge.fromHistory epoch.bound) (staged inventory .challenge).inputs)
    (inventory.inputs.length + 2)).current

theorem challenge_items_are_actual :
    challengeItems inventory = (Mandate.law base epoch.scope).rawItems (current epoch inventory.inputs) (emit inventory .challenge) := by
  change (Mandate.law base epoch.scope).rawItems (World.actual inventory (emit inventory .challenge)).before
    (World.actual inventory (emit inventory .challenge)).submitted = _
  rw [(World.actual_word_and_cut inventory _).1, (World.actual_word_and_cut inventory _).2]

def challengePosition : Mandate.Challenge.Position (Mandate.Challenge.fromHistory epoch.bound) (staged inventory .challenge).inputs :=
  ⟨inventory.inputs.length + 2, ⟨0, by
    change 0 < (challengeItems inventory).length
    rw [challenge_items_are_actual, challenge_word_is_one_original_signature inventory active]
    simp [RawLaw.rawItems, RawLaw.execute]⟩⟩

theorem challenge_position_item :
    (challengePosition inventory active).item (Mandate.Challenge.fromHistory epoch.bound) (staged inventory .challenge).inputs =
      ⟨0, current epoch inventory.inputs, signature epoch (challenger inventory active)⟩ := by
  have items := congrArg (fun items => items[0]?) (challenge_items_are_actual inventory)
  rw [challenge_word_is_one_original_signature inventory active] at items
  have bound : 0 < (challengeItems inventory).length := (challengePosition inventory active).index.isLt
  rw [List.getElem?_eq_getElem bound] at items
  exact Option.some.inj (items.trans (by simp [RawLaw.rawItems, RawLaw.execute]))

theorem the_actual_native_challenge_has_no_material_debit :
    (Mandate.law base epoch.scope).debit
      ((challengePosition inventory active).item (Mandate.Challenge.fromHistory epoch.bound) _).before
      ((challengePosition inventory active).item (Mandate.Challenge.fromHistory epoch.bound) _).request = [] := by
  rw [challenge_position_item]
  rfl

def challengeClaim : Mandate.Challenge.Claim (Mandate.Challenge.fromHistory epoch.bound) (staged inventory .challenge).inputs :=
  (Mandate.Challenge.read (Mandate.Challenge.fromHistory epoch.bound) _ (challengePosition inventory active)).get (by
    have member := every_challenge_choice_is_a_real_member epoch (current epoch inventory.inputs)
      (challengePayment inventory active).choice (challengePayment inventory active).listed
    have signed : Mandate.Challenge.Submission (scope := epoch.scope) (signature epoch (challenger inventory active)) :=
      ⟨member, rfl, rfl, rfl, True.intro⟩
    have valid := signature_valid epoch (current epoch inventory.inputs) _ member
    have signedAt : Mandate.Challenge.Submission (scope := epoch.scope)
        ((challengePosition inventory active).item (Mandate.Challenge.fromHistory epoch.bound) _).request := by
      rw [challenge_position_item]
      exact signed
    have validAt : (Mandate.law base epoch.scope).Valid
        ((challengePosition inventory active).item (Mandate.Challenge.fromHistory epoch.bound) _).before
        ((challengePosition inventory active).item (Mandate.Challenge.fromHistory epoch.bound) _).request := by
      rw [challenge_position_item]
      exact valid
    have activeAt : Mandate.Response.Active
        ((challengePosition inventory active).item (Mandate.Challenge.fromHistory epoch.bound) _).before := by
      rw [challenge_position_item]
      exact active
    unfold Mandate.Response.Active at activeAt
    unfold Mandate.Challenge.read
    rw [dif_pos signedAt, dif_pos validAt, dif_pos activeAt]
    rfl)

theorem challenge_claim_is_in_the_actual_newborn_census :
    challengeClaim inventory active ∈ Mandate.Challenge.claimsAt (Mandate.Challenge.fromHistory epoch.bound)
      (staged inventory .challenge).inputs (inventory.inputs.length + 2) := by
  apply List.mem_filterMap.mpr
  refine ⟨challengePosition inventory active, ?_, (Option.some_get _).symm⟩
  exact List.mem_map.mpr ⟨(challengePosition inventory active).index, List.mem_finRange _, rfl⟩

def challengeResident := Mandate.Challenge.Cross.Resident.admitAt epoch.bound (inventory.inputs.length + 2)
  (by change inventory.inputs.length + 2 < (inventory.inputs ++ [emit inventory .challenge]).length + 2; simp)
  ⟨challengeClaim inventory active, challenge_claim_is_in_the_actual_newborn_census inventory active⟩

theorem challenge_resident_is_in_the_saved_next_inventory :
    challengeResident inventory active ∈ (staged inventory .challenge).objections := by
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨⟨challengeClaim inventory active, challenge_claim_is_in_the_actual_newborn_census inventory active⟩,
    List.mem_attach _ _, rfl⟩

def generated_challenge_has_its_own_complete_native_run :=
  (challengeResident inventory active).history.state.generated

def generated_challenge_has_actual_repayment_continuation :=
  (challengeResident inventory active).responseRun epoch.bound (repayment inventory .challenge)

theorem generated_challenge_continues_in_the_full_next_inventory :
    (challengeResident inventory active).advance epoch.bound (repayment inventory .challenge) ∈
      (advance inventory .challenge).objections :=
  Mandate.Challenge.Cross.every_old_resident_is_actually_consumed epoch.bound
    (staged inventory .challenge).objections (repayment inventory .challenge)
    (challengeResident inventory active) (challenge_resident_is_in_the_saved_next_inventory inventory active)

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input
