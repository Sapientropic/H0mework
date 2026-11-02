import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Future.Native

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Future

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle
open Institutions.Capitalism.Universal.Source.ProgrammeFace Followup
variable {fuel : ℚ} {old : Followup.Joint.Inventory fuel} (ready : Ready old)

theorem signature_valid (before : Current) (actor : Bool) (member : actor ∈ Delegation.members ready.scope.task) :
    (epochLaw ready).Valid before (signature ready actor) := by
  change actor ∈ Delegation.members ready.task at member
  simp [epochLaw, Mandate.law, signature, RawLaw.Valid, RawLaw.SignerMatches,
    RawLaw.operationAllowed, RawPolicy.eval, eraseCurrent, eraseRequest, eraseOperation,
    base, RawLaw.requiredPorts, RawLaw.debit, RawLaw.credit, RawLaw.ClaimGuard,
    TaskUse, Ready.scope, NonnegativeBundle, member]

theorem every_challenge_choice_is_a_real_member (before : Current) (choice : Choice)
    (listed : choice ∈ menu ready .challenge before) : choice.actor ∈ Delegation.members ready.scope.task := by
  rcases List.mem_append.mp listed with generated | fallback
  · obtain ⟨method, _, selected⟩ := List.mem_flatMap.mp generated
    obtain ⟨actor, member, same⟩ := List.mem_map.mp selected
    cases same
    have same := List.mem_singleton.mp member
    rw [same]
    exact (Mandate.Response.firstMember ready.scope).property
  · have same := List.mem_singleton.mp fallback
    rw [same]
    exact (Mandate.Response.firstMember ready.scope).property

theorem an_active_cut_always_generates_a_valid_challenge (before : Current)
    (active : Mandate.Response.Active before) : (choose ready .challenge before).isSome = true := by
  have accepted : Legal ready .challenge before ⟨sponsor ready, .direct⟩ := by
    refine ⟨active, ?_⟩
    intro item member
    change item ∈ [⟨0, before, signature ready (sponsor ready)⟩] at member
    cases List.mem_singleton.mp member
    exact signature_valid ready before _ (Mandate.Response.firstMember ready.scope).property
  cases found : choose ready .challenge before with
  | some paid => rfl
  | none => exact False.elim (no_selected_choice_has_escaped_its_actual_check ready .challenge before found
      ⟨sponsor ready, .direct⟩ (by simp [menu, actors, List.flatMap]) accepted)

variable {originInputs : List (List Action)} (inventory : Inventory ready originInputs)
  (active : Mandate.Response.Active (current ready inventory.inputs))

noncomputable def challengePayment : Paid ready .challenge (current ready inventory.inputs) :=
  (choose ready .challenge (current ready inventory.inputs)).get (an_active_cut_always_generates_a_valid_challenge ready _ active)

noncomputable def challenger := (challengePayment ready inventory active).choice.actor

theorem challenge_word_is_one_original_signature :
    emit ready inventory .challenge = [signature ready (challenger ready inventory active)] := by
  have chosen := (Option.some_get (an_active_cut_always_generates_a_valid_challenge ready (current ready inventory.inputs) active)).symm
  change choose ready .challenge (current ready inventory.inputs) = some (challengePayment ready inventory active) at chosen
  rw [emit, paid_word_is_the_actual_selected_candidate ready _ _ _ chosen]
  rfl

noncomputable def challengeItems := Registered.traceItems
  (Mandate.Challenge.I (Mandate.Challenge.fromHistory (B ready)) (staged ready inventory .challenge).inputs)
  (ProgrammeHistory.visitAt (Mandate.Challenge.I (Mandate.Challenge.fromHistory (B ready)) (staged ready inventory .challenge).inputs)
    (inventory.inputs.length + 2)).current

theorem challenge_items_are_actual :
    challengeItems ready inventory = (epochLaw ready).rawItems (current ready inventory.inputs) (emit ready inventory .challenge) := by
  change (epochLaw ready).rawItems (Joint.actual ready inventory (emit ready inventory .challenge)).before
    (Joint.actual ready inventory (emit ready inventory .challenge)).submitted = _
  rw [(Joint.actual_word_and_cut ready inventory _).1, (Joint.actual_word_and_cut ready inventory _).2]

noncomputable def challengePosition : Mandate.Challenge.Position (Mandate.Challenge.fromHistory (B ready)) (staged ready inventory .challenge).inputs :=
  ⟨inventory.inputs.length + 2, ⟨0, by
    change 0 < (challengeItems ready inventory).length
    rw [challenge_items_are_actual, challenge_word_is_one_original_signature ready inventory active]
    simp [RawLaw.rawItems, RawLaw.execute]⟩⟩

theorem challenge_position_item :
    (challengePosition ready inventory active).item (Mandate.Challenge.fromHistory (B ready)) (staged ready inventory .challenge).inputs =
      ⟨0, current ready inventory.inputs, signature ready (challenger ready inventory active)⟩ := by
  have items := congrArg (fun items => items[0]?) (challenge_items_are_actual ready inventory)
  rw [challenge_word_is_one_original_signature ready inventory active] at items
  have bound : 0 < (challengeItems ready inventory).length := (challengePosition ready inventory active).index.isLt
  rw [List.getElem?_eq_getElem bound] at items
  exact Option.some.inj (items.trans (by simp [RawLaw.rawItems, RawLaw.execute]))

noncomputable def challengeClaim : Mandate.Challenge.Claim (Mandate.Challenge.fromHistory (B ready)) (staged ready inventory .challenge).inputs :=
  (Mandate.Challenge.read (Mandate.Challenge.fromHistory (B ready)) _ (challengePosition ready inventory active)).get (by
    have member := every_challenge_choice_is_a_real_member ready (current ready inventory.inputs)
      (challengePayment ready inventory active).choice (challengePayment ready inventory active).listed
    have signed : Mandate.Challenge.Submission (scope := ready.scope) (signature ready (challenger ready inventory active)) :=
      ⟨member, rfl, rfl, rfl, True.intro⟩
    have valid := signature_valid ready (current ready inventory.inputs) _ member
    have signedAt : Mandate.Challenge.Submission (scope := ready.scope)
        ((challengePosition ready inventory active).item (Mandate.Challenge.fromHistory (B ready)) _).request := by
      rw [challenge_position_item]
      exact signed
    have validAt : (Mandate.law base ready.scope).Valid
        ((challengePosition ready inventory active).item (Mandate.Challenge.fromHistory (B ready)) _).before
        ((challengePosition ready inventory active).item (Mandate.Challenge.fromHistory (B ready)) _).request := by
      rw [challenge_position_item]
      exact valid
    have activeAt : Mandate.Response.Active
        ((challengePosition ready inventory active).item (Mandate.Challenge.fromHistory (B ready)) _).before := by
      rw [challenge_position_item]
      exact active
    unfold Mandate.Response.Active at activeAt
    unfold Mandate.Challenge.read
    rw [dif_pos signedAt, dif_pos validAt, dif_pos activeAt]
    rfl)

theorem challenge_claim_is_in_the_actual_newborn_census :
    challengeClaim ready inventory active ∈ Mandate.Challenge.claimsAt (Mandate.Challenge.fromHistory (B ready))
      (staged ready inventory .challenge).inputs (inventory.inputs.length + 2) := by
  apply List.mem_filterMap.mpr
  refine ⟨challengePosition ready inventory active, ?_, (Option.some_get _).symm⟩
  exact List.mem_map.mpr ⟨(challengePosition ready inventory active).index, List.mem_finRange _, rfl⟩

noncomputable def challengeResident := Mandate.Challenge.Cross.Resident.admitAt (B ready) (inventory.inputs.length + 2)
  (by change inventory.inputs.length + 2 < (inventory.inputs ++ [emit ready inventory .challenge]).length + 2; simp)
  ⟨challengeClaim ready inventory active, challenge_claim_is_in_the_actual_newborn_census ready inventory active⟩

theorem challenge_resident_is_in_the_saved_next_inventory :
    challengeResident ready inventory active ∈ (staged ready inventory .challenge).objections := by
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨⟨challengeClaim ready inventory active, challenge_claim_is_in_the_actual_newborn_census ready inventory active⟩,
    List.mem_attach _ _, rfl⟩

noncomputable def generated_challenge_has_actual_native_continuation :=
  (Settlement.native ready (staged ready inventory .challenge)).objections
    (challengeResident ready inventory active) (challenge_resident_is_in_the_saved_next_inventory ready inventory active)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Future
