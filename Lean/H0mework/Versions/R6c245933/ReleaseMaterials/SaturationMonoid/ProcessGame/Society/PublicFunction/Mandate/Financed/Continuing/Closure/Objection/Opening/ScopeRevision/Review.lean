import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.Renewal.Runtime

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Institutions.Capitalism.Universal.Source.ProgrammeFace Followup

variable {fuel : ℚ}

def exitAfter (inventory : Joint.Inventory fuel) :=
  (law.execute inventory.cut.past.frame.raw 0 (Exit.emit inventory)).final

def provision (inventory : Joint.Inventory fuel) : List Action :=
  if law.Valid (exitAfter inventory)
      (request scope (exitAfter inventory) (Review.produce base scope (exitAfter inventory)).actor.val .review)
  then [] else [Exit.production (Mandate.Response.firstMember scope).val]

def beforeReview (inventory : Joint.Inventory fuel) :=
  (law.execute (exitAfter inventory) 0 (provision inventory)).final

def review (inventory : Joint.Inventory fuel) := Review.produce base scope (beforeReview inventory)

def emit (inventory : Joint.Inventory fuel) := Exit.emit inventory ++ provision inventory ++ (review inventory).word

def advance (inventory : Joint.Inventory fuel) := Joint.submit inventory (emit inventory)

def reviewItem (inventory : Joint.Inventory fuel) : ExecutionItem Bool Good Mandate.Source.Port (State Bool Unit) Unit :=
  ⟨(Exit.emit inventory).length + (provision inventory).length, beforeReview inventory,
    request scope (beforeReview inventory) (review inventory).actor.val .review⟩

private theorem final_ignores_item_index (current : Current) (first second : Nat) (word : List Action) :
    (law.execute current first word).final = (law.execute current second word).final := by
  induction word generalizing current first second with
  | nil => rfl
  | cons action tail ih => exact ih (law.step current action) (first + 1) (second + 1)

theorem review_is_an_actual_original_item (inventory : Joint.Inventory fuel) :
    reviewItem inventory ∈ law.rawItems inventory.cut.past.frame.raw (emit inventory) := by
  unfold emit RawLaw.rawItems
  rw [law.execute_append, law.execute_append]
  simp only [Review.Outcome.word, RawLaw.execute, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
  right
  simp only [Nat.zero_add, List.length_append]
  rw [final_ignores_item_index _ _ 0 (provision inventory)]
  rfl

def positions (inventory : Joint.Inventory fuel) :=
  Response.positionsBefore (fuel := fuel) (inputs := (advance inventory).inputs) (inventory.cut.depth + 3)

def participants (inventory : Joint.Inventory fuel) :=
  ((positions inventory).map (fun position => (position.item fuel (advance inventory).inputs).request.signer)).eraseDups

theorem each_participant_has_an_actual_signature (inventory : Joint.Inventory fuel) (actor : Bool)
    (inside : actor ∈ participants inventory) :
    ∃ position ∈ positions inventory, (position.item fuel (advance inventory).inputs).request.signer = actor := by
  exact List.mem_map.mp (List.mem_eraseDups.mp inside)

theorem a_recorded_signer_is_a_real_actor (inventory : Joint.Inventory fuel)
    (position : Position fuel (advance inventory).inputs) :
    ActualBirth.presentAt (I fuel (advance inventory).inputs) (position.origin fuel _).visit
      (position.item fuel _).request.signer := by
  have actual := (position.origin fuel _).instruction_mem (I fuel _) (position.item fuel _) (position.decoded fuel _)
  change (position.item fuel _).request.signer ∈ (parties (I fuel _).law _)
  apply List.mem_dedup.mpr
  apply List.mem_flatMap.mpr
  refine ⟨position.item fuel _, actual, ?_⟩
  change (position.item fuel _).request.signer ∈ (position.item fuel _).request.signer :: _
  exact List.mem_cons_self

def entrant (inventory : Joint.Inventory fuel) :=
  (participants inventory).find? (fun actor => decide (actor ∉ Delegation.members task))

def Quiet (current : Current) : Prop := current.technology.holder = none ∧ current.technology.offered = none
instance (current : Current) : Decidable (Quiet current) := by unfold Quiet; infer_instance

structure Ready (inventory : Joint.Inventory fuel) where
  private mk ::
  paid : law.Valid (beforeReview inventory) (reviewItem inventory).request
  quiet : Quiet (advance inventory).cut.past.frame.raw
  actor : Bool
  recorded : actor ∈ participants inventory
  new_member : actor ∉ Delegation.members task

def choose (inventory : Joint.Inventory fuel) : Option (Ready inventory) :=
  if paid : law.Valid (beforeReview inventory) (reviewItem inventory).request then
    if quiet : Quiet (advance inventory).cut.past.frame.raw then
      match selected : entrant inventory with
      | some actor => some ⟨paid, quiet, actor, List.mem_of_find?_eq_some selected,
          of_decide_eq_true (List.find?_some (p := fun actor => decide (actor ∉ Delegation.members task)) selected)⟩
      | none => none
    else none
  else none

def slots (inventory : Joint.Inventory fuel) : List (ServiceSlot Bool Good) :=
  (participants inventory).flatMap fun actor =>
    [⟨actor, base.necessities (eraseCurrent (advance inventory).cut.past.frame.raw) actor, .necessity⟩,
     ⟨actor, base.mandatoryMaintenance (eraseCurrent (advance inventory).cut.past.frame.raw) actor, .maintenance⟩]

def Ready.task {inventory : Joint.Inventory fuel} (ready : Ready inventory) : PublicTaskSpec Bool Good :=
  ⟨slots inventory, (advance inventory).cut.past.frame.raw.clock + 2,
    (advance inventory).cut.past.frame.raw.clock + 3, by
      refine ⟨⟨ready.actor, [(.service, 1)], .necessity⟩, ?_, (.service, 1), by simp, by decide⟩
      apply List.mem_flatMap.mpr
      exact ⟨ready.actor, ready.recorded, by simp [base]⟩⟩

def Ready.scope {inventory : Joint.Inventory fuel} (ready : Ready inventory) :
    Mandate.Scope (Party := Bool) (Good := Good) (Port := Mandate.Source.Port) :=
  ⟨ready.task, .service, .challenge, by decide, [(.service, 1)]⟩

theorem the_new_member_really_belongs_to_the_generated_scope {inventory : Joint.Inventory fuel} (ready : Ready inventory) :
    ready.actor ∈ Delegation.members ready.scope.task := by
  apply List.mem_map.mpr
  refine ⟨⟨ready.actor, [(.service, 1)], .necessity⟩, ?_, rfl⟩
  apply List.mem_flatMap.mpr
  exact ⟨ready.actor, ready.recorded, by simp [base]⟩

inductive Blocked (inventory : Joint.Inventory fuel) : Prop where
  | unpaid (refused : ¬ law.Valid (beforeReview inventory) (reviewItem inventory).request)
  | active (retained : ¬ Quiet (advance inventory).cut.past.frame.raw)
  | no_new_actor (absent : entrant inventory = none)

theorem every_refused_scope_handoff_has_an_actual_reason (inventory : Joint.Inventory fuel)
    (absent : choose inventory = none) : Blocked inventory := by
  unfold choose at absent
  split at absent
  · split at absent
    · split at absent
      · cases absent
      · exact .no_new_actor (by assumption)
    · exact .active (by assumption)
  · exact .unpaid (by assumption)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision
