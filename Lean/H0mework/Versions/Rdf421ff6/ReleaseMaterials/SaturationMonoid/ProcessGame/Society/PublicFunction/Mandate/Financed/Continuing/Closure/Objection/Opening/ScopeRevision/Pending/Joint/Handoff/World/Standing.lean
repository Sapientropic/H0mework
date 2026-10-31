import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Source

/-! The paid origin supplies both actual task members. Actual scope
handoffs retain their service slots, so finite future inputs retain standing. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
noncomputable section
variable {oldScope : Mandate.Scope (Party := Bool) (Good := Good) (Port := Mandate.Source.Port)}
  {bound : BoundSource base oldScope} {inputs : List (List Action)} (fresh : Ready bound inputs)

private def MaterialOnly (word : List Action) : Prop :=
  ∀ action ∈ word, ∀ actor target, action.operation ≠ .revise actor target

private theorem material_append {left right : List Action}
    (first : MaterialOnly left) (second : MaterialOnly right) : MaterialOnly (left ++ right) := by
  intro action member actor target
  rcases List.mem_append.mp member with earlier | later
  · exact first action earlier actor target
  · exact second action later actor target

private theorem provision_material (before : Current) (actor : Bool) :
    MaterialOnly (provisionActor fresh before actor) := by
  intro action member operator target same
  simp only [provisionActor, List.mem_append, List.mem_replicate] at member
  rcases member with transfer | production
  · split at transfer
    · cases List.mem_singleton.mp transfer
      cases same
    · exact List.not_mem_nil transfer
  · rcases production with ⟨_, rfl⟩
    cases same

private theorem production_material (before : Current) (actors : List Bool) :
    MaterialOnly (productionWord fresh before actors) := by
  induction actors generalizing before with
  | nil => simp [productionWord, MaterialOnly]
  | cons actor tail ih =>
      exact material_append (provision_material fresh before actor) (ih _)

private theorem affordable_material (before : Current) (actor : Bool) (count : Nat) :
    MaterialOnly (affordableProduction fresh before actor count) := by
  induction count generalizing before with
  | zero => simp [affordableProduction, MaterialOnly]
  | succ count ih =>
      unfold affordableProduction
      split
      · apply material_append (left := [Exit.production actor]) (right := affordableProduction fresh _ actor count)
        · simp [MaterialOnly, Exit.production]
        · exact ih _
      · simp [MaterialOnly]

private theorem affordable_word_material (before : Current) (actors : List Bool) :
    MaterialOnly (affordableWord fresh before actors) := by
  induction actors generalizing before with
  | nil => simp [affordableWord, MaterialOnly]
  | cons actor tail ih => exact material_append (affordable_material fresh before actor _) (ih _)

private theorem funding_material (before : Current) (actor : Bool) (amount : ℚ) :
    MaterialOnly (Future.funding before actor amount) := by
  dsimp only [Future.funding]
  split <;> simp [MaterialOnly]

private theorem financing_material (before : Current) (actors : List Bool) :
    MaterialOnly (financing fresh before actors) := by
  induction actors generalizing before with
  | nil => simp [financing, MaterialOnly]
  | cons actor tail ih => exact material_append (funding_material before actor _) (ih _)

private theorem supplied_material (before : Current) (actor : Bool) :
    MaterialOnly (Future.provision before actor) := by
  dsimp only [Future.provision]
  split <;> simp [MaterialOnly, Exit.production]

private theorem front_material (before : Current) (method : Method) :
    MaterialOnly (method.front fresh before) := by
  cases method
  · simp [Method.front, MaterialOnly]
  · exact production_material fresh before _
  · exact material_append (affordable_word_material fresh before _)
      (financing_material fresh _ _)
  · exact material_append
      (material_append (affordable_word_material fresh before _) (financing_material fresh _ _))
      (supplied_material _ _)

private theorem candidate_command_signer (before : Current) (method : Method)
    (action : Action) (member : action ∈ candidate fresh before method)
    (operator : Bool) (target : State Bool Unit) (command : action.operation = .revise operator target) :
    action.signer = fresh.actor := by
  simp only [candidate, List.mem_append] at member
  rcases member with original | restore
  · simp only [serviceWord,List.mem_append] at original
    rcases original with (((front | pair) | service) | challenge) | last
    · exact False.elim (front_material fresh before method action front operator target command)
    · simp only [signedPair, List.mem_cons, List.not_mem_nil, or_false] at pair
      rcases pair with rfl | rfl <;> rfl
    · obtain ⟨slot, _, rfl⟩ := List.mem_map.mp service
      rfl
    · cases List.mem_singleton.mp challenge
      cases command
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at last
      rcases last with rfl | rfl <;> rfl
  · have material : MaterialOnly (restoreExit fresh ((law fresh).execute before 0 (serviceWord fresh before method)).final) := by
      unfold restoreExit
      split
      · simp [MaterialOnly]
      · exact supplied_material _ _
    exact False.elim (material action restore operator target command)

theorem candidate_grant_is_by_the_actual_review_actor (before : Current) (method : Method)
    (grant : Mandate.Grant base fresh.scope before (candidate fresh before method)) :
    grant.candidate = fresh.actor := by
  have request_member : grant.acceptance.item.val.request ∈ candidate fresh before method := by
    have mapped : grant.acceptance.item.val.request ∈
        ((Mandate.law base fresh.scope).rawItems before (candidate fresh before method)).map ExecutionItem.request :=
      List.mem_map.mpr ⟨grant.acceptance.item.val, grant.acceptance.item.property, rfl⟩
    simpa only [RawLaw.rawItems, RawLaw.inventory_requests_exact] using mapped
  exact grant.candidate_actually_signed.symm.trans
    (candidate_command_signer fresh before method _ request_member _ _ grant.acceptance.operation)

def BothMembers (scope : Mandate.Scope (Party := Bool) (Good := Good) (Port := Mandate.Source.Port)) : Prop :=
  ∀ actor : Bool, actor ∈ Delegation.members scope.task

theorem paid_origin_generates_both_task_members (before : Current) (paid : Paid fresh before) :
    BothMembers fresh.scope := by
  let opening := paid.opening fresh before
  have candidate_member : opening.grant.candidate ∈ Delegation.members fresh.scope.task := by
    rw [candidate_grant_is_by_the_actual_review_actor fresh before paid.method opening.grant]
    exact fresh.review_actor_is_in_the_generated_task
  have challenger_member := opening.challenge_signed.1
  have distinct := opening.independent
  intro actor
  cases actor <;> cases candidate : opening.grant.candidate <;>
    cases challenger : opening.challenge.request.signer <;> simp_all

theorem actual_handoff_retains_every_task_member (actor : Bool)
    (member : actor ∈ Delegation.members bound.source.seed.task) :
    actor ∈ Delegation.members fresh.scope.task := by
  obtain ⟨slot, inside, bearer⟩ := List.mem_map.mp member
  exact List.mem_map.mpr ⟨slot, every_original_task_slot_is_retained fresh slot inside, bearer⟩

namespace World
variable {epoch : Epoch} (inventory : Inventory epoch)

theorem every_actual_next_retains_standing (actor : Bool)
    (member : actor ∈ Delegation.members epoch.scope.task) :
    actor ∈ Delegation.members (next inventory).1.scope.task := by
  unfold next
  cases cycleResult inventory
  next fresh selected saved exact =>
    exact actual_handoff_retains_every_task_member fresh actor member
  next absent reason => exact member

theorem both_members_survive_the_actual_next (members : BothMembers epoch.scope) :
    BothMembers (next inventory).1.scope :=
  fun actor => every_actual_next_retains_standing inventory actor (members actor)

theorem every_finite_epoch_chain_preserves_both_members (packet : Packet) (count : Nat)
    (members : BothMembers packet.1.scope) : BothMembers (evolve packet count).1.scope := by
  induction count generalizing packet with
  | zero => exact members
  | succ count ih =>
      exact ih (next packet.2) (both_members_survive_the_actual_next packet.2 members)

theorem every_finite_primitive_epoch_chain_preserves_both_members (packet : Packet) (words : List (List Action))
    (members : BothMembers packet.1.scope) : BothMembers (alternate packet words).1.scope := by
  induction words generalizing packet with
  | nil => exact members
  | cons word tail ih =>
      exact ih (next (submit packet.2 word)) (both_members_survive_the_actual_next (submit packet.2 word) members)

namespace Input

theorem every_actual_input_cycle_retains_both_members (intent : Intent) (members : BothMembers epoch.scope) :
    BothMembers (cycle inventory intent).1.scope :=
  both_members_survive_the_actual_next (advance inventory intent) members

theorem every_finite_input_epoch_chain_preserves_both_members (packet : Packet) (intents : List Intent)
    (members : BothMembers packet.1.scope) : BothMembers (run packet intents).1.scope := by
  induction intents generalizing packet with
  | nil => exact members
  | cons intent tail ih =>
      exact ih (cycle packet.2 intent) (every_actual_input_cycle_retains_both_members packet.2 intent members)

end Input
end World

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff
