import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Source

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Followup

variable {fuel : ℚ} {inventory : Joint.Inventory fuel} (ready : Ready inventory)

def ClaimSilent (action : Action) : Prop := match action.operation with
  | .issue .. | .assign .. | .settle .. => False
  | _ => True

private theorem silent_step (current : Current) (action : Action) (silent : ClaimSilent action) :
    ((epochLaw ready).step current action).claims = current.claims := by
  unfold RawLaw.step
  split
  · change RawLaw.nextClaims current action = current.claims
    rcases action with ⟨signer, consents, purpose, gates, operation⟩
    cases operation <;> simp_all [ClaimSilent, RawLaw.nextClaims]
  · rfl

private theorem silent_execute (current : Current) (index : Nat) (word : List Action)
    (silent : ∀ action ∈ word, ClaimSilent action) :
    ((epochLaw ready).execute current index word).final.claims = current.claims := by
  induction word generalizing current index with
  | nil => rfl
  | cons action tail ih =>
      change ((epochLaw ready).execute ((epochLaw ready).step current action) (index + 1) tail).final.claims = _
      rw [ih _ _ (fun next inside => silent next (List.mem_cons_of_mem _ inside)),
        silent_step ready current action (silent action List.mem_cons_self)]

private theorem silent_provision (current : Current) (actor : Bool) :
    ∀ action ∈ provisionActor ready current actor, ClaimSilent action := by
  intro action inside
  unfold provisionActor at inside
  dsimp only at inside
  split at inside
  · rcases List.mem_append.mp inside with one | many
    · have same := List.mem_singleton.mp one
      subst action
      trivial
    · obtain ⟨_, rfl⟩ := List.mem_replicate.mp many
      trivial
  · obtain ⟨_, rfl⟩ := List.mem_replicate.mp inside
    trivial

private theorem silent_production (current : Current) (actors : List Bool) :
    ∀ action ∈ productionWord ready current actors, ClaimSilent action := by
  induction actors generalizing current with
  | nil => simp [productionWord]
  | cons actor tail ih =>
      intro action inside
      obtain front | rest := List.mem_append.mp inside
      · exact silent_provision ready current actor action front
      · exact ih _ action rest

private theorem silent_candidate (current : Current) (method : Method) :
    ∀ action ∈ candidate ready current method, ClaimSilent action := by
  intro action inside
  unfold candidate at inside
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at inside
  rcases inside with (((front | pair) | service) | challenge) | revoke | review
  · cases method with
    | direct => exact False.elim (List.not_mem_nil front)
    | productive => exact silent_production ready current _ action front
  · rcases List.mem_cons.mp pair with rfl | rest
    · trivial
    · have same := List.mem_singleton.mp rest
      subst action
      trivial
  · obtain ⟨slot, _, rfl⟩ := List.mem_map.mp service
    trivial
  · subst action; trivial
  · subst action; trivial
  · subst action; trivial

theorem epoch_word_preserves_every_claim_address (current : Current) :
    ((epochLaw ready).next current (epochWord ready current)).claims = current.claims :=
  silent_execute ready current 0 _ (silent_candidate ready current _)

theorem the_actual_new_history_preserves_the_complete_old_claim_matrix :
    (epochCurrent ready 3).claims = (epochInitial ready).claims := by
  rw [generated_word_has_its_own_actual_after, epoch_word_preserves_every_claim_address]
  change ((epochLaw ready).execute ((epochLaw ready).next (epochInitial ready) []) 0
    [refusedRequest ready]).final.claims = _
  rw [silent_execute ready _ 0 _ (by
    intro action inside
    have same := List.mem_singleton.mp inside
    subst action
    trivial)]
  rfl

noncomputable def legacy (_ : Ready inventory) := Runtime.generate fuel (advance inventory).inputs inventory.cut.depth

theorem original_financial_sources_support_the_new_actual_matrix :
    Financial.BalanceConservation.ledgerClaims (I fuel (advance inventory).inputs)
      (legacy ready).account.current = (epochCurrent ready 3).claims := by
  rw [the_actual_new_history_preserves_the_complete_old_claim_matrix]
  have same := (advance inventory).cut.actual_current
  have depth : (advance inventory).cut.depth = inventory.cut.depth + 1 :=
    Joint.afterInput_depth inventory.cut (emit inventory)
  rw [depth, Nat.add_assoc] at same
  change epochInitial ready = currentAt fuel (advance inventory).inputs (inventory.cut.depth + 3) at same
  rw [same]
  exact (legacy ready).actual_matrix

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision
