import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Source
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Effects

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Followup

variable {fuel : ℚ} {inventory : Joint.Inventory fuel} (ready : Ready inventory)

private theorem silent_step (before : Current) (action : Action) (silent : ClaimSilent action) :
    ((epochLaw ready).step before action).claims = before.claims := by
  unfold RawLaw.step
  split
  · change RawLaw.nextClaims before action = before.claims
    rcases action with ⟨signer, consents, purpose, gates, operation⟩
    cases operation <;> simp_all [ClaimSilent, RawLaw.nextClaims]
  · rfl

private theorem silent_execute (before : Current) (index : Nat) (word : List Action)
    (silent : ∀ action ∈ word, ClaimSilent action) :
    ((epochLaw ready).execute before index word).final.claims = before.claims := by
  induction word generalizing before index with
  | nil => rfl
  | cons action tail ih =>
    change ((epochLaw ready).execute ((epochLaw ready).step before action) (index + 1) tail).final.claims = _
    rw [ih _ _ (fun next member => silent next (List.mem_cons_of_mem _ member)),
      silent_step ready before action (silent action List.mem_cons_self)]

def SilentPast (inputs : List (List Action)) : Prop := ∀ word ∈ inputs, ∀ action ∈ word, ClaimSilent action

private theorem silent_front (candidate : Candidate) (before : Current) :
    ∀ action ∈ candidate.front before, ClaimSilent action := by
  intro action inside
  cases candidate with
  | mk actor command method =>
    cases method with
    | direct => exact False.elim (List.not_mem_nil inside)
    | productive => have same := List.mem_singleton.mp inside; subst action; trivial
    | supplied =>
      unfold Candidate.front at inside
      dsimp only at inside
      split at inside
      · rcases List.mem_append.mp inside with one | one <;>
          have same := List.mem_singleton.mp one <;> subst action <;> trivial
      · have same := List.mem_singleton.mp inside; subst action; trivial

private theorem silent_attempt (inputs : List (List Action)) (request : Request ready inputs) (candidate : Candidate) :
    ∀ action ∈ attempt ready inputs request candidate, ClaimSilent action := by
  intro action inside
  rcases List.mem_append.mp inside with first | rest
  · unfold preamble at first
    split at first
    · exact False.elim (List.not_mem_nil first)
    · have same := List.mem_singleton.mp first; subst action; trivial
  · rcases List.mem_append.mp rest with front | last
    · exact silent_front _ _ action front
    · have same := List.mem_singleton.mp last; subst action; trivial

theorem emitted_word_preserves_every_financial_address (inputs : List (List Action)) :
    (afterCurrent ready inputs).claims = (current ready inputs).claims := by
  rw [emitted_response_has_its_own_generated_after]
  apply silent_execute
  intro action inside
  unfold emit at inside
  split at inside
  · rename_i request selected
    exact silent_attempt ready inputs request _ action inside
  · exact False.elim (List.not_mem_nil inside)

theorem physical_past_preserves_the_complete_original_claim_matrix (inputs : List (List Action)) (silent : SilentPast inputs) :
    (current ready inputs).claims = (epochInitial ready).claims := by
  induction inputs using List.reverseRecOn with
  | nil =>
    change (OutstandingSource.History.currentAt (epochSource ready) [] 2).claims = _
    rw [(OutstandingSource.History.actual_frame (epochSource ready) [] 2).1]
    change ((epochLaw ready).execute ((epochLaw ready).next (epochInitial ready) []) 0 [refusedRequest ready]).final.claims = _
    exact silent_execute ready _ 0 _ (by intro action member; have same := List.mem_singleton.mp member; subst action; trivial)
  | append_singleton past word ih =>
    have before := Mandate.Challenge.Cross.emitted_word_uses_actual_cut (B ready) past word
    have emitted := Mandate.Challenge.Cross.emitted_word_is_actual (B ready) past word
    have after := OutstandingSource.History.actual_next (epochSource ready) (past ++ [word]) (past.length + 1)
    have actual : OutstandingSource.History.currentAt (epochSource ready) (past ++ [word]) (past.length + 3) =
        (epochLaw ready).next (current ready past) word := by
      calc
        _ = (OutstandingSource.History.actualExecution (epochSource ready) (past ++ [word]) (past.length + 1)).after := after.symm
        _ = _ := congrArg₂ (epochLaw ready).next before emitted
    change (OutstandingSource.History.currentAt (epochSource ready) (past ++ [word]) ((past ++ [word]).length + 2)).claims = _
    simp only [List.length_append, List.length_singleton, Nat.add_assoc] at *
    rw [actual]
    exact (silent_execute ready (current ready past) 0 word (silent word (by simp))).trans
      (ih (fun next member => silent next (List.mem_append_left _ member)))

theorem original_native_finance_supports_the_actual_response_matrix (inputs : List (List Action)) (silent : SilentPast inputs) :
    Financial.BalanceConservation.ledgerClaims (I fuel (advance inventory).inputs) (legacy ready).account.current =
      (afterCurrent ready inputs).claims := by
  rw [emitted_word_preserves_every_financial_address, physical_past_preserves_the_complete_original_claim_matrix ready inputs silent]
  have paid := original_financial_sources_support_the_new_actual_matrix ready
  rw [the_actual_new_history_preserves_the_complete_old_claim_matrix] at paid
  exact paid

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending
