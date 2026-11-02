import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Continuation

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Followup
variable {fuel : ℚ} {old : Followup.Joint.Inventory fuel} (ready : Ready old)
  {originInputs : List (List Action)} (inventory : Inventory ready originInputs)

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

private theorem silent_attempt (request : Request ready inventory) (candidate : Candidate) :
    ∀ action ∈ attempt ready inventory request candidate, ClaimSilent action := by
  intro action inside
  rcases List.mem_append.mp inside with first | rest
  · unfold preamble at first
    split at first
    · exact False.elim (List.not_mem_nil first)
    · have same := List.mem_singleton.mp first; subst action; trivial
  · rcases List.mem_append.mp rest with front | last
    · exact silent_front _ _ action front
    · have same := List.mem_singleton.mp last; subst action; trivial

theorem emitted_word_is_financially_silent : ∀ action ∈ emit ready inventory, ClaimSilent action := by
  intro action inside
  unfold emit at inside
  split at inside
  · rename_i request selected
    exact silent_attempt ready inventory request _ action inside
  · exact False.elim (List.not_mem_nil inside)

theorem actual_response_preserves_the_financial_past (silent : SilentPast inventory.inputs) :
    SilentPast (advance ready inventory).inputs := by
  intro word inside action member
  rcases List.mem_append.mp inside with previous | latest
  · exact silent word previous action member
  · have same := List.mem_singleton.mp latest
    subst word
    exact emitted_word_is_financially_silent ready inventory action member

theorem finite_responses_preserve_the_financial_past (silent : SilentPast inventory.inputs) (count : Nat) :
    SilentPast (run ready inventory count).inputs := by
  induction count with
  | zero => exact silent
  | succ count ih => exact actual_response_preserves_the_financial_past ready _ ih

theorem finite_alternation_preserves_the_financial_past (silent : SilentPast inventory.inputs)
    (words : List (List Action)) (physical : SilentPast words) : SilentPast (alternate ready inventory words).inputs := by
  induction words generalizing inventory with
  | nil => exact silent
  | cons word tail ih =>
    apply ih (submit ready (advance ready inventory) word)
    · intro actionWord inside action member
      rcases List.mem_append.mp inside with previous | latest
      · exact actual_response_preserves_the_financial_past ready inventory silent actionWord previous action member
      · have same := List.mem_singleton.mp latest
        subst actionWord
        exact physical word List.mem_cons_self action member
    · exact fun next member => physical next (List.mem_cons_of_mem _ member)

theorem original_native_finance_supports_the_complete_current_matrix (silent : SilentPast inventory.inputs) :
    Financial.BalanceConservation.ledgerClaims (I fuel (ScopeRevision.advance old).inputs) (legacy ready).account.current =
      (current ready inventory.inputs).claims := by
  have original := original_financial_sources_support_the_new_actual_matrix ready
  rw [the_actual_new_history_preserves_the_complete_old_claim_matrix] at original
  rw [physical_past_preserves_the_complete_original_claim_matrix ready inventory.inputs silent]
  exact original

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint
