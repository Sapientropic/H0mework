import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Finance
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.BalanceConservation.Execution

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Finance

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle
open Followup Financial.Family.BalanceConservation

variable {fuel : ℚ} {old : Followup.Joint.Inventory fuel} (ready : Ready old)

abbrev epochInput (inputs : List (List Action)) := OutstandingSource.History.input (epochSource ready) inputs

theorem original_compatible (inputs : List (List Action)) :
    Compatible sources (epochInput ready inputs) (originalAccount ready).current := by
  intro claim member
  rw [every_original_native_claim_is_literal] at member
  obtain ⟨original, _, same⟩ := List.mem_map.mp member
  subst claim
  exact ⟨rfl, rfl⟩

theorem original_matrix_at_epoch_initial :
    Financial.Family.ledgerClaims sources (originalAccount ready).current = (epochInitial ready).claims := by
  rw [original_complete_matrix]
  have matched := ScopeRevision.original_financial_sources_support_the_new_actual_matrix ready
  rw [ScopeRevision.the_actual_new_history_preserves_the_complete_old_claim_matrix] at matched
  exact matched

theorem initial_matrix (inputs : List (List Action)) :
    Financial.Family.ledgerClaims sources (initial ready inputs).current = (current ready inputs).claims := by
  simpa [initial, epochInput, current, OutstandingSource.History.currentAt, sources] using
    continueVisits_claims_source sources (epochInput ready inputs) 0 (inputs.length + 2) (originalAccount ready)
    (original_compatible ready inputs) (original_matrix_at_epoch_initial ready)

theorem Generated.compatible {originInputs inputs : List (List Action)} {state : Account}
    (generated : Generated ready originInputs inputs state) (targetInputs : List (List Action)) :
    Compatible sources (epochInput ready targetInputs) state.current := by
  induction generated with
  | initial =>
      exact continueVisits_compatible sources (epochInput ready _) 0 _ _ (original_compatible ready _)
  | @submit inputs state prior word ih =>
      exact consumeVisit_compatible sources (epochInput ready (inputs ++ [word])) _ _ ih

theorem Generated.actual_matrix {originInputs inputs : List (List Action)} {state : Account}
    (generated : Generated ready originInputs inputs state) :
    Financial.Family.ledgerClaims sources state.current = (current ready inputs).claims := by
  induction generated with
  | initial => exact initial_matrix ready _
  | @submit inputs state prior word ih =>
      have before : OutstandingSource.History.currentAt (epochSource ready) (inputs ++ [word]) (inputs.length + 2) =
          current ready inputs := Mandate.Challenge.Cross.emitted_word_uses_actual_cut (B ready) inputs word
      have matched : Financial.Family.ledgerClaims sources state.current =
          (OutstandingSource.History.currentAt (epochSource ready) (inputs ++ [word]) (inputs.length + 2)).claims := by
        rw [before]
        exact ih
      have next := consumeVisit_claims_source_next sources (epochInput ready (inputs ++ [word]))
        (inputs.length + 2) state (prior.compatible ready _) matched
      simpa only [append, current, OutstandingSource.History.currentAt, sources, id_eq, epochInput,
        List.length_append, List.length_singleton, Nat.add_assoc] using next

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Finance
