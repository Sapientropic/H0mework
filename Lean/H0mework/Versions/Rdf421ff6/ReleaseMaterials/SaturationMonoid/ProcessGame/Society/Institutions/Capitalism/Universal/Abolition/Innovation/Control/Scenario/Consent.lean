import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Control.Scenario.Source
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program.Resigning

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Control.Scenario

open Source.Program

theorem public_validity_does_not_require_the_old_controller_consents
    (before : Current) (action : RequestAt) :
    openLaw.Valid before action ↔ openLaw.Valid before (action.resign action.signer) := by
  constructor
  · intro accepted
    exact ⟨accepted.1, fun _ _ => .inl rfl, accepted.2.2⟩
  · intro accepted
    exact ⟨accepted.1, fun _ _ => .inl rfl, accepted.2.2⟩

theorem clearing_the_old_consents_keeps_the_same_actual_public_effect
    (before : Current) (action : RequestAt) :
    openLaw.step before (action.resign action.signer) = openLaw.step before action := by
  by_cases accepted : openLaw.Valid before action
  · exact openLaw.accepted_resign_same_effect before action action.signer accepted
      ((public_validity_does_not_require_the_old_controller_consents before action).mp accepted)
  · have refused : ¬ openLaw.Valid before (action.resign action.signer) :=
      fun paid => accepted ((public_validity_does_not_require_the_old_controller_consents before action).mpr paid)
    rw [openLaw.rejected_preserves_current _ _ refused, openLaw.rejected_preserves_current _ _ accepted]

def withoutOwnerConsents (word : RawEvent Party Good Bool Nat Unit) :=
  word.map fun action => action.resign action.signer

theorem the_complete_public_material_result_keeps_no_owner_consent_gate
    (before : Current) (position : Nat) (word : RawEvent Party Good Bool Nat Unit) :
    (openLaw.execute before position (withoutOwnerConsents word)).final =
      (openLaw.execute before position word).final := by
  induction word generalizing before position with
  | nil => rfl
  | cons action word ih =>
      simp only [withoutOwnerConsents, List.map_cons, RawLaw.execute]
      rw [clearing_the_old_consents_keeps_the_same_actual_public_effect]
      exact ih _ _

theorem every_cleared_request_has_only_its_original_own_signature
    (word : RawEvent Party Good Bool Nat Unit) (action : RequestAt)
    (original : action ∈ withoutOwnerConsents word) : action.consents = [] := by
  obtain ⟨previous, _listed, rfl⟩ := List.mem_map.mp original
  rfl

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Control.Scenario
