import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Followup.Joint.Continuation

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Followup.Joint

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {fuel : ℚ} {inputs : List (List Action)} {cut : Cut fuel inputs}

theorem every_fresh_signature_continues_an_actual_row_or_admits_a_native_row
    (rows : List (Row cut)) (seen : List PositionKey) (event : Event cut) (claim : Claim fuel inputs)
    (decoded : read fuel inputs event.val = some claim) (fresh : eventKey event ∉ seen) :
    ((decide rows seen event).mode = .continued ∧
      (∃ row ∈ rows, row.canReconfirm event = true) ∧ (decide rows seen event).newborn = none) ∨
    ((decide rows seen event).mode = .admitted ∧ ∃ row, (decide rows seen event).newborn = some row) := by
  generalize selected : decide rows seen event = decision
  cases decision with
  | ordinary absent => rw [decoded] at absent; cases absent
  | known original exact repeated => exact False.elim (fresh repeated)
  | continued original exact new existing =>
      exact Or.inl ⟨rfl, List.any_eq_true.mp existing, rfl⟩
  | admitted original exact new noExisting => exact Or.inr ⟨rfl, _, rfl⟩

theorem continuation_and_fresh_admission_are_mutually_exclusive (rows : List (Row cut)) (seen : List PositionKey)
    (event : Event cut) : ¬ ((decide rows seen event).mode = .continued ∧ (decide rows seen event).mode = .admitted) := by
  rintro ⟨continued, admitted⟩
  cases continued.symm.trans admitted

theorem every_actual_new_signature_has_a_joint_disposition (inventory : Inventory fuel) (word : List Action)
    (index : Fin (actualEvents inventory.cut word).length) (claim : Claim fuel (submit inventory word).inputs)
    (decoded : read fuel (submit inventory word).inputs ((actualEvents inventory.cut word).get index).val = some claim)
    :
    ((decisionAt inventory word index).mode = .continued ∧
      (∃ row ∈ (frameBefore inventory word index.val).rows, row.canReconfirm ((actualEvents inventory.cut word).get index) = true) ∧
      (decisionAt inventory word index).newborn = none) ∨
    ((decisionAt inventory word index).mode = .admitted ∧ (newbornAt inventory word index).isSome = true) := by
  rcases every_fresh_signature_continues_an_actual_row_or_admits_a_native_row _ _ _ claim decoded (actual_event_is_fresh inventory word index) with continued | admitted
  · exact Or.inl continued
  · obtain ⟨mode, row, born⟩ := admitted
    exact Or.inr ⟨mode, newbornAt_is_complete inventory word index row born⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Followup.Joint
