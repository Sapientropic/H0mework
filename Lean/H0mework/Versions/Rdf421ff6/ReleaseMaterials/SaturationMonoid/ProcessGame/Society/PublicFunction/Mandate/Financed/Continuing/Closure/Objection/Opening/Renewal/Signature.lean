import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.Renewal.Repair

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.Renewal

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Institutions.Capitalism.Universal.Source.ProgrammeFace Followup

variable {fuel : ℚ} {inputs : List (List Action)}

def word (current : Current) (actor : Bool) := attemptedWord current actor ++ [submission]

theorem prefix_keeps_the_current_holder (current : Current) (actor : Bool) :
    (law.execute current 0 (attemptedWord current actor)).final.technology.holder = current.technology.holder := by
  unfold attemptedWord
  rw [law.execute_append]
  have material := material_execution_keeps_authority
    (law.execute current 0 (core current actor)).final (0 + (core current actor).length) (repairs current actor) (by
      intro action inside
      obtain ⟨demand, _, rfl⟩ := List.mem_map.mp inside
      rfl)
  exact (congrArg State.holder material).trans (core_keeps_the_current_holder current actor)

def signaturePosition (cut : Cut fuel inputs) (actor : Bool) : Position fuel (branchInputs cut (word cut.past.frame.raw actor)) :=
  ⟨cut.depth + 2, ⟨(attemptedWord cut.past.frame.raw actor).length, by
    change _ < (financialItems fuel (branchInputs cut (word cut.past.frame.raw actor)) (cut.depth + 2)).length
    rw [new_items]
    simp only [RawLaw.rawItems, law.inventory_length, word, List.length_append, List.length_singleton]
    omega⟩⟩

theorem signature_item (cut : Cut fuel inputs) (actor : Bool) :
    (signaturePosition cut actor).item fuel (branchInputs cut (word cut.past.frame.raw actor)) =
      ⟨(attemptedWord cut.past.frame.raw actor).length,
        (law.execute cut.past.frame.raw 0 (attemptedWord cut.past.frame.raw actor)).final, submission⟩ := by
  have same := congrArg (fun items => items[(attemptedWord cut.past.frame.raw actor).length]?)
    (new_items cut (word cut.past.frame.raw actor))
  have bound : (attemptedWord cut.past.frame.raw actor).length <
      (financialItems fuel (branchInputs cut (word cut.past.frame.raw actor)) (cut.depth + 2)).length :=
    (signaturePosition cut actor).index.isLt
  rw [List.getElem?_eq_getElem bound] at same
  apply Option.some.inj
  apply same.trans
  unfold word RawLaw.rawItems
  rw [law.execute_append]
  simp only [RawLaw.execute, List.getElem?_append, law.inventory_length, Nat.lt_irrefl,
    if_false, Nat.sub_self, List.getElem?_cons_zero, Nat.zero_add]

def signature (cut : Cut fuel inputs) (actor : Bool) (held : cut.past.frame.raw.technology.holder = some actor) :
    Claim fuel (branchInputs cut (word cut.past.frame.raw actor)) :=
  let position := signaturePosition cut actor
  have found : (read fuel (branchInputs cut (word cut.past.frame.raw actor)) position).isSome = true := by
    unfold read
    have signed : isSubmission (position.item fuel _).request = true := by
      rw [signature_item]
      exact (isSubmission_iff _).mpr rfl
    have active : (position.item fuel _).before.technology.holder.isSome = true ∨
        (position.item fuel _).before.technology.offered.isSome = true := by
      left
      rw [signature_item, prefix_keeps_the_current_holder, held]
      rfl
    rw [dif_pos signed, dif_pos active]
    rfl
  (read fuel (branchInputs cut (word cut.past.frame.raw actor)) position).get found

theorem signature_is_actually_read (cut : Cut fuel inputs) (actor : Bool)
    (held : cut.past.frame.raw.technology.holder = some actor) :
    read fuel (branchInputs cut (word cut.past.frame.raw actor)) (signaturePosition cut actor) =
      some (signature cut actor held) := (Option.some_get _).symm

theorem signature_snapshot_is_after_the_actual_attempt (cut : Cut fuel inputs) (actor : Bool)
    (held : cut.past.frame.raw.technology.holder = some actor) :
    (signature cut actor held).snapshot =
      (law.execute cut.past.frame.raw 0 (attemptedWord cut.past.frame.raw actor)).final.technology := by
  have position := Response.read_position _ _ (signature_is_actually_read cut actor held)
  change ((signature cut actor held).position.item fuel _).before.technology = _
  rw [position, signature_item]

theorem every_refusal_stays_in_the_signed_word (current : Current) (actor : Bool)
    (refusal : Refusal current actor) :
    refusal.item ∈ law.rawItems current (word current actor) ∧ ¬ law.Valid refusal.item.before refusal.item.request := by
  refine ⟨?_, refusal.refused⟩
  unfold word attemptedWord RawLaw.rawItems
  rw [law.execute_append, law.execute_append]
  exact List.mem_append_left _ (List.mem_append_left _ refusal.actual)

theorem every_supply_is_in_the_signed_word (current : Current) (actor : Bool) (event : SupplyEvent current actor)
    (inside : event ∈ supplies current actor) : event.item ∈ law.rawItems current (word current actor) := by
  have actual := every_supply_is_in_the_original_word current actor event inside
  unfold word RawLaw.rawItems
  rw [law.execute_append]
  exact List.mem_append_left _ actual

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.Renewal
