import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Followup.Joint.Runtime

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Institutions.Capitalism.Universal.Source.ProgrammeFace
open Followup

variable {fuel : ℚ} {inputs : List (List Action)}

def signedWord (suffix : List Action) := submission :: suffix

theorem new_items (cut : Cut fuel inputs) (word : List Action) :
    financialItems fuel (branchInputs cut word) (cut.depth + 2) = law.rawItems cut.past.frame.raw word := by
  change law.rawItems (actualExecution fuel (branchInputs cut word) (cut.depth + 1)).before
    (actualExecution fuel (branchInputs cut word) (cut.depth + 1)).submitted = _
  rw [new_input_uses_the_original_cut, new_input_is_actually_emitted]

def signaturePosition (cut : Cut fuel inputs) (suffix : List Action) : Position fuel (branchInputs cut (signedWord suffix)) :=
  ⟨cut.depth + 2, ⟨0, by
    change 0 < (financialItems fuel (branchInputs cut (signedWord suffix)) (cut.depth + 2)).length
    rw [new_items]
    simp only [signedWord, RawLaw.rawItems, RawLaw.execute, List.length_cons]
    omega⟩⟩

theorem signature_item (cut : Cut fuel inputs) (suffix : List Action) :
    (signaturePosition cut suffix).item fuel (branchInputs cut (signedWord suffix)) = ⟨0, cut.past.frame.raw, submission⟩ := by
  have same := congrArg (fun items => items[0]?) (new_items cut (signedWord suffix))
  have bound : 0 < (financialItems fuel (branchInputs cut (signedWord suffix)) (cut.depth + 2)).length :=
    (signaturePosition cut suffix).index.isLt
  rw [List.getElem?_eq_getElem bound] at same
  apply Option.some.inj
  exact same.trans (by simp only [signedWord, RawLaw.rawItems, RawLaw.execute, List.getElem?_cons_zero])

def signature (cut : Cut fuel inputs) (suffix : List Action) (active : Mandate.Response.Active cut.past.frame.raw) :
    Claim fuel (branchInputs cut (signedWord suffix)) :=
  let position := signaturePosition cut suffix
  have found : (read fuel (branchInputs cut (signedWord suffix)) position).isSome = true := by
    unfold read
    have signed : isSubmission (position.item fuel (branchInputs cut (signedWord suffix))).request = true := by
      rw [signature_item]
      exact (isSubmission_iff _).mpr rfl
    have current : (position.item fuel (branchInputs cut (signedWord suffix))).before.technology.holder.isSome = true ∨
        (position.item fuel (branchInputs cut (signedWord suffix))).before.technology.offered.isSome = true := by
      rw [signature_item]
      exact active
    rw [dif_pos signed, dif_pos current]
    rfl
  (read fuel (branchInputs cut (signedWord suffix)) position).get found

theorem signature_is_actually_read (cut : Cut fuel inputs) (suffix : List Action)
    (active : Mandate.Response.Active cut.past.frame.raw) :
    read fuel (branchInputs cut (signedWord suffix)) (signaturePosition cut suffix) = some (signature cut suffix active) :=
  (Option.some_get _).symm

theorem signature_snapshot_is_the_actual_cut (cut : Cut fuel inputs) (suffix : List Action)
    (active : Mandate.Response.Active cut.past.frame.raw) :
    (signature cut suffix active).snapshot = cut.past.frame.raw.technology := by
  have position := Response.read_position _ _ (signature_is_actually_read cut suffix active)
  change ((signature cut suffix active).position.item fuel _).before.technology = _
  rw [position, signature_item]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening
