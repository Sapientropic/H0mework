import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.Signature

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Institutions.Capitalism.Universal.Source.ProgrammeFace
open Followup

variable {fuel : ℚ}

def firstIndex (inventory : Joint.Inventory fuel) (suffix : List Action) :
    Fin (Joint.actualEvents inventory.cut (signedWord suffix)).length :=
  ⟨0, by
    have bound : 0 < (financialItems fuel (branchInputs inventory.cut (signedWord suffix)) (inventory.cut.depth + 2)).length :=
      (signaturePosition inventory.cut suffix).index.isLt
    simpa only [Joint.actualEvents, List.length_map, List.length_finRange] using bound⟩

theorem first_event_is_the_signature_position (inventory : Joint.Inventory fuel) (suffix : List Action) :
    ((Joint.actualEvents inventory.cut (signedWord suffix)).get (firstIndex inventory suffix)).val =
      signaturePosition inventory.cut suffix := by
  let count := (financialItems fuel (branchInputs inventory.cut (signedWord suffix)) (inventory.cut.depth + 2)).length
  have positive : 0 < count := (signaturePosition inventory.cut suffix).index.isLt
  have bound : 0 < (List.finRange count).length := by
    simpa only [List.length_finRange] using positive
  have mappedBound : 0 < ((List.finRange count).map (Joint.actualEvent inventory.cut (signedWord suffix))).length := by
    simpa only [List.length_map] using bound
  change (((List.finRange count).map (Joint.actualEvent inventory.cut (signedWord suffix)))[0]'mappedBound).val = _
  rw [List.getElem_map]
  change (⟨inventory.cut.depth + 2, (List.finRange count)[0]'bound⟩ : Position fuel _) = _
  apply congrArg (fun index : Fin count => (⟨inventory.cut.depth + 2, index⟩ : Position fuel _))
  apply Fin.ext
  simp only [List.getElem_finRange]
  rfl

theorem actual_signature_is_consumed_as_continuation_or_new_native_admission
    (inventory : Joint.Inventory fuel) (suffix : List Action) (active : Mandate.Response.Active inventory.cut.past.frame.raw) :
    ((Joint.decisionAt inventory (signedWord suffix) (firstIndex inventory suffix)).mode = .continued ∧
      (∃ row ∈ (Joint.frameBefore inventory (signedWord suffix) 0).rows,
        row.canReconfirm ((Joint.actualEvents inventory.cut (signedWord suffix)).get (firstIndex inventory suffix)) = true) ∧
      (Joint.decisionAt inventory (signedWord suffix) (firstIndex inventory suffix)).newborn = none) ∨
    ((Joint.decisionAt inventory (signedWord suffix) (firstIndex inventory suffix)).mode = .admitted ∧
      (Joint.newbornAt inventory (signedWord suffix) (firstIndex inventory suffix)).isSome = true) := by
  apply Joint.every_actual_new_signature_has_a_joint_disposition inventory (signedWord suffix) (firstIndex inventory suffix)
    (signature inventory.cut suffix active)
  rw [first_event_is_the_signature_position]
  exact signature_is_actually_read inventory.cut suffix active

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening
