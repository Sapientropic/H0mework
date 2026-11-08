import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.Stop
import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Civil.Consumers.Receipt

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.Consumers

open Conflict.Consumers.Evolving
open Conflict.Civil.Consumers

noncomputable section

private theorem quiet_of_empty_m11 (word : W)
    (clear : (Boundary.spaceAt opening word id).boundaryCertificates.length = 0) :
    ¬ Nonempty (Boundary.AggressionAt opening word id) := by
  rintro ⟨attack⟩
  have listed := attack.listed
  rw [List.length_eq_zero_iff.mp clear] at listed
  exact List.not_mem_nil listed

theorem the_original_civilian_action_stops_m11_aggression_and_pays_exit :
    ∃ success, inspectStop opening id command task intervention calm exit [conflict, peace] =
      .stopped success := by
  have quiet : ¬ Nonempty (Boundary.AggressionAt opening (intervention ++ peace) id) := by
    apply quiet_of_empty_m11
    change (Boundary.sourceCrossings opening.native.input.law (opening.raw, intervention ++ peace)
      id).boundaryCertificates.length = 0
    rw [sourceInput, sourceRead]
    decide +kernel
  have exitQuiet : ¬ Nonempty (Boundary.AggressionAt opening ((intervention ++ calm) ++ exit) id) := by
    apply quiet_of_empty_m11
    change (Boundary.sourceCrossings opening.native.input.law (opening.raw, (intervention ++ calm) ++ exit)
      id).boundaryCertificates.length = 0
    rw [sourceInput, sourceRead]
    decide +kernel
  have stopped : ProtectedStop opening id command task intervention calm exit [conflict, peace] := by
    refine ⟨the_investment_is_the_citizens_own_action, ?_,
      the_citizen_keeps_and_spends_her_original_independent_exit, exitQuiet⟩
    intro word listed
    simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
    rcases listed with rfl | rfl
    · rintro ⟨capture⟩
      exact the_original_attack_cannot_requisition_the_spent_stock capture.paid
    · exact quiet
  exact ⟨stopped, inspectStop_returns_each_protected_stop stopped⟩

theorem the_reordered_funding_is_a_genuine_m11_bypass :
    Nonempty (Boundary.AggressionAt opening (intervention ++ routedAttack) id) := by
  have positive : 0 < (Boundary.spaceAt opening (intervention ++ routedAttack) id).boundaryCertificates.length := by
    change 0 < (Boundary.sourceCrossings opening.native.input.law (opening.raw, intervention ++ routedAttack)
      id).boundaryCertificates.length
    rw [sourceInput, sourceRead]
    decide +kernel
  let certificates := (Boundary.spaceAt opening (intervention ++ routedAttack) id).boundaryCertificates
  let exact := certificates[0]
  exact ⟨Boundary.AggressionAt.ofPaidBoundary a_differently_financed_attack_is_an_actual_bypass exact
    (List.getElem_mem positive)⟩

theorem admitting_the_reordered_funding_rules_out_a_civilian_stop :
    ¬ ProtectedStop opening id command task intervention calm exit [conflict, peace, routedAttack] := by
  intro stopped
  exact stopped.stopped routedAttack (by simp) the_reordered_funding_is_a_genuine_m11_bypass

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.Consumers
