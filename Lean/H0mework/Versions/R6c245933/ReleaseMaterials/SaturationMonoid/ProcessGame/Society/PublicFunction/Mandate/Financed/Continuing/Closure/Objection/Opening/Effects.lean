import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.Resource

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

def revokeBefore (current : Current) (method : Method) := (law.execute current 0 (method.prefix current)).final

def revokeItem (current : Current) (method : Method) : ExecutionItem Bool Good Mandate.Source.Port (State Bool Unit) Unit :=
  ⟨1 + (method.prefix current).length, revokeBefore current method, request scope (revokeBefore current method) false .revoke⟩

theorem candidate_contains_its_actual_revoke (current : Current) (method : Method) :
    revokeItem current method ∈ law.rawItems current (candidate current method) := by
  cases method <;> simp [revokeItem, revokeBefore, candidate, signedWord, Response.Method.word,
    Response.Method.prefix, RawLaw.rawItems, RawLaw.execute, submission_preserves_authority_and_stock]

theorem candidate_final_is_its_actual_revoke (current : Current) (method : Method) :
    (law.execute current 0 (candidate current method)).final =
      law.step (revokeBefore current method) (request scope (revokeBefore current method) false .revoke) := by
  cases method <;> simp only [candidate, signedWord, Response.Method.word, Response.Method.prefix,
    List.cons_append, List.nil_append, RawLaw.execute, submission_preserves_authority_and_stock, revokeBefore]

theorem a_paid_candidate_retires_the_actual_authority (current : Current) (method : Method)
    (legal : Legal current method) :
    (law.execute current 0 (candidate current method)).final.technology.holder = none ∧
    (law.execute current 0 (candidate current method)).final.technology.offered = none := by
  have accepted := legal (revokeItem current method) (candidate_contains_its_actual_revoke current method)
  have effect := Mandate.paid_command_effect base scope (revokeBefore current method) false .revoke accepted
  rw [candidate_final_is_its_actual_revoke]
  have technology : (law.step (revokeBefore current method)
      (request scope (revokeBefore current method) false .revoke)).technology =
      advance scope (revokeBefore current method) .revoke := effect.1
  rw [technology]
  exact ⟨rfl, rfl⟩

theorem a_paid_selected_word_retires_the_actual_authority (current : Current)
    (paid : (select current).isPaid = true) :
    (law.execute current 0 (word current)).final.technology.holder = none ∧
    (law.execute current 0 (word current)).final.technology.offered = none := by
  rw [a_paid_plan_has_no_unpaid_repair_suffix current paid]
  have legal : Legal current (select current).method := by
    generalize chosen : select current = selection at paid ⊢
    cases selection
    next method included legal => exact legal
    next refused => cases paid
  exact a_paid_candidate_retires_the_actual_authority current _ legal

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening
