import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Instances.UBI.Source
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option maxRecDepth 4096

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Instances.UBI

open Source.Program

private theorem base_exact : (law.execute (state 0 0) 0 body).final = state 0 0 := by
  apply RawCurrent.ext
  · funext party good
    cases party <;> cases good <;> decide +kernel
  · funext instrument debtor creditor
    cases instrument
    cases debtor <;> cases creditor <;> decide +kernel
  · exact Subsingleton.elim _ _
  · decide +kernel
  · decide +kernel

private theorem base_accepted : ∀ item ∈ law.rawItems (state 0 0) body,
    law.Valid item.before item.request := by
  simp only [RawLaw.rawItems, body, RawLaw.execute, List.forall_mem_cons,
    List.not_mem_nil, false_implies, implies_true, and_true]
  decide +kernel

theorem whole_body_exact (clock : ℚ) (round : Nat) :
    (law.execute (state clock round) 0 body).final = state clock round := by
  change (law.execute ((state 0 0).retime clock round) 0 body).final = _
  rw [law.execute_retime time_independent, base_exact]
  rfl

theorem whole_body_accepted (clock : ℚ) (round : Nat) :
    ∀ item ∈ law.rawItems (state clock round) body, law.Valid item.before item.request :=
  (law.accepted_retime time_independent (state 0 0) clock round 0 body).mpr base_accepted

theorem actual_next (clock : ℚ) (round : Nat) :
    law.next (state clock round) body = state (clock + 1) (round + 1) := by
  unfold RawLaw.next
  rw [whole_body_exact]
  simp [law, state]

theorem currentAt_exact (n : Nat) : program.currentAt n = state (n : ℚ) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change program.tick (program.currentAt n) = _
      rw [ih]
      change law.next (state (n : ℚ) n) body = _
      rw [actual_next]
      simp

theorem every_round_is_actual (n : Nat) :
    ∀ item ∈ law.rawItems (program.currentAt n) body, law.Valid item.before item.request := by
  rw [currentAt_exact]
  exact whole_body_accepted _ _

theorem every_submitted_request_is_actual (n : Nat) (request : Input) (member : request ∈ body) :
    ∃ item ∈ law.rawItems (program.currentAt n) body,
      item.request = request ∧ law.Valid item.before item.request := by
  have original : request ∈ (law.rawItems (program.currentAt n) body).map ExecutionItem.request := by
    rw [RawLaw.rawItems, RawLaw.inventory_requests_exact]
    exact member
  obtain ⟨item, inside, same⟩ := List.mem_map.mp original
  exact ⟨item, inside, same, every_round_is_actual n item inside⟩

theorem periodic_grant_has_actual_purchasing_power (n : Nat) :
    (∃ item ∈ law.rawItems (program.currentAt n) body,
      item.request = grant ∧ law.Valid item.before item.request) ∧
    (∃ item ∈ law.rawItems (program.currentAt n) body,
      item.request = redeem ∧ law.Valid item.before item.request ∧
        item.request.signer = true ∧ item.request.consents = [] ∧
        flowAt (law.actualCredit item.before item.request) true () = 1) ∧
    (∃ item ∈ law.rawItems (program.currentAt n) body,
      item.request = consume ∧ law.Valid item.before item.request ∧
        flowAt (law.actualDebit item.before item.request) true () = 1) := by
  have issued := every_submitted_request_is_actual n grant (by simp [body])
  obtain ⟨payment, paymentMember, paymentKind, paymentLegal⟩ :=
    every_submitted_request_is_actual n redeem (by simp [body])
  obtain ⟨need, needMember, needKind, needLegal⟩ :=
    every_submitted_request_is_actual n consume (by simp [body])
  refine ⟨issued, ⟨payment, paymentMember, paymentKind, paymentLegal, ?_, ?_, ?_⟩,
    ⟨need, needMember, needKind, needLegal, ?_⟩⟩
  · rw [paymentKind]; rfl
  · rw [paymentKind]; rfl
  · simp only [RawLaw.actualCredit, if_pos paymentLegal]
    norm_num [RawLaw.credit, paymentKind, redeem, flowAt, amount, locate, law]
  · simp only [RawLaw.actualDebit, if_pos needLegal]
    simp [RawLaw.debit, needKind, consume, flowAt, amount, locate]

theorem no_employment_or_contribution_condition :
    (body.filter (fun request => match request.operation with
      | .transfer .. | .use _ _ .contribution => true
      | .produce member => member
      | _ => false)).length = 0 := by decide +kernel

#print axioms periodic_grant_has_actual_purchasing_power
#print axioms currentAt_exact
#print axioms no_employment_or_contribution_condition

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Instances.UBI
