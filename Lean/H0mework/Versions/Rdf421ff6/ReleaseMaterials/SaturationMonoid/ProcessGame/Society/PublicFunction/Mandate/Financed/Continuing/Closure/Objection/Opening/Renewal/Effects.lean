import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.Renewal.Plan

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.Renewal

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

def material (action : Action) : Bool :=
  match action.operation with | .revise _ _ => false | _ => true

theorem material_step_keeps_authority (current : Current) (action : Action)
    (plain : material action = true) : (law.step current action).technology = current.technology := by
  unfold RawLaw.step
  split
  · cases operation : action.operation <;> simp_all [RawLaw.paidStep, material]
  · rfl

theorem material_execution_keeps_authority (current : Current) (index : Nat) (word : List Action)
    (plain : ∀ action ∈ word, material action = true) :
    (law.execute current index word).final.technology = current.technology := by
  induction word generalizing current index with
  | nil => rfl
  | cons action tail ih =>
      change (law.execute (law.step current action) (index + 1) tail).final.technology = _
      rw [ih _ _ (fun item inside => plain item (List.mem_cons_of_mem _ inside))]
      exact material_step_keeps_authority current action (plain action List.mem_cons_self)

theorem funding_is_material (current : Current) (needs : List (Bool × ℚ)) :
    ∀ action ∈ funding current needs, material action = true := by
  induction needs generalizing current with
  | nil => simp only [funding, List.not_mem_nil, false_implies, implies_true]
  | cons need tail ih =>
      intro action inside
      simp only [funding, List.mem_append] at inside
      rcases inside with front | back
      · dsimp only [fund] at front
        split at front
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at front
          rcases front with rfl | rfl <;> rfl
        · cases front
      · exact ih _ action back

theorem prefix_is_material (current : Current) (actor : Bool) (method : Method) :
    ∀ action ∈ method.prefix current actor, material action = true := by
  cases method with
  | direct => simp [Method.prefix]
  | productive =>
      intro action inside
      simp only [Method.prefix, List.mem_append, List.mem_singleton] at inside
      rcases inside with rfl | other
      · rfl
      · split at other
        · cases other
        · simp only [List.mem_singleton] at other
          subst action
          rfl
  | financed => exact funding_is_material _ _

theorem before_proposal_is_the_same_authority (current : Current) (actor : Bool) (method : Method) :
    (beforeProposal current actor method).technology = current.technology :=
  material_execution_keeps_authority _ _ _ (prefix_is_material current actor method)

theorem command_keeps_holder (current : Current) (signer : Bool) (command : Command Bool)
    (kind : command = .propose signer ∨ command = .renew ∨ ∃ candidate, command = .propose candidate) :
    (law.step current (request scope current signer command)).technology.holder = current.technology.holder := by
  unfold RawLaw.step
  split
  · rcases kind with rfl | rfl | ⟨candidate, rfl⟩ <;> rfl
  · rfl

theorem core_keeps_the_current_holder (current : Current) (actor : Bool) :
    (law.execute current 0 (core current actor)).final.technology.holder = current.technology.holder := by
  unfold core candidate
  rw [law.execute_append]
  simp only [RawLaw.execute]
  change (law.step (beforeRenewal current actor (selected current actor))
    (renewal current actor (selected current actor))).technology.holder = _
  unfold renewal
  rw [command_keeps_holder _ actor .renew (Or.inr (Or.inl rfl))]
  unfold beforeRenewal proposal
  rw [command_keeps_holder _ sponsor (.propose actor) (Or.inr (Or.inr ⟨actor, rfl⟩))]
  exact congrArg State.holder (before_proposal_is_the_same_authority current actor _)

theorem paid_renewal_is_a_real_second_command (current : Current) (actor : Bool)
    (ready : Ready current actor) :
    law.Valid (beforeRenewal current actor ready.method) (renewal current actor ready.method) :=
  ready.legal _ (renewal_is_a_real_item current actor ready.method)

theorem paid_renewal_advances_the_actual_authority (current : Current) (actor : Bool)
    (ready : Ready current actor) :
    (law.step (beforeRenewal current actor ready.method) (renewal current actor ready.method)).technology =
      Mandate.advance scope (beforeRenewal current actor ready.method) .renew :=
  (paid_command_effect base scope _ actor .renew (paid_renewal_is_a_real_second_command current actor ready)).1

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.Renewal
