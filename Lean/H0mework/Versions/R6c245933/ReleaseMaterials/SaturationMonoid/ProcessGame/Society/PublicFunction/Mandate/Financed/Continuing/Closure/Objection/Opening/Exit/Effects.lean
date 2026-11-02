import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.Exit.Plan

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.Exit

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

theorem production_valid_iff_material (current : Current) (actor : Bool) :
    law.Valid current (production actor) ↔ 1 ≤ current.stock actor .feedstock := by
  simp [law, Mandate.law, production, RawLaw.Valid, RawLaw.SignerMatches, RawLaw.operationAllowed,
    RawPolicy.eval, RawLaw.requiredPorts, RawLaw.debit, RawLaw.credit, RawLaw.ClaimGuard,
    eraseCurrent, eraseRequest, eraseOperation, TaskUse, base, scope, task, Delegation.members,
    NonnegativeBundle, locate, flowAt, amount]

theorem exit_valid_iff_material (current : Current) (actor : Bool) (holder : current.technology.holder = some actor) :
    law.Valid current (request scope current actor .exit) ↔ 1 ≤ current.stock actor .service := by
  simp [law, Mandate.law, request, RawLaw.Valid, RawLaw.SignerMatches, RawLaw.operationAllowed,
    RawPolicy.eval, RawLaw.requiredPorts, RawLaw.debit, RawLaw.credit, RawLaw.ClaimGuard,
    Mandate.CanRun, advance, base, scope, task, Delegation.members, NonnegativeBundle,
    locate, flowAt, amount, holder]

theorem production_keeps_the_authority (current : Current) (actor : Bool) :
    (law.step current (production actor)).technology = current.technology := by
  unfold RawLaw.step
  split <;> rfl

def exitItem (current : Current) (actor : Bool) (method : Method) :
    ExecutionItem Bool Good Mandate.Source.Port (State Bool Unit) Unit :=
  ⟨1 + (method.prefix current actor).length, beforeExit current actor method,
    request scope (beforeExit current actor method) actor .exit⟩

theorem candidate_contains_its_actual_exit (current : Current) (actor : Bool) (method : Method) :
    exitItem current actor method ∈ law.rawItems current (candidate current actor method) := by
  cases method <;> simp [exitItem, beforeExit, candidate, signedWord, Method.prefix,
    RawLaw.rawItems, RawLaw.execute, submission_preserves_authority_and_stock]

theorem candidate_final_is_its_actual_exit (current : Current) (actor : Bool) (method : Method) :
    (law.execute current 0 (candidate current actor method)).final =
      law.step (beforeExit current actor method) (request scope (beforeExit current actor method) actor .exit) := by
  cases method <;> simp only [candidate, signedWord, Method.prefix, List.cons_append, List.nil_append,
    RawLaw.execute, submission_preserves_authority_and_stock, beforeExit]

theorem paid_word_retires_its_actual_holder (current : Current) (actor : Bool) (ready : Ready current actor)
    (chosen : choose current actor = some ready) :
    (law.execute current 0 (word current actor)).final.technology.holder = none ∧
    (law.execute current 0 (word current actor)).final.technology.offered = none := by
  rw [paid_core_has_no_repair_suffix current actor ready chosen, candidate_final_is_its_actual_exit]
  have accepted := ready.legal _ (candidate_contains_its_actual_exit current actor ready.method)
  have effect : (law.step (beforeExit current actor ready.method)
      (request scope (beforeExit current actor ready.method) actor .exit)).technology =
        advance scope (beforeExit current actor ready.method) .exit :=
    (Mandate.paid_command_effect base scope _ actor .exit accepted).1
  rw [effect]
  exact ⟨rfl, rfl⟩

private theorem productive_items (current : Current) (actor : Bool) :
    law.rawItems current (candidate current actor .productive) =
      [⟨0, current, submission⟩, ⟨1, current, production actor⟩,
       ⟨2, law.step current (production actor), request scope (law.step current (production actor)) actor .exit⟩] := by
  simp only [candidate, signedWord, Method.prefix, beforeExit,
    submission_preserves_authority_and_stock, List.cons_append, List.nil_append, RawLaw.rawItems, RawLaw.execute]

private theorem productive_refusal_has_material_gap (current : Current) (actor : Bool)
    (holder : current.technology.holder = some actor)
    (item : ExecutionItem Bool Good Mandate.Source.Port (State Bool Unit) Unit)
    (actual : item ∈ law.rawItems current (candidate current actor .productive))
    (refused : ¬ law.Valid item.before item.request) :
    ∃ debit ∈ law.debit item.before item.request, 0 < debit.2 - item.before.stock debit.1.1 debit.1.2 := by
  rw [productive_items] at actual
  simp only [List.mem_cons, List.not_mem_nil, or_false] at actual
  rcases actual with same | same | same
  · subst item; exact False.elim (refused (submission_valid current))
  · subst item
    refine ⟨((actor, .feedstock), 1), ?_, sub_pos.mpr (lt_of_not_ge (fun enough => refused ((production_valid_iff_material _ _).mpr enough)))⟩
    simp [law, Mandate.law, RawLaw.debit, production, base, locate]
  · subst item
    have kept : (law.step current (production actor)).technology.holder = some actor := by rw [production_keeps_the_authority, holder]
    refine ⟨((actor, .service), 1), ?_, sub_pos.mpr (lt_of_not_ge (fun enough => refused ((exit_valid_iff_material _ _ kept).mpr enough)))⟩
    simp [law, Mandate.law, RawLaw.debit, request, base, scope, locate]

theorem blocked_holder_has_a_positive_repair (current : Current) (actor : Bool)
    (holder : current.technology.holder = some actor) (blocked : choose current actor = none) :
    ∃ demand, demand ∈ demands current actor := by
  have notLegal : ¬ Legal current actor .productive := by
    unfold choose at blocked
    split at blocked
    · cases blocked
    · rename_i absent
      intro legal
      have denied := List.find?_eq_none.mp absent .productive (by simp [methods])
      have accepted : decide (Legal current actor .productive) = true := decide_eq_true legal
      rw [accepted] at denied
      exact denied rfl
  have invalid : ∃ item ∈ law.rawItems current (candidate current actor .productive), ¬ law.Valid item.before item.request := by
    by_contra none
    apply notLegal
    intro item included
    by_contra refused
    exact none ⟨item, included, refused⟩
  obtain ⟨item, actual, refused⟩ := invalid
  obtain ⟨debit, required, shortfall⟩ := productive_refusal_has_material_gap current actor holder item actual refused
  have inCore : item ∈ law.rawItems current (core current actor) := by simpa only [core, selected, blocked] using actual
  obtain ⟨demand, present, _⟩ := every_positive_refusal_is_recorded current actor item inCore refused debit required shortfall
  exact ⟨demand, present⟩

theorem word_is_its_core_and_repairs (current : Current) (actor : Bool) :
    word current actor = core current actor ++ repairs current actor := rfl

def suffix (current : Current) (actor : Bool) :=
  ((selected current actor).prefix current actor ++ [request scope (beforeExit current actor (selected current actor)) actor .exit]) ++
    repairs current actor

theorem word_is_signed (current : Current) (actor : Bool) :
    word current actor = signedWord (suffix current actor) := by
  simp only [word, core, candidate, suffix, signedWord, List.cons_append]

theorem Demand.supplier_is_distinct {current : Current} {actor : Bool} (demand : Demand current actor) :
    demand.supplier ≠ demand.debit.1.1 := by
  cases same : demand.debit.1.1 <;> simp_all [Demand.supplier]

theorem supply_valid_iff_material {current : Current} {actor : Bool} (demand : Demand current actor) (before : Current) :
    law.Valid before demand.request ↔ demand.quantity ≤ before.stock demand.supplier demand.debit.1.2 := by
  have positive := le_of_lt demand.shortfall
  simp [law, Mandate.law, Demand.request, RawLaw.Valid, RawLaw.SignerMatches,
    RawLaw.operationAllowed, RawPolicy.eval, RawLaw.requiredPorts, RawLaw.debit, RawLaw.credit,
    RawLaw.ClaimGuard, eraseCurrent, eraseRequest, eraseOperation, TaskUse, base, scope, task,
    Delegation.members, NonnegativeBundle, locate, flowAt, amount, positive, Demand.quantity]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.Exit
