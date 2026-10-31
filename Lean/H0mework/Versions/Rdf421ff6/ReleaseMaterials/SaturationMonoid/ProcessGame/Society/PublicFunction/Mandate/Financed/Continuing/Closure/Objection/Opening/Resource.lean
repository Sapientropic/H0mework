import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.Plan

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

private theorem nonrevision_step (current : Current) (action : Action)
    (plain : ∀ operator target, action.operation ≠ .revise operator target) :
    (law.step current action).technology = current.technology := by
  unfold RawLaw.step
  split
  · cases operation : action.operation <;> simp only [RawLaw.paidStep, operation]
    exact False.elim (plain _ _ operation)
  · rfl

theorem method_prefix_keeps_the_signed_snapshot (current : Current) (method : Method) :
    (law.execute current 0 (method.prefix current)).final.technology = current.technology := by
  cases method with
  | direct => rfl
  | productive => exact nonrevision_step _ _ (by intros; simp [Response.production])
  | loan lender =>
      let issued : Action := ⟨false, [], .resource, [], .issue () false lender (Response.principal current)⟩
      let payout : Action := ⟨lender, [], .resource, [], .transfer lender false [(.service, Response.principal current)]⟩
      exact (nonrevision_step (law.step current issued) payout (by intros; simp [payout])).trans
        (nonrevision_step current issued (by intros; simp [issued]))

theorem method_prefix_final_ignores_item_index (current : Current) (method : Method) (index : Nat) :
    (law.execute current index (method.prefix current)).final = (law.execute current 0 (method.prefix current)).final := by
  cases method <;> rfl

theorem production_valid_iff_material (current : Current) :
    law.Valid current Response.production ↔ 1 ≤ current.stock false .feedstock := by
  simp [law, Mandate.law, Response.production, RawLaw.Valid, RawLaw.SignerMatches, RawLaw.operationAllowed,
    RawPolicy.eval, RawLaw.requiredPorts, RawLaw.debit, RawLaw.credit, RawLaw.ClaimGuard, eraseCurrent,
    eraseRequest, eraseOperation, TaskUse, base, scope, task, Delegation.members, NonnegativeBundle,
    locate, flowAt, amount]

theorem revoke_valid_iff_material (current : Current) (active : Mandate.Response.Active current) :
    law.Valid current (request scope current false .revoke) ↔ 1 ≤ current.stock false .service := by
  simp [law, Mandate.law, request, RawLaw.Valid, RawLaw.SignerMatches, RawLaw.operationAllowed,
    RawPolicy.eval, RawLaw.requiredPorts, RawLaw.debit, RawLaw.credit, RawLaw.ClaimGuard, Mandate.CanRun, advance,
    base, scope, task, Delegation.members, NonnegativeBundle, locate, flowAt, amount,
    Mandate.Response.Active] at active ⊢
  exact fun _ => active

theorem supply_valid_iff_material {current : Current} (demand : Demand current) (before : Current) :
    law.Valid before demand.request ↔ demand.quantity ≤ before.stock demand.supplier demand.debit.1.2 := by
  have positive := le_of_lt demand.shortfall
  simp [law, Mandate.law, Demand.request, Demand.requestTo, RawLaw.Valid, RawLaw.SignerMatches,
    RawLaw.operationAllowed, RawPolicy.eval, RawLaw.requiredPorts, RawLaw.debit, RawLaw.credit,
    RawLaw.ClaimGuard, eraseCurrent, eraseRequest, eraseOperation, TaskUse, base, scope, task,
    Delegation.members, NonnegativeBundle, locate, flowAt, amount, positive, Demand.quantity]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening
