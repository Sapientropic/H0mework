import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Settlement.Runtime
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.FinancialRegression

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 24000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Settlement.Regression

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle
open Followup
noncomputable section

abbrev ready := FinancialRegression.ready
abbrev financed := FinancialRegression.financed
def debts {inputs : List (List Action)} (inventory : Inventory ready inputs) := FinancialRegression.debts inventory

def once := advance ready financed
def twice := advance ready once
def thrice := advance ready twice

theorem saved_old_and_new_shares_generate_both_actual_payment_addresses :
    Joint.emit ready financed = [] ∧
    (positions ready financed).map (fun position => (position.debtor, position.creditor)) =
      [(false, false), (false, true)] ∧
    (emit ready financed).length = 2 ∧
    ∀ item ∈ (epochLaw ready).rawItems (current ready financed.inputs) (emit ready financed),
      (epochLaw ready).Valid item.before item.request := by decide +kernel

theorem repeated_actual_settlement_consumes_both_original_issues :
    debts once = [(7, 0, 2), (2, 0, 2)] ∧
    debts twice = [(7, 0, 0), (2, 0, 1)] ∧
    debts thrice = [(7, 0, 0), (2, 0, 0)] ∧
    (current ready thrice.inputs).stock false .feedstock = 1 ∧
    (current ready thrice.inputs).stock false .service = 2 ∧
    (current ready thrice.inputs).stock true .service = 7 ∧
    emit ready thrice = [] := by decide +kernel

def drainWord : List Action :=
  [⟨false, [], .resource, [], .use false [(.service, 3)] .external⟩,
   ⟨false, [], .resource, [], .transfer false true [(.feedstock, 3)]⟩]
def drained := submit ready FinancialRegression.initialInventory drainWord
def supplied := advance ready drained
def resumed := advance ready supplied

theorem actual_material_shortfall_generates_refusal_then_a_paid_repair_request :
    (∀ item ∈ (epochLaw ready).rawItems (current ready FinancialRegression.initialInventory.inputs) drainWord,
      (epochLaw ready).Valid item.before item.request) ∧
    (current ready drained.inputs).stock false .feedstock = 0 ∧
    (current ready drained.inputs).stock true .feedstock = 3 ∧
    (current ready drained.inputs).stock false .service = 0 ∧
    Repayment.Portfolio.Repair.kind (epochLaw ready) position (afterPrefix ready drained) = .blocked ∧
    (emit ready drained).length = 3 ∧
    (Repayment.Portfolio.Repair.orders (epochLaw ready) position (afterPrefix ready drained)).length = 1 ∧
    debts supplied = debts drained ∧
    (current ready supplied.inputs).stock false .feedstock = 1 := by decide +kernel

theorem the_next_saved_inventory_uses_actual_repair_material_to_pay :
    Repayment.Portfolio.Repair.kind (epochLaw ready) position (afterPrefix ready supplied) = .paid ∧
    debts resumed = [(7, 0, 4)] ∧
    (current ready resumed.inputs).stock false .feedstock = 0 ∧
    (current ready resumed.inputs).stock true .service = 3 := by decide +kernel

abbrev exhausted := Joint.Regression.exhausted

theorem an_unfunded_repair_request_cannot_clear_the_original_debt_or_objection :
    Repayment.Portfolio.Repair.kind (epochLaw ready) position (afterPrefix ready exhausted) = .blocked ∧
    debts (advance ready exhausted) = debts exhausted ∧
    (current ready (advance ready exhausted).inputs).technology.holder = some true ∧
    (advance ready exhausted).objections.length = exhausted.objections.length ∧
    ¬ (∀ item ∈ (epochLaw ready).rawItems (current ready exhausted.inputs) (emit ready exhausted),
      (epochLaw ready).Valid item.before item.request) := by decide +kernel

theorem the_original_snapshot_response_and_native_grants_survive_the_payment_suffix :
    Joint.emit ready Joint.Regression.shifted ≠ [] ∧
    (advance ready Joint.Regression.shifted).grants.length = Joint.Regression.shifted.grants.length ∧
    (current ready (advance ready Joint.Regression.shifted).inputs).technology.holder = none ∧
    (advance ready Joint.Regression.shifted).objections.length = 2 := by decide +kernel

abbrev publicScopeSettlementPaidFacade := Runtime.facade ready financed
abbrev publicScopeSettlementRepairFacade := Runtime.facade ready drained
abbrev publicScopeSettlementResumedFacade := Runtime.facade ready supplied
abbrev publicScopeSettlementRefusedFacade := Runtime.facade ready exhausted

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Settlement.Regression
