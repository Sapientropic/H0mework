import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Regression
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Embedding.Regression

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 24000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.FinancialRegression

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle
open Followup
noncomputable section

abbrev ready := Regression.ready
def initialInventory := initial ready []
def financingWord : List Action :=
  [⟨false, [], .resource, [], .issue () false true 2⟩,
   ⟨true, [], .resource, [], .assign () false true false 2⟩]
def financed := submit ready initialInventory financingWord
def paymentWord : List Action :=
  [⟨false, [], .resource, [], .settle () false true 1⟩,
   ⟨false, [], .resource, [], .settle () false false 1⟩]
def paid := submit ready financed paymentWord

def debts {inputs : List (List Action)} (inventory : Inventory ready inputs) :=
  inventory.finance.current.slots.map fun slot =>
    ((Financial.Family.slotClaim Finance.sources slot).2.quantity,
      (Financial.Family.slotBalance Finance.sources slot) false,
      (Financial.Family.slotBalance Finance.sources slot) true)

theorem actual_new_issuance_and_assignment_retain_old_origin_and_original_principal :
    debts initialInventory = [(7, 0, 7)] ∧ debts financed = [(7, 2, 5), (2, 0, 2)] ∧
    ∀ item ∈ (epochLaw ready).rawItems (current ready initialInventory.inputs) financingWord,
      (epochLaw ready).Valid item.before item.request := by decide +kernel

theorem two_later_actual_payments_consume_the_saved_old_and_new_debt_inventory :
    debts paid = [(7, 1, 4), (2, 0, 2)] ∧
    (current ready paid.inputs).stock false .service = 2 ∧ (current ready paid.inputs).stock true .service = 1 ∧
    ∀ item ∈ (epochLaw ready).rawItems (current ready financed.inputs) paymentWord,
      (epochLaw ready).Valid item.before item.request := by decide +kernel

theorem all_actual_financial_addresses_have_their_native_shares :
    ∀ debtor holder : Bool,
      Financial.Family.ledgerClaims Finance.sources paid.finance.current () debtor holder =
        (current ready paid.inputs).claims () debtor holder := by decide +kernel

def refusedWord : List Action :=
  [⟨false, [], .resource, [], .assign () false true false 1⟩,
   ⟨false, [], .resource, [], .settle () false true 100⟩]
def refused := submit ready financed refusedWord

theorem false_assignment_and_unfunded_settlement_cannot_consume_the_saved_principal :
    debts refused = debts financed ∧
    refused.finance.current.history.map LifecycleEvent.kind = financed.finance.current.history.map LifecycleEvent.kind := by
  decide +kernel

theorem every_generated_inventory_has_the_complete_actual_matrix
    {originInputs : List (List Action)} (inventory : Inventory ready originInputs) :
    Financial.Family.ledgerClaims Finance.sources inventory.finance.current = (current ready inventory.inputs).claims :=
  financial_matrix_at_every_actual_cut ready inventory

def selfAssignmentWord : List Action := [⟨true, [], .resource, [], .assign () false true true 6⟩]
def selfAssigned := submit ready financed selfAssignmentWord

def selfAssignmentRemainders := (Finance.appendTrace ready financed.inputs selfAssignmentWord financed.finance).filterMap
  fun row => match row.result with
    | .movement _ allocation => some allocation.remaining
    | _ => none

theorem self_assignment_uses_one_quota_across_both_original_issues :
    debts selfAssigned = debts financed ∧ selfAssignmentRemainders = [0] ∧
    (selfAssigned.finance.current.history.drop financed.finance.current.history.length).map LifecycleEvent.kind =
      [.progressed, .progressed] := by decide +kernel

abbrev publicScopeJointFinancedFacade := ScopeJointRuntime.facade ready financed
abbrev publicScopeJointPaymentFacade := ScopeJointRuntime.facade ready paid
abbrev publicScopeJointFinancialRefusedFacade := ScopeJointRuntime.facade ready refused

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.FinancialRegression
