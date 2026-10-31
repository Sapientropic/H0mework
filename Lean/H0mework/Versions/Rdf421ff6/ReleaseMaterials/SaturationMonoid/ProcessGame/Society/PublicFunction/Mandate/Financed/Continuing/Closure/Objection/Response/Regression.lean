import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Response.Runtime
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Regression

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Response.Regression

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle
open ResponseRuntime

noncomputable section

def productive := Objection.Regression.challenged

def drain (current : Current) : Action :=
  ⟨false, [], .resource, [], .transfer false true [(.service, current.stock false .service)]⟩

def financedFirst := start 0 []
def financed := afterInput financedFirst [drain financedFirst.past.frame.raw, submission]

def emptyWord (fuel : ℚ) : List Action :=
  let before := (start fuel []).past.frame.raw
  let move : Action := ⟨false, [], .resource, [], .transfer false true [(.feedstock, before.stock false .feedstock)]⟩
  let cash := drain (law.step before move)
  let after := law.step (law.step before move) cash
  let consume : Action := ⟨true, [], .resource, [], .use true [(.service, after.stock true .service)] .external⟩
  [move, cash, consume, submission]

def repair := afterInput (start 1 []) (emptyWord 1)
def blocked := afterInput (start 0 []) (emptyWord 0)

def isCurrent {fuel : ℚ} {inputs : List (List Action)} {cut : Cut fuel inputs} : Decision cut → Bool
  | .current .. => true | _ => false

def isShifted {fuel : ℚ} {inputs : List (List Action)} {cut : Cut fuel inputs} : Decision cut → Bool
  | .shifted .. => true | _ => false

def selected {fuel : ℚ} {inputs : List (List Action)} (cut : Cut fuel inputs) : Option Method :=
  (choose cut.past.frame.raw).map Ready.method

def firstPending {fuel : ℚ} {inputs : List (List Action)} (cut : Cut fuel inputs)
    (present : (pending cut).isSome = true) := (pending cut).get present

def productivePending := firstPending productive (by decide +kernel)
def financedPending := firstPending financed (by decide +kernel)
def repairPending := firstPending repair (by decide +kernel)
def blockedPending := firstPending blocked (by decide +kernel)
def repairedPending := firstPending (nextCut repair) (by decide +kernel)

def kinds {fuel : ℚ} {inputs : List (List Action)} (cut : Cut fuel inputs) (original : Pending cut) :=
  (newAfter cut original).state.current.history.map LifecycleEvent.kind

theorem native_residual_generates_and_executes_paid_local_production :
    productive.past.frame.raw.stock false .service = 0 ∧
    isCurrent (decideAt productive) = true ∧ selected productive = some .productive ∧
    (emit productive).length = 2 ∧ (nextCut productive).past.frame.raw.technology.holder = none ∧
    (nextCut productive).past.frame.raw.stock false .feedstock = 2 ∧
    (nextCut productive).past.frame.raw.stock false .service = 2 ∧
    kinds productive productivePending = [.admitted, .obligationTerminal] := by decide +kernel

theorem native_residual_generates_actual_loan_payout_and_revoke :
    financed.past.frame.raw.stock false .feedstock = 0 ∧
    financed.past.frame.raw.stock false .service = 0 ∧
    selected financed = some (.loan true) ∧ (actualFunding financed).isSome = true ∧
    (nextCut financed).past.frame.raw.technology.holder = none ∧
    (nextCut financed).past.frame.raw.stock false .service = 0 ∧
    (nextCut financed).past.frame.raw.claims () false true = 8 ∧
    kinds financed financedPending = [.admitted, .obligationTerminal] ∧
    (Financial.accountAt (ResponseRuntime.I financed) (financed.depth + 3)).current.slots.map
      (fun slot => (Financial.slotClaim _ slot).quantity) = [7, 1] := by decide +kernel

theorem blocked_candidate_emits_and_receives_actual_feedstock_repair :
    selected repair = none ∧ (emit repair).length = 4 ∧
    (law.rawItems repair.past.frame.raw (emit repair)).map (fun item => decide (law.Valid item.before item.request)) =
      [false, false, true, false] ∧
    (nextCut repair).past.frame.raw.stock false .feedstock = 1 ∧
    (nextCut repair).past.frame.raw.technology.holder = some true ∧
    kinds repair repairPending = [.admitted, .deferred] ∧
    (newAfter repair repairPending).isPending 1 (nextInputs repair) = true ∧
    selected (nextCut repair) = some .productive ∧
    (nextCut (nextCut repair)).past.frame.raw.technology.holder = none ∧
    (nextCut (nextCut repair)).past.frame.raw.stock false .service = 2 ∧
    kinds (nextCut repair) repairedPending = [.admitted, .deferred, .obligationTerminal] := by decide +kernel

theorem failed_suppliers_do_not_mint_funds_or_new_liabilities :
    selected blocked = none ∧ (emit blocked).length = 4 ∧
    (law.rawItems blocked.past.frame.raw (emit blocked)).map (fun item => decide (law.Valid item.before item.request)) =
      [false, false, false, false] ∧
    (nextCut blocked).past.frame.raw.stock false .feedstock = 0 ∧
    (nextCut blocked).past.frame.raw.stock false .service = 0 ∧
    (nextCut blocked).past.frame.raw.claims () false true = 7 ∧
    (nextCut blocked).past.frame.raw.technology.holder = some true ∧
    kinds blocked blockedPending = [.admitted, .deferred] ∧
    (actualFunding blocked).isSome = false ∧
    (newAfter blocked blockedPending).isPending 0 (nextInputs blocked) = true := by decide +kernel

def shifted := afterInput productive Objection.Regression.changedSnapshotWord
def shiftedPending := firstPending shifted (by decide +kernel)

theorem changed_snapshot_emits_a_new_request_without_closing_the_old_one :
    isShifted (decideAt shifted) = true ∧ (emit shifted).length = 1 ∧
    (claimsAt 3 (nextInputs shifted) (shifted.depth + 2)).length = 0 ∧
    (newAfter shifted shiftedPending).isPending 3 (nextInputs shifted) = true := by decide +kernel

theorem no_objection_uses_the_original_source_response :
    (pending financedFirst).isSome = false ∧
    (actualOrders financedFirst).length = 0 ∧ (actualFunding financedFirst).isSome = false := by decide +kernel

def cashReady := afterInput Objection.Regression.first [submission]
def cashPending := firstPending cashReady (by decide +kernel)

theorem existing_cash_uses_one_paid_revoke_without_a_new_loan :
    selected cashReady = some .direct ∧ (emit cashReady).length = 1 ∧
    (actualFunding cashReady).isSome = false ∧
    (nextCut cashReady).past.frame.raw.stock false .service = cashReady.past.frame.raw.stock false .service - 1 ∧
    (nextCut cashReady).past.frame.raw.claims () false true = 7 ∧
    kinds cashReady cashPending = [.admitted, .obligationTerminal] := by decide +kernel

abbrev publicObjectionProductionFacade := ResponseRuntime.facade productive
abbrev publicObjectionFinanceFacade := ResponseRuntime.facade financed
abbrev publicObjectionRepairFacade := ResponseRuntime.facade repair
abbrev publicObjectionBlockedFacade := ResponseRuntime.facade blocked

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Response.Regression
