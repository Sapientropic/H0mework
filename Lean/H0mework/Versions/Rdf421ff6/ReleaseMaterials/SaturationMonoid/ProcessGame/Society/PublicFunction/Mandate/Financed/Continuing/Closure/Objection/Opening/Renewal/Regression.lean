import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.Renewal.Runtime
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.Admission.Regression

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.Renewal.Regression

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle
open Followup

noncomputable section

def first := Exit.Regression.first
def renewed := advance first
def withdrawn := advance renewed

def ownGrant (inventory : Joint.Inventory 3) :=
  (grantsAt base scope (Runtime.mandateCurrentAt 3 (inputs inventory) 0)
    (Runtime.mandateWordAt 3 (inputs inventory) 0)).get ⟨0, by
      change 0 < (grantsAt base scope (law.next (initial 3) [])
        (SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.original 3)).length
      decide +kernel⟩

def record (inventory : Joint.Inventory 3) :=
  Runtime.traceGrant 3 (inputs inventory) 0 (inventory.cut.depth + 1) (ownGrant inventory)

theorem real_member_proposes_and_the_current_holder_pays_its_own_renewal :
    pending first = false ∧ first.cut.past.frame.raw.technology.holder = some true ∧
    (choose first.cut.past.frame.raw true).map Ready.method = some .direct ∧
    (commandsAt base scope first.cut.past.frame.raw (emit first)).map (fun event => event.command) = [.propose true, .renew] ∧
    renewed.cut.past.frame.raw.technology.version = first.cut.past.frame.raw.technology.version + 2 ∧
    renewed.cut.past.frame.raw.stock true .service = first.cut.past.frame.raw.stock true .service - 1 ∧
    renewed.cut.past.frame.raw.stock false .service = first.cut.past.frame.raw.stock false .service - 1 ∧
    renewed.cut.past.frame.raw.technology.holder = some true ∧
    (grantsAt base scope first.cut.past.frame.raw (emit first)).isEmpty = true := by decide +kernel

theorem renewed_authority_is_immediately_subject_to_a_real_new_objection :
    Joint.Regression.histories renewed = [[.admitted]] ∧ pending renewed = true ∧
    emit renewed = Admission.emit renewed ∧
    withdrawn.cut.past.frame.raw.technology.holder = none ∧
    Joint.Regression.histories withdrawn = [[.admitted, .progressed, .obligationTerminal]] ∧
    withdrawn.cut.past.frame.raw.claims () false true = 7 := by
  refine ⟨by decide +kernel, by decide +kernel, ?_, by decide +kernel⟩
  simp only [emit, show pending renewed = true from by decide +kernel, if_true]

theorem original_native_grant_is_maintained_then_released_without_new_admission :
    (native first).mandates.length = 1 ∧
    (record first).continuation.state.history.map LifecycleEvent.kind = [.admitted, .maintained] ∧
    (record renewed).continuation.state.history.map LifecycleEvent.kind = [.admitted, .maintained, .bearerRelease] := by decide +kernel

theorem maintained_original_grant_is_in_the_same_native_records :
    (⟨⟨0, by omega⟩, record first⟩ :
      Sigma fun birth : Fin (first.cut.depth + 2) => Runtime.TracedGrant 3 (inputs first) birth.val (first.cut.depth + 1)) ∈
        (native first).mandates :=
  Runtime.every_original_grant_is_retained 3 (inputs first) (first.cut.depth + 1) ⟨0, by omega⟩
    (ownGrant first) (List.get_mem _ _)

theorem actual_renewal_keeps_the_original_admission_and_live_responsibility :
    (record first).continuation.state.LiveAt 0 ∧
    HEq (record first).continuation.obligation.admission
      (Lifecycle.original base scope (Runtime.mandateCurrentAt 3 (inputs first)) (Runtime.mandateWordAt 3 (inputs first))
        0 (ownGrant first)).admission :=
  ⟨(record first).continuation.responsibility_remains_live, (record first).continuation.original_admission⟩

def financed := Opening.Regression.empty
def financeRenewed := advance financed

theorem holder_finances_its_renewal_on_its_own_account_with_old_debt_retained :
    (choose financed.cut.past.frame.raw true).map Ready.method = some .financed ∧
    financeRenewed.cut.past.frame.raw.claims () true false = 1 ∧
    financeRenewed.cut.past.frame.raw.claims () false true = 7 ∧
    financeRenewed.cut.past.frame.raw.technology.holder = some true ∧ pending financeRenewed = true ∧
    (advance financeRenewed).cut.past.frame.raw.technology.holder = none ∧
    (advance financeRenewed).cut.past.frame.raw.claims () true false = 2 := by decide +kernel

def burnService (current : Current) (actor : Bool) : Action :=
  ⟨actor, [], .resource, [], .use actor [(.service, current.stock actor .service)] .external⟩

def exhaust (current : Current) (actor : Bool) : Action :=
  ⟨actor, [], .resource, [], .use actor
    [(.feedstock, current.stock actor .feedstock), (.service, current.stock actor .service)] .external⟩

def moveFeedstock : Action := ⟨false, [], .resource, [], .transfer false true [(.feedstock, 1)]⟩
def productive := Joint.submit first
  [moveFeedstock, burnService first.cut.past.frame.raw false, burnService first.cut.past.frame.raw true]
def blocked := Joint.submit first [exhaust first.cut.past.frame.raw false, exhaust first.cut.past.frame.raw true]
def late := (List.replicate 12 ([] : List Action)).foldl Joint.submit first

theorem both_signers_can_produce_the_actual_renewal_cost_without_a_new_loan :
    (choose productive.cut.past.frame.raw true).map Ready.method = some .productive ∧
    (advance productive).cut.past.frame.raw.stock false .feedstock = productive.cut.past.frame.raw.stock false .feedstock - 1 ∧
    (advance productive).cut.past.frame.raw.stock true .feedstock = productive.cut.past.frame.raw.stock true .feedstock - 1 ∧
    (advance productive).cut.past.frame.raw.claims () true false = 0 ∧
    pending (advance productive) = true := by decide +kernel

theorem actual_refusals_and_failed_supplies_still_generate_a_real_open_objection :
    pending blocked = false ∧ (choose blocked.cut.past.frame.raw true).isSome = false ∧
    (demands blocked.cut.past.frame.raw true).map Demand.quantity = [1, 1, 1] ∧
    (law.rawItems blocked.cut.past.frame.raw (emit blocked)).map (fun item => decide (law.Valid item.before item.request)) =
      [false, false, false, false, false, false, false, true] ∧
    Joint.Regression.histories (advance blocked) = [[.admitted]] ∧
    (advance blocked).cut.past.frame.raw.technology.holder = some true ∧
    (advance blocked).cut.past.frame.raw.claims () false true = 7 := by decide +kernel

theorem expiration_is_a_policy_block_and_does_not_mint_a_new_period_or_material_gap :
    task.deadline < late.cut.past.frame.raw.clock ∧
    (choose late.cut.past.frame.raw true).isSome = false ∧ (demands late.cut.past.frame.raw true).isEmpty = true ∧
    (advance late).cut.past.frame.raw.technology = late.cut.past.frame.raw.technology ∧
    pending (advance late) = true ∧ (grantsAt base scope late.cut.past.frame.raw (emit late)).isEmpty = true := by decide +kernel

theorem a_preexisting_withdrawal_preempts_any_new_renewal :
    emit Joint.Regression.legacy = Admission.emit Joint.Regression.legacy := by
  simp only [emit, show pending Joint.Regression.legacy = true from by decide +kernel, if_true]

def before := beforeRenewal first.cut.past.frame.raw true .direct
def wrongSigner := request scope before false .renew
def missingGate : Action := {request scope before true .renew with gates := []}
def reviewed := law.step before (request scope before false .review)
def stale := request scope before true .renew

theorem a_renewal_needs_the_current_holder_its_real_gate_and_fresh_target :
    ¬ law.Valid before wrongSigner ∧ ¬ law.Valid before missingGate ∧ ¬ law.Valid reviewed stale := by decide +kernel

abbrev publicRenewalFacade := RenewalRuntime.facade first
abbrev publicRenewalFinanceFacade := RenewalRuntime.facade financed
abbrev publicRenewalProductiveFacade := RenewalRuntime.facade productive
abbrev publicRenewalBlockedFacade := RenewalRuntime.facade blocked
abbrev publicRenewalPriorityFacade := RenewalRuntime.facade renewed

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.Renewal.Regression
