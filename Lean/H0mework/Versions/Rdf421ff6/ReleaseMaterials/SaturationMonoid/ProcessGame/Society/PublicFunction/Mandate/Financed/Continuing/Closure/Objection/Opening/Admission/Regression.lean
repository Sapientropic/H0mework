import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.Admission.Runtime
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.Exit.Regression

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.Admission.Regression

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle
open Followup

noncomputable section

def first := Exit.Regression.exited
def entered := advance first

def drain (good : Good) : Action :=
  ⟨false, [], .resource, [], .transfer false true [(good, first.cut.past.frame.raw.stock false good)]⟩

def productive := Joint.submit first [drain .service]
def repair := Joint.submit first [drain .service, drain .feedstock]
def supplied := advance repair
def repaired := advance supplied

def late := (List.replicate 12 ([] : List Action)).foldl Joint.submit first

theorem source_selects_and_pays_new_two_leg_admission_with_old_debt :
    Quiet first.cut.past.frame.raw ∧
    (choose first.cut.past.frame.raw).map (fun ready => (ready.choice.sponsor, ready.choice.candidate, ready.choice.method)) =
      some (false, false, .direct) ∧
    (newGrants first).length = 1 ∧
    entered.cut.past.frame.raw.claims () false true = 7 := by decide +kernel

def newGrant := (newGrants first).get ⟨0, by decide +kernel⟩
def newRecord := Runtime.traceGrant 3 (inputs first) (first.cut.depth + 1) (first.cut.depth + 1) newGrant

theorem actual_new_grant_is_in_the_native_run :
    (⟨⟨first.cut.depth + 1, by omega⟩, newRecord⟩ :
      Sigma fun birth : Fin (first.cut.depth + 2) => Runtime.TracedGrant 3 (inputs first) birth.val (first.cut.depth + 1)) ∈
        (native first).mandates := every_new_grant_is_in_the_same_native_records first newGrant (List.get_mem _ _)

theorem new_native_responsibility_keeps_its_actual_admission :
    newRecord.continuation.state.LiveAt 0 ∧
    HEq newRecord.continuation.obligation.admission
      (Lifecycle.original base scope (Runtime.mandateCurrentAt 3 (inputs first)) (Runtime.mandateWordAt 3 (inputs first))
        (first.cut.depth + 1) newGrant).admission :=
  ⟨newRecord.continuation.responsibility_remains_live, newRecord.continuation.original_admission⟩

theorem the_new_grant_consumes_the_real_same_word_exit_after_acceptance :
    (native first).mandates.length = 2 ∧
    newRecord.continuation.state.history.map LifecycleEvent.kind = [.admitted, .bearerRelease] ∧
    entered.cut.past.frame.raw.technology.holder = none := by decide +kernel

theorem productive_admission_really_uses_the_holders_own_material :
    productive.cut.past.frame.raw.stock false .service = 0 ∧
    (choose productive.cut.past.frame.raw).map Ready.choice = some ⟨false, false, .productive⟩ ∧
    (newGrants productive).length = 1 ∧
    (advance productive).cut.past.frame.raw.claims () false true = 7 := by decide +kernel

theorem real_supply_recomputes_the_next_cut_and_generates_its_new_grant :
    (choose repair.cut.past.frame.raw).isSome = false ∧
    (demands repair.cut.past.frame.raw).map Demand.quantity = [1, 1] ∧
    supplied.cut.past.frame.raw.stock false .feedstock = 1 ∧
    (choose supplied.cut.past.frame.raw).map Ready.choice = some ⟨false, false, .productive⟩ ∧
    (newGrants supplied).length = 1 ∧ repaired.cut.past.frame.raw.claims () false true = 7 := by decide +kernel

theorem expired_admission_is_a_policy_block_not_a_new_grant_or_a_supply_gap :
    task.deadline < late.cut.past.frame.raw.clock ∧
    (choose late.cut.past.frame.raw).isSome = false ∧
    (newGrants late).length = 0 ∧ (demands late.cut.past.frame.raw).length = 0 ∧
    (commandsAt base scope late.cut.past.frame.raw (emit late)).any (fun event => decide (event.command = .review)) = true := by decide +kernel

theorem source_sponsorship_is_not_minted_for_nonmembers :
    (choices.map Choice.sponsor).all (fun actor => decide (actor = false)) = true ∧
    ¬ law.Valid first.cut.past.frame.raw (request scope first.cut.past.frame.raw true (.propose true)) := by decide +kernel

def badAcceptance := request scope (beforeAcceptance first.cut.past.frame.raw ⟨false, false, .direct⟩) true .accept

theorem acceptance_needs_the_actual_offered_candidates_signature :
    ¬ law.Valid (beforeAcceptance first.cut.past.frame.raw ⟨false, false, .direct⟩) badAcceptance := by decide +kernel

theorem active_cut_still_uses_the_existing_holder_exit :
    emit Exit.Regression.first = Exit.emit Exit.Regression.first :=
  active_emission_is_the_existing_exit _ (by left; decide +kernel)

theorem newborn_admission_does_not_reopen_the_old_objection_archive :
    Joint.Regression.histories entered = Joint.Regression.histories first := by decide +kernel

abbrev publicAdmissionFacade := AdmissionRuntime.facade first
abbrev publicAdmissionProductiveFacade := AdmissionRuntime.facade productive
abbrev publicAdmissionRepairFacade := AdmissionRuntime.facade repair
abbrev publicAdmissionBlockedFacade := AdmissionRuntime.facade late

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.Admission.Regression
