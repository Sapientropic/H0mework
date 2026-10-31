import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Future.Runtime
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Future.Challenge
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Settlement.Regression

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 24000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Future.Regression

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle
open Followup
noncomputable section
abbrev ready := Settlement.Regression.ready
abbrev inventory := FinancialRegression.initialInventory

def admitted := staged ready inventory .admission
def afterAdmission := advance ready inventory .admission
def exited := staged ready admitted .exit
def renewed := staged ready admitted .renewal
def revised := staged ready afterAdmission .revision

theorem actual_material_and_double_signing_generate_a_new_grant_and_objection :
    (choose ready .admission (current ready inventory.inputs)).isSome = true ∧
    (selected ready .admission (current ready inventory.inputs)).method = .supplied ∧
    admitted.grants.length = 1 ∧ admitted.objections.length = 1 ∧
    (current ready admitted.inputs).technology.holder = some true ∧
    (current ready admitted.inputs).stock false .feedstock = 2 := by decide +kernel

theorem the_same_source_consumes_the_new_withdrawal_and_saved_debt :
    (current ready afterAdmission.inputs).technology.holder = none ∧
    FinancialRegression.debts afterAdmission = [(7,0,4)] ∧
    afterAdmission.grants.length = 1 ∧ afterAdmission.objections.length = 1 := by decide +kernel

theorem the_actual_holder_can_sign_its_own_paid_exit :
    (choose ready .exit (current ready admitted.inputs)).isSome = true ∧
    (current ready exited.inputs).technology.holder = none ∧
    exited.grants.length = 1 ∧ exited.objections.length = 2 := by decide +kernel

theorem actual_renewal_needs_a_new_pair_and_keeps_the_original_grant :
    (choose ready .renewal (current ready admitted.inputs)).isSome = true ∧
    (current ready renewed.inputs).technology.last = some .renew ∧
    (current ready renewed.inputs).technology.holder = some true ∧
    renewed.grants.length = admitted.grants.length ∧ renewed.objections.length = 2 := by decide +kernel

theorem paid_review_occurs_after_the_deadline_without_reopening_it_by_name :
    ready.task.deadline < (current ready afterAdmission.inputs).clock ∧
    (choose ready .revision (current ready afterAdmission.inputs)).isSome = true ∧
    (current ready revised.inputs).technology.last = some .review ∧
    (current ready revised.inputs).technology.version = (current ready afterAdmission.inputs).technology.version + 1 ∧
    (choose ready .admission (current ready afterAdmission.inputs)).isNone = true ∧
    ¬ Eligible ready .admission (current ready afterAdmission.inputs) := by decide +kernel

def noMaterial := submit ready inventory [⟨false, [], .resource, [], .use false [(.feedstock,3)] .external⟩]
def financed := staged ready noMaterial .admission

theorem actual_financed_admission_adds_its_new_principal_to_the_saved_original_account :
    (selected ready .admission (current ready noMaterial.inputs)).method = .financed ∧
    financed.grants.length = 1 ∧
    FinancialRegression.debts financed = [(7,0,7),(2,2,0)] := by decide +kernel

abbrev exhausted := Joint.Regression.exhausted

theorem zero_material_keeps_a_real_challenge_and_unpaid_exit_in_the_native_inventory :
    (choose ready .challenge (current ready exhausted.inputs)).isSome = true ∧
    (staged ready exhausted .challenge).objections.length = exhausted.objections.length + 1 ∧
    (advance ready exhausted .challenge).objections.length = exhausted.objections.length + 1 ∧
    (choose ready .exit (current ready exhausted.inputs)).isNone = true ∧
    FinancialRegression.debts (advance ready exhausted .exit) = FinancialRegression.debts exhausted ∧
    (current ready (advance ready exhausted .exit).inputs).technology.holder = some true := by decide +kernel

theorem a_quiet_matching_shape_cannot_manufacture_a_native_challenge :
    ¬ Eligible ready .challenge (current ready inventory.inputs) ∧
    (staged ready inventory .challenge).objections.length = inventory.objections.length := by decide +kernel

def finiteRun := run ready inventory [.admission,.revision,.challenge,.exit]

theorem finite_intents_recompute_each_actual_cut_and_consume_the_original_debt :
    finiteRun.inputs.length = inventory.inputs.length + 8 ∧
    FinancialRegression.debts finiteRun = [(7,0,0)] ∧
    finiteRun.grants.length = 1 := by decide +kernel

theorem the_source_itself_chooses_new_inputs_from_each_saved_residual :
    nextIntent ready inventory = .admission ∧
    nextIntent ready exhausted = .challenge ∧
    (evolve ready inventory 2).inputs.length = inventory.inputs.length + 4 ∧
    FinancialRegression.debts (evolve ready inventory 2) = [(7,0,1)] := by decide +kernel

abbrev publicScopeFutureAdmissionFacade := Runtime.facade ready inventory .admission
abbrev publicScopeFutureExitFacade := Runtime.facade ready admitted .exit
abbrev publicScopeFutureRenewalFacade := Runtime.facade ready admitted .renewal
abbrev publicScopeFutureRevisionFacade := Runtime.facade ready afterAdmission .revision
abbrev publicScopeFutureChallengeFacade := Runtime.facade ready exhausted .challenge
abbrev publicScopeFutureBlockedFacade := Runtime.facade ready exhausted .exit
abbrev publicScopeFutureFinancedFacade := Runtime.facade ready noMaterial .admission

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Future.Regression
