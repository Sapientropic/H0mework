import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Followup.Cross.Runtime
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Followup.Regression

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Followup.Cross.Regression

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle

noncomputable section

def base := initial Followup.Regression.changed Followup.Regression.original.claim Followup.Regression.original.inside
def renewed := advance base
def settled := advance renewed

def kinds {fuel : ℚ} {originInputs : List (List Action)} {original : Claim fuel originInputs} (stage : Stage original) :=
  stage.history.state.current.history.map LifecycleEvent.kind

def residualVersion {fuel : ℚ} {originInputs inputs : List (List Action)} {original : Claim fuel originInputs} :
    History original inputs → Option Nat
  | .pending target _ _ => some target.snapshot.version
  | .closed .. => none

theorem source_driven_two_root_followup_closes_the_original_duty :
    kinds base = [.admitted] ∧ residualVersion base.history = some 2 ∧
    kinds renewed = [.admitted, .progressed] ∧ residualVersion renewed.history = some 3 ∧
    kinds settled = [.admitted, .progressed, .obligationTerminal] ∧ settled.history.isPending = false ∧
    settled.history.state.current.slots.length = 1 ∧ settled.cut.past.frame.raw.technology.holder = none ∧
    renewed.cut.depth = base.cut.depth + 1 ∧ settled.cut.depth = base.cut.depth + 2 := by decide +kernel

theorem transported_state_and_original_run_are_literal :
    (before renewed (emit renewed)).state = renewed.history.state ∧
    (before settled []).state = settled.history.state :=
  ⟨transport_preserves_the_entire_generated_state _ _ _ _, transport_preserves_the_entire_generated_state _ _ _ _⟩

def held := submit base [{submission with signer := true}]
def malformed := submit base [{submission with gates := []}]

theorem unrelated_or_malformed_signature_cannot_retarget_across_roots :
    kinds held = [.admitted] ∧ residualVersion held.history = some 2 ∧ held.history.isPending = true ∧
    kinds malformed = [.admitted] ∧ residualVersion malformed.history = some 2 ∧ malformed.history.isPending = true := by decide +kernel

def sameVisit := afterInput Objection.Regression.first [submission, submission]
def sameVisitOriginal : Claim 3 (branchInputs Objection.Regression.first [submission, submission]) :=
  (claimsAt 3 (branchInputs Objection.Regression.first [submission, submission]) 2).get ⟨1, by decide +kernel⟩
def sameVisitStage := initial sameVisit sameVisitOriginal (by decide +kernel)
def earlier := (claimsAt 3 sameVisitStage.inputs 2).get ⟨0, by decide +kernel⟩

theorem an_earlier_signature_in_the_same_visit_cannot_be_replayed_as_followup :
    (sameVisitStage.history.receive earlier.position).state.current.history.map LifecycleEvent.kind = [.admitted] ∧
    residualVersion (sameVisitStage.history.receive earlier.position) = some 2 := by decide +kernel

def refused := submit renewed [Response.Regression.drain renewed.cut.past.frame.raw,
  request scope (law.step renewed.cut.past.frame.raw (Response.Regression.drain renewed.cut.past.frame.raw)) false .revoke]
def repaired := advance refused

theorem later_root_refusal_keeps_updated_target_and_source_repairs_it :
    kinds refused = [.admitted, .progressed, .deferred] ∧ residualVersion refused.history = some 3 ∧
    refused.history.isPending = true ∧
    kinds repaired = [.admitted, .progressed, .deferred, .obligationTerminal] ∧
    repaired.cut.past.frame.raw.technology.holder = none := by decide +kernel

def fundedBase := initial Response.Regression.financed Response.Regression.financedPending.claim Response.Regression.financedPending.inside
def financed := advance fundedBase

theorem original_duty_consumes_actual_financing_on_its_new_root :
    fundedBase.cut.past.frame.raw.stock false .service = 0 ∧
    fundedBase.cut.past.frame.raw.stock false .feedstock = 0 ∧
    kinds financed = [.admitted, .obligationTerminal] ∧
    financed.cut.past.frame.raw.claims () false true = 8 ∧
    financed.cut.past.frame.raw.technology.holder = none := by decide +kernel

def blockedBase := initial Response.Regression.blocked Response.Regression.blockedPending.claim Response.Regression.blockedPending.inside
def blocked := run blockedBase 3

theorem repeated_real_failures_preserve_the_same_duty_without_new_debt :
    kinds blocked = [.admitted, .deferred, .deferred, .deferred] ∧ blocked.history.isPending = true ∧
    blocked.cut.past.frame.raw.claims () false true = 7 ∧ blocked.history.state.current.slots.length = 1 := by decide +kernel

def reopenedWorld := submit settled [submission]
def afterArchive := run reopenedWorld 2

theorem original_archive_survives_later_world_changes_and_responses :
    kinds reopenedWorld = [.admitted, .progressed, .obligationTerminal] ∧
    kinds afterArchive = kinds settled ∧ afterArchive.history.isPending = false := by decide +kernel

abbrev publicCrossRootObjectionFacade := CrossRuntime.facade renewed
abbrev publicCrossRootObjectionBlockedFacade := CrossRuntime.facade blockedBase

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Followup.Cross.Regression
