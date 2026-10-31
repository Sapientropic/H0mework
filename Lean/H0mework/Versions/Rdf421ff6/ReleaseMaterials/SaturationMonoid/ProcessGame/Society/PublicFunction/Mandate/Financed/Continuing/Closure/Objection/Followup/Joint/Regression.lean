import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Followup.Joint.Runtime
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Followup.Cross.Regression

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Followup.Joint.Regression

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle

noncomputable section

def kinds {fuel : ℚ} {inputs : List (List Action)} {cut : Cut fuel inputs} (row : Row cut) :=
  row.2.history.state.current.history.map LifecycleEvent.kind

def histories {fuel : ℚ} (inventory : Inventory fuel) := inventory.frame.rows.map kinds

def empty := initial Objection.Regression.first
def twoSignatures := submit empty [submission, submission]
def singleWord := [submission, request scope (law.step empty.cut.past.frame.raw submission) false .revoke]
def sameWordSettled := submit empty singleWord

theorem actual_signatures_admit_then_continue_one_native_row :
    empty.frame.rows.length = 0 ∧ twoSignatures.frame.rows.length = 1 ∧
    (decisionAt empty [submission, submission] ⟨0, by decide +kernel⟩).mode = .admitted ∧
    (decisionAt empty [submission, submission] ⟨1, by decide +kernel⟩).mode = .continued ∧
    histories twoSignatures = [[.admitted, .progressed]] ∧ twoSignatures.frame.seen = [(2, 0), (2, 1)] := by decide +kernel

theorem newborn_consumes_the_actual_suffix_without_reading_ahead_at_admission :
    histories sameWordSettled = [[.admitted, .obligationTerminal]] ∧
    (sameWordSettled.frame.rows.map Row.isPending) = [false] ∧
    sameWordSettled.cut.past.frame.raw.technology.holder = none := by decide +kernel

def legacyCut := afterInput Objection.Regression.first [submission, submission]
def legacy := initial legacyCut
def changed := submit legacy Followup.Regression.changedPrefix
def reconfirmed := advance changed
def settled := advance reconfirmed

theorem all_legacy_rows_consume_one_reconfirmation_and_one_paid_revoke :
    legacy.frame.rows.length = 2 ∧ changed.frame.rows.length = 2 ∧
    emit changed = [submission] ∧ reconfirmed.frame.rows.length = 2 ∧
    histories reconfirmed = [[.admitted, .progressed, .progressed], [.admitted, .progressed]] ∧
    histories settled = [[.admitted, .progressed, .progressed, .obligationTerminal], [.admitted, .progressed, .obligationTerminal]] ∧
    settled.frame.rows.length = 2 ∧ settled.cut.past.frame.raw.technology.holder = none := by
  refine ⟨by decide +kernel, by decide +kernel, ?_, by decide +kernel⟩
  have unmatched : changed.frame.rows.any Row.matches = false := by decide +kernel
  have pending : changed.frame.rows.any Row.isPending = true := by decide +kernel
  simp only [emit, unmatched, pending, Bool.false_eq_true, ↓reduceIte]

def malformed := submit empty [{submission with gates := []}, {submission with signer := true}]

theorem raw_present_without_the_registered_signature_does_not_create_a_row :
    malformed.frame.rows = [] ∧ malformed.frame.seen = [] := by decide +kernel

def blockedBase := initial Response.Regression.blocked
def blocked := run blockedBase 3

theorem repeated_real_failure_preserves_all_original_rows_and_principal :
    blocked.frame.rows.length = blockedBase.frame.rows.length ∧
    histories blocked = [[.admitted, .deferred, .deferred, .deferred]] ∧
    blocked.cut.past.frame.raw.claims () false true = 7 := by decide +kernel

def funded := advance (initial Response.Regression.financed)

theorem the_joint_word_uses_actual_finance_before_closing_the_original_row :
    histories funded = [[.admitted, .obligationTerminal]] ∧
    funded.cut.past.frame.raw.claims () false true = 8 ∧ funded.cut.past.frame.raw.technology.holder = none := by decide +kernel

def laterSignature := submit settled [submission]
def laterResponses := run laterSignature 2

theorem completed_archives_remain_when_later_world_changes_have_no_active_mandate :
    histories laterSignature = histories settled ∧ histories laterResponses = histories settled ∧
    laterSignature.frame.rows.length = 2 ∧ laterResponses.frame.rows.length = 2 := by decide +kernel

def fundAcceptance : Action := ⟨false, [], .resource, [], .transfer false true [(.service, 1)]⟩
def proposal := request scope (law.step sameWordSettled.cut.past.frame.raw fundAcceptance) false (.propose true)
def acceptance := request scope (law.step (law.step sameWordSettled.cut.past.frame.raw fundAcceptance) proposal) true .accept
def newCycleWord := [fundAcceptance, proposal, acceptance, submission]
def newCycle := submit sameWordSettled newCycleWord

theorem a_later_actual_grant_creates_a_new_duty_while_the_original_archive_remains :
    histories newCycle = [[.admitted, .obligationTerminal], [.admitted]] ∧
    newCycle.frame.rows.length = 2 ∧ newCycle.cut.past.frame.raw.technology.holder = some true ∧
    (newCycle.frame.rows.map Row.isPending) = [false, true] := by decide +kernel

abbrev publicJointObjectionFacade := JointRuntime.facade changed (emit changed)
abbrev publicJointObjectionBirthFacade := JointRuntime.facade empty singleWord
abbrev publicJointObjectionBlockedFacade := JointRuntime.facade blockedBase (emit blockedBase)

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Followup.Joint.Regression
