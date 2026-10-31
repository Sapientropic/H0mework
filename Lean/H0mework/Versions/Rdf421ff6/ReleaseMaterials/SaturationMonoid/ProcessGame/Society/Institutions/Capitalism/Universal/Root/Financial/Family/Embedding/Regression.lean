import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Embedding.Canonical
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Regression

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Embedding.Regression

open ResponsibilityLifecycle Source.Program Examples.TransferAndRepayment

def sources (_ : Unit) := input
def paid := (accountAt sources () 2).account

theorem actual_issue_assignment_and_both_payments_have_their_original_records :
    paid.current.history.map LifecycleEvent.kind = [.admitted, .progressed, .progressed, .obligationTerminal] ∧
    paid.current.slots.map (fun row => slotBalance sources row 1) = [0] ∧
    paid.current.slots.map (fun row => slotBalance sources row 2) = [0] := by decide +kernel

theorem the_full_terminal_archive_and_all_four_records_are_embedded :
    paid.current = state sources () Examples.TransferAndRepayment.final.current := accountAt_full_state sources () 2

theorem every_finite_actual_cut_has_the_complete_raw_matrix (ordinal : Nat) :
    ledgerClaims sources (accountAt sources () ordinal).account.current =
      (ProgrammeSource.rawCurrent input (ProgrammeHistory.visitAt input ordinal).current).claims :=
  accountAt_actual_matrix sources () rfl ordinal

def rejectedWord := [request 0 (.issue () 0 1 2), request 0 (.assign () 0 1 2 1), request 0 (.settle () 0 1 3)]
def rejectedInput : ProgrammeSource.Input Party Unit Unit Unit Unit := {input with instructions := rejectedWord}
def rejectedSources (_ : Unit) := rejectedInput
def rejected := (accountAt rejectedSources () 2).account

theorem rejected_signature_and_unfunded_payment_do_not_create_lifecycle_progress :
    rejected.current.history.map LifecycleEvent.kind = [.admitted] ∧
    rejected.current.slots.map (fun row => slotBalance rejectedSources row 1) = [2] ∧
    rejected.current.slots.map (fun row => slotBalance rejectedSources row 2) = [0] := by decide +kernel

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Embedding.Regression
