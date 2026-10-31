import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.History
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Examples.TransferAndRepayment

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Regression

open ResponsibilityLifecycle Source.Program Examples.TransferAndRepayment

def originalWord := [request 0 (.issue () 0 1 2)]
def original : ProgrammeSource.Input Party Unit Unit Unit Unit :=
  ⟨law, initial, originalWord, none, fun _ => [], none⟩

def revisedLaw : RawLaw Party Unit Unit Unit Unit := {law with duration := fun _ => 2}
def revisedWord := [request 0 (.issue () 0 1 2), request 1 (.assign () 0 1 2 2), request 0 (.settle () 0 2 2)]
def revised : ProgrammeSource.Input Party Unit Unit Unit Unit :=
  ⟨revisedLaw, law.next initial originalWord, revisedWord, none, fun _ => [], none⟩

def sources : Bool → ProgrammeSource.Input Party Unit Unit Unit Unit
  | false => original
  | true => revised

def before := through sources false 2
def after := continueVisits sources true 0 2 before

def debtRows (state : (process sources).GeneratedState) := state.current.slots.map fun slot =>
  ((slotClaim sources slot).1, (slotClaim sources slot).2.instruction.index,
    (slotBalance sources slot) 1, (slotBalance sources slot) 2)

theorem a_different_actual_source_retains_original_claim_and_adds_only_its_own_issue :
    debtRows before = [(false, 0, 2, 0)] ∧ debtRows after = [(false, 0, 0, 0), (true, 0, 2, 0)] ∧
    after.current.history.map LifecycleEvent.kind = [.admitted, .admitted, .progressed, .progressed, .obligationTerminal, .progressed] := by
  decide +kernel

theorem one_actual_source_quota_is_not_reused_on_the_second_loan :
    ledgerClaims sources after.current () 0 1 = 2 ∧ ledgerClaims sources after.current () 0 2 = 0 ∧
    (revisedLaw.next revised.initial revisedWord).stock 0 () = 0 ∧
    (revisedLaw.next revised.initial revisedWord).stock 2 () = 2 := by decide +kernel

def originalDebt := before.current.slots[0]'(by decide +kernel)
def originalDebtFollow := Migration.follow sources (continueVisits_run sources true 0 2 before) 0 originalDebt
  (List.getElem?_eq_getElem (by decide +kernel))

theorem the_complete_original_native_admission_is_preserved :
    Migration.identity sources originalDebtFollow.slot = Migration.identity sources originalDebt :=
  originalDebtFollow.path.preserves_identity sources

theorem every_actual_matrix_address_is_supported :
    ∀ debtor holder : Party, ledgerClaims sources after.current () debtor holder =
      (revisedLaw.next revised.initial revisedWord).claims () debtor holder := by decide +kernel

def refusedWord := [request 0 (.assign () 0 1 2 1), request 0 (.settle () 0 1 3)]
def refused : ProgrammeSource.Input Party Unit Unit Unit Unit :=
  {revised with instructions := refusedWord}
def refusedSources : Bool → ProgrammeSource.Input Party Unit Unit Unit Unit
  | false => original
  | true => refused
def refusedBefore := through refusedSources false 2
def refusedAfter := continueVisits refusedSources true 0 2 refusedBefore

theorem false_assignment_signature_and_unfunded_payment_keep_the_original_debt :
    refusedAfter.current.history.map LifecycleEvent.kind = [.admitted] ∧
    ledgerClaims refusedSources refusedAfter.current () 0 1 = 2 ∧
    (revisedLaw.next refused.initial refusedWord).claims () 0 1 = 2 := by decide +kernel

def repriced : ProgrammeSource.Input Party Unit Unit Unit Unit :=
  {revised with law := {revisedLaw with settlementRate := fun _ => 2}, instructions := [request 0 (.settle () 0 1 1)]}
def repricedSources : Bool → ProgrammeSource.Input Party Unit Unit Unit Unit
  | false => original
  | true => repriced
def repricedBefore := through repricedSources false 2
def repricedAfter := continueVisits repricedSources true 0 2 repricedBefore
def repricedQuotas := (instructionTrace repricedSources (visitOrigins repricedSources true 1) repricedBefore).filterMap
  fun record => match record.result with
    | .movement _ allocation => some allocation.remaining
    | _ => none

theorem a_source_cannot_change_the_original_settlement_rate_to_discharge_old_debt :
    repricedAfter.current.history.map LifecycleEvent.kind = [.admitted] ∧
    ledgerClaims repricedSources repricedAfter.current () 0 1 = 2 ∧ repricedQuotas = [1] := by decide +kernel

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Regression
