import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Financing
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.FixedTask

/-! A financed candidate is generated from primitive requests and executed
at the captured source's own successor. If no funded candidate is generated,
the existing service compiler still supplies service or a typed bounded
obstruction. No financial existence claim is read from that fallback. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction

open Institutions.Capitalism.Universal.Source.Program
open Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

structure FinancedSource (Party Good Port Technology Instrument : Type)
    [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument] where
  seed : FixedTaskSource Party Good Port Technology Instrument
  terms : Financing.Terms Party Instrument

namespace FinancedSource

variable (source : FinancedSource Party Good Port Technology Instrument)

def financedAt (current : RawCurrent Party Good Technology Instrument) :=
  Financing.compileFinanced? source.seed.law current source.seed.task
    (source.seed.actionsAt current) source.seed.budget source.terms

def outcomeAt (current : RawCurrent Party Good Technology Instrument) :=
  match source.financedAt current with
  | some funded => PlanningOutcome.paid funded.service
  | none => compile source.seed.law current source.seed.task
      (source.seed.actionsAt current) source.seed.budget

def reportAt (current : RawCurrent Party Good Technology Instrument) :
    ProgrammeSource.ProgrammeReport Party Good Port Technology Instrument :=
  if current.round = source.seed.initial.round + 1 then .original current source.seed.original
  else .planning source.seed.law current source.seed.task (source.seed.actionsAt current)
    source.seed.budget (source.outcomeAt current)

def input : ProgrammeSource.Input Party Good Port Technology Instrument where
  law := source.seed.law
  initial := source.seed.initial
  instructions := source.seed.original
  emission? := some (fun current => (source.reportAt current).word)
  observedEmission? := some { generate := source.reportAt, word := ProgrammeSource.ProgrammeReport.word }
  localAttempts := source.seed.actionsAt

def currentAt (depth : Nat) :=
  ProgrammeSource.rawCurrent source.input (ProgrammeHistory.visitAt source.input depth).current

def actualExecution (depth : Nat) :=
  (ProgrammeLiving.projectionLaw source.input).project .execution
    (ProgrammeSource.emitted source.input
      (ProgrammeHistory.visitAt source.input (depth + 1)).current) ()

theorem current_round (depth : Nat) :
    (source.currentAt depth).round = source.seed.initial.round + depth :=
  ProgrammeHistory.visit_round source.input depth

theorem actual_word (depth : Nat) :
    (source.actualExecution depth).submitted = (source.reportAt (source.currentAt (depth + 1))).word := by
  change ProgrammeSource.rawEvent source.input
    (ProgrammeSource.next source.input (ProgrammeHistory.visitAt source.input depth).current) =
    (source.reportAt (ProgrammeSource.rawCurrent source.input
      (ProgrammeSource.next source.input (ProgrammeHistory.visitAt source.input depth).current))).word
  cases (ProgrammeHistory.visitAt source.input depth).current <;> rfl

theorem original_is_actually_rejected :
    (source.actualExecution 0).submitted = source.seed.original ∧
    ∃ item ∈ (source.actualExecution 0).interpreted.items,
      ¬ source.seed.law.Valid item.before item.request := by
  have original : (source.actualExecution 0).submitted = source.seed.original := by
    rw [source.actual_word]
    unfold reportAt
    rw [source.current_round, if_pos rfl]
    rfl
  refine ⟨original, ?_⟩
  change ∃ item ∈ (source.seed.law.execute (source.currentAt 1) 0
    (source.actualExecution 0).submitted).items, _
  rw [original]
  exact source.seed.refused

theorem funded_plan_is_actual (depth : Nat)
    (funded : Financing.FinancedPlan source.seed.law (source.currentAt (depth + 2))
      source.seed.task (source.seed.actionsAt (source.currentAt (depth + 2))) source.seed.budget source.terms)
    (generated : source.financedAt (source.currentAt (depth + 2)) = some funded) :
    (source.actualExecution (depth + 1)).submitted = funded.service.word ∧
    (source.actualExecution (depth + 1)).after = funded.service.next ∧
    source.currentAt (depth + 3) = funded.service.next := by
  have word : (source.actualExecution (depth + 1)).submitted = funded.service.word := by
    rw [source.actual_word]
    unfold reportAt
    rw [source.current_round, if_neg (by omega)]
    unfold outcomeAt
    rw [generated]
    rfl
  have after : (source.actualExecution (depth + 1)).after = funded.service.next :=
    (source.actualExecution (depth + 1)).after_exact.trans
      (congrArg (source.seed.law.next (source.currentAt (depth + 2))) word)
  exact ⟨word, after, (source.actualExecution (depth + 1)).root_next_exact.symm.trans after⟩

theorem finance_is_in_actual_execution (depth : Nat)
    (funded : Financing.FinancedPlan source.seed.law (source.currentAt (depth + 2))
      source.seed.task (source.seed.actionsAt (source.currentAt (depth + 2))) source.seed.budget source.terms)
    (generated : source.financedAt (source.currentAt (depth + 2)) = some funded) :
    funded.finance.issue ∈ (source.actualExecution (depth + 1)).interpreted.items ∧
    funded.finance.payout ∈ (source.actualExecution (depth + 1)).interpreted.items ∧
    source.seed.law.Valid funded.finance.issue.before funded.finance.issue.request ∧
    source.seed.law.Valid funded.finance.payout.before funded.finance.payout.request ∧
    funded.finance.payout.request.signer = source.terms.lender := by
  have actual := source.funded_plan_is_actual depth funded generated
  have items : (source.actualExecution (depth + 1)).interpreted.items =
      source.seed.law.rawItems (source.currentAt (depth + 2)) funded.service.word := by
    change (source.seed.law.execute (source.currentAt (depth + 2)) 0
      (source.actualExecution (depth + 1)).submitted).items = _
    rw [actual.1]
    rfl
  rw [items]
  exact ⟨funded.finance.issue_mem, funded.finance.payout_mem,
    funded.finance.issue_accepted, funded.finance.payout_accepted, funded.finance.lender_signed⟩

theorem actual_financing_balance (depth : Nat)
    (funded : Financing.FinancedPlan source.seed.law (source.currentAt (depth + 2))
      source.seed.task (source.seed.actionsAt (source.currentAt (depth + 2))) source.seed.budget source.terms)
    (generated : source.financedAt (source.currentAt (depth + 2)) = some funded) :
    source.seed.law.totalDebit (source.actualExecution (depth + 1)).interpreted.items
        source.terms.borrower (source.seed.law.settlementUnit source.terms.instrument) ≤
      source.terms.principal * source.seed.law.settlementRate source.terms.instrument ∧
    (source.actualExecution (depth + 1)).after.claims source.terms.instrument
        source.terms.borrower source.terms.lender =
      (source.actualExecution (depth + 1)).before.claims source.terms.instrument
        source.terms.borrower source.terms.lender + source.terms.principal ∧
    ∀ code debtor creditor, (code, debtor, creditor) ≠
        (source.terms.instrument, source.terms.borrower, source.terms.lender) →
      (source.actualExecution (depth + 1)).after.claims code debtor creditor =
        (source.actualExecution (depth + 1)).before.claims code debtor creditor := by
  have actual := source.funded_plan_is_actual depth funded generated
  refine ⟨?_, ?_, ?_⟩
  · change source.seed.law.totalDebit
      (source.seed.law.execute (source.currentAt (depth + 2)) 0
        (source.actualExecution (depth + 1)).submitted).items _ _ ≤ _
    rw [actual.1]
    exact funded.covers.1
  · rw [actual.2.1]
    exact funded.actual_net_principal
  · intro code debtor creditor other
    rw [actual.2.1]
    exact funded.other_claims_unchanged code debtor creditor other

def runningCurrent (depth : Nat) : (ProgrammeSource.V source.input).Current :=
  .running (source.currentAt (depth + 2))
    (ProgrammeSource.pastAt (ProgrammeHistory.visitAt source.input (depth + 2)).current)

theorem runningCurrent_is_original_visit (depth : Nat) :
    source.runningCurrent depth = (ProgrammeHistory.visitAt source.input (depth + 2)).current := by
  unfold runningCurrent currentAt
  change ProgrammeSource.Current.running
    (ProgrammeSource.rawCurrent source.input (ProgrammeSource.next source.input
      (ProgrammeHistory.visitAt source.input (depth + 1)).current))
    (ProgrammeSource.pastAt (ProgrammeSource.next source.input
      (ProgrammeHistory.visitAt source.input (depth + 1)).current)) =
    ProgrammeSource.next source.input (ProgrammeHistory.visitAt source.input (depth + 1)).current
  cases (ProgrammeHistory.visitAt source.input (depth + 1)).current <;> rfl

def taskEntry (depth : Nat) :=
  ProgrammeSource.sourceEntry source.input (source.runningCurrent depth)
    (.instruction ⟨0, by change 0 < 1; decide⟩)

def taskWrite (depth : Nat) :=
  (ProgrammeLedger.evolution source.input (source.runningCurrent depth)).destination (source.taskEntry depth)

def writtenReceipt (depth : Nat) :=
  ProgrammeLedger.writtenTransferReceipt source.input (source.currentAt (depth + 2))
    (ProgrammeSource.pastAt (ProgrammeHistory.visitAt source.input (depth + 2)).current)
    (source.taskEntry depth)

theorem written_funded_report (depth : Nat)
    (funded : Financing.FinancedPlan source.seed.law (source.currentAt (depth + 2))
      source.seed.task (source.seed.actionsAt (source.currentAt (depth + 2))) source.seed.budget source.terms)
    (generated : source.financedAt (source.currentAt (depth + 2)) = some funded) :
    ProgrammeLedger.transferReceiptOf source.input (source.taskWrite depth).2 = some (source.writtenReceipt depth) ∧
    (source.writtenReceipt depth).val = .planning source.seed.law (source.currentAt (depth + 2))
      source.seed.task (source.seed.actionsAt (source.currentAt (depth + 2))) source.seed.budget (.paid funded.service) := by
  constructor
  · exact (ProgrammeLedger.destination_transfer_receipt source.input _ _ (source.taskEntry depth)).trans
      (congrArg some (ProgrammeLedger.writtenTransferReceipt_exact source.input _ _
        (source.taskEntry depth)).symm)
  · rw [(source.writtenReceipt depth).property]
    change source.reportAt (source.currentAt (depth + 2)) = _
    unfold reportAt
    rw [source.current_round, if_neg (by omega)]
    unfold outcomeAt
    rw [generated]

end FinancedSource

end SaturationMonoid.ProcessGame.Society.PublicFunction
