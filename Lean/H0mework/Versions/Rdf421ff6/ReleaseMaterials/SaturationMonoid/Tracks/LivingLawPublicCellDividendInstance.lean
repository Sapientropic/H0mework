import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Regression

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

namespace SaturationMonoid.Tracks.LivingLawPublicCellDividendInstance

open ProcessGame.Society.PublicFunction
open ProcessGame.Society.PublicFunction.Productivity
open ProcessGame.Society.PublicFunction.Productivity.Cell
open ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit
open ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program
open ProcessGame.Society.Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

abbrev productionSource := SharedAudit.source
abbrev publicCellDividendFacade := SharedAudit.Runtime.facade
abbrev activated := SharedAudit.Runtime.activated

theorem paid_schema_is_generated_in_the_original_root :
    let certificate := SharedAudit.Runtime.projectionLaw.project .method
      (ProgrammeSource.emitted productionSource.input (ProgrammeHistory.visitAt productionSource.input 4).current) () rfl
    certificate.method.item ∈ (productionSource.actualExecution 3).interpreted.items ∧
      flowAt (law.actualDebit certificate.method.item.before certificate.method.item.request) 0 .labor = 1 ∧
      (SharedAudit.frameAt 5).method = some certificate.method ∧
      (productionSource.actualExecution 3).after = productionSource.currentAt 5 ∧
      HEq (publicCellDividendFacade.readoutAt (activated 4) .method)
        ((activated 4).tick.generated.projectionOutcome (.component .method)) ∧
      HEq (activated 4).tick.generated.wholeLedgerWriteBack
        ((activated 4).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt (activated 4).current.visit.current) ∧
      (activated 4).tick.nextCurrent = publicCellDividendFacade.process.stateAt
        (publicCellDividendFacade.process.successor (activated 4).state) := by
  dsimp only
  let certificate := SharedAudit.Runtime.methodCertificate
  have factor := publicCellDividendFacade.readoutAt_factorizes (activated 4) .method
  exact ⟨certificate.original, certificate.paid, certificate.stored, certificate.next,
    factor.2.2.2.1, factor.2.2.1, factor.2.2.2.2⟩

theorem strict_cell_dividend_and_full_responsibility_are_in_the_original_root :
    let certificate := SharedAudit.Runtime.projectionLaw.project .dividend
      (ProgrammeSource.emitted productionSource.input (ProgrammeHistory.visitAt productionSource.input 10).current) () rfl
    certificate.amount = 1 ∧ 0 < certificate.amount ∧
      (∀ actor good, law.totalDebit (SharedAudit.receipts productionSource 11) actor good +
        (if actor = 0 ∧ good = .labor then 1 else 0) = law.totalDebit (SharedAudit.receipts Cell.source 11) actor good) ∧
      (∀ actor good, law.totalCredit (SharedAudit.receipts productionSource 11) actor good =
        law.totalCredit (SharedAudit.receipts Cell.source 11) actor good) ∧
      productionSource.currentAt 11 = SharedAudit.withLabor (Cell.source.currentAt 11) 1 ∧
      (productionSource.actualExecution 6).submitted = certificate.method.method.plan 2 ∧
      (∀ index, (certificate.native index).state = (OutstandingSource.NativeService.historyAt productionSource index 1).state) ∧
      Financial.BalanceConservation.ledgerClaims productionSource.input (SharedAudit.financialAccount 11).current =
        (productionSource.currentAt 11).claims ∧
      Nonempty ((Financial.process productionSource.input).Run
        (SharedAudit.financialAccount 0).current (SharedAudit.financialAccount 11).current) ∧
      ProgrammeLedger.transferReceiptOf productionSource.input (productionSource.taskWrite 9).2 =
        some (productionSource.writtenReceipt 9) ∧
      (productionSource.actualExecution 9).after = productionSource.currentAt 11 ∧
      HEq (publicCellDividendFacade.readoutAt (activated 10) .dividend)
        ((activated 10).tick.generated.projectionOutcome (.component .dividend)) ∧
      HEq (activated 10).tick.generated.wholeLedgerWriteBack
        ((activated 10).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt (activated 10).current.visit.current) ∧
      (activated 10).tick.nextCurrent = publicCellDividendFacade.process.stateAt
        (publicCellDividendFacade.process.successor (activated 10).state) := by
  dsimp only
  let certificate := SharedAudit.Runtime.certificate
  have factor := publicCellDividendFacade.readoutAt_factorizes (activated 10) .dividend
  exact ⟨certificate.generated_amount.trans exact_strict_labor_dividend.1, certificate.positive,
    certificate.debits, certificate.credits, certificate.carrier, certificate.reuse, certificate.archives,
    certificate.finance, ⟨certificate.financeRun⟩, certificate.row, certificate.next,
    factor.2.2.2.1, factor.2.2.1, factor.2.2.2.2⟩

theorem every_old_legal_continuation_keeps_the_actual_dividend (word : List RequestAt)
    (accepted : ∀ item ∈ law.rawItems (Cell.source.currentAt 11) word, law.Valid item.before item.request) :
    (∀ item ∈ law.rawItems (productionSource.currentAt 11) word, law.Valid item.before item.request) ∧
      (law.execute (productionSource.currentAt 11) 0 word).final =
        SharedAudit.withLabor (law.execute (Cell.source.currentAt 11) 0 word).final 1 :=
  SharedAudit.Runtime.certificate.continuation word accepted

end SaturationMonoid.Tracks.LivingLawPublicCellDividendInstance
