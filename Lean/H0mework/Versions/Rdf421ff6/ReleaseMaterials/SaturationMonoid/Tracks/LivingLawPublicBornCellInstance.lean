import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Born.Regression

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

namespace SaturationMonoid.Tracks.LivingLawPublicBornCellInstance

open ProcessGame.Society.PublicFunction
open ProcessGame.Society.PublicFunction.Productivity
open ProcessGame.Society.PublicFunction.Productivity.Cell
open ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit
open ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Born
open ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program
open ProcessGame.Society.Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

abbrev productionSource := SharedAudit.source
abbrev publicBornCellFacade := Born.Runtime.facade
abbrev activated := Born.Runtime.activated

theorem every_born_service_run_is_in_its_own_original_visit (ordinal : Nat)
    (index : Fin (births (Nat.succ (activated ordinal).state)).length) (kind : Born.Kind) :
    let visit : Nat := (activated ordinal).state
    let birth := discovered visit index
    let certificate := Born.Runtime.projectionLaw.project (.newborn birth kind)
      (ProgrammeSource.emitted productionSource.input (ProgrammeHistory.visitAt productionSource.input visit).current)
      () visit (discovered_has_arrived visit index) rfl
    birth.ordinal ≤ visit ∧
      birth.instructionOrigin.instruction? productionSource.input = some birth.item ∧
      certificate.admission.state.LiveAt 0 ∧
      certificate.service.state.history = certificate.service.run.events ∧
      Financial.BalanceConservation.ledgerClaims productionSource.input (financialAccount (visit + 1)).current =
        (productionSource.currentAt (visit + 1)).claims ∧
      ProgrammeLedger.transferReceiptOf productionSource.input (productionSource.taskWrite (visit - 1)).2 =
        some (productionSource.writtenReceipt (visit - 1)) ∧
      (productionSource.actualExecution (visit - 1)).after = productionSource.currentAt (visit + 1) ∧
      HEq (publicBornCellFacade.readoutAt (activated ordinal) (.newborn index kind))
        ((activated ordinal).tick.generated.projectionOutcome (.component (.newborn birth kind))) ∧
      HEq (activated ordinal).tick.generated.wholeLedgerWriteBack
        ((activated ordinal).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt (activated ordinal).current.visit.current) ∧
      (activated ordinal).tick.nextCurrent = publicBornCellFacade.process.stateAt
        (publicBornCellFacade.process.successor (activated ordinal).state) := by
  dsimp only
  let visit : Nat := (activated ordinal).state
  let birth := discovered visit index
  let certificate := Born.Runtime.atVisit birth kind visit (discovered_has_arrived visit index)
  have factor := publicBornCellFacade.readoutAt_factorizes (activated ordinal) (.newborn index kind)
  exact ⟨certificate.arrived, birth.instruction_decodes_the_original_item, certificate.initially_live,
    certificate.exact_history, certificate.finance, certificate.row, certificate.next,
    factor.2.2.2.1, factor.2.2.1, factor.2.2.2.2⟩

theorem actual_two_generations_have_new_responsibilities_and_the_strict_dividend :
    let certificate := Born.Runtime.projectionLaw.project .family
      (ProgrammeSource.emitted productionSource.input (ProgrammeHistory.visitAt productionSource.input 10).current) () rfl
    certificate.births.length = 4 ∧ (certificate.births.map birthKey).Nodup ∧
      (∀ index kind, (Native.initial (born index) kind).state.LiveAt 0) ∧
      (∀ index kind, (certificate.services index kind).state.TerminalAt 0) ∧
      (∀ index kind later,
        (Native.historyAt (born index) kind (11 - (born index).ordinal + later)).state =
          (certificate.services index kind).state) ∧
      (∀ index, (certificate.cells index).item.request.operation = .produce (born index).child ∧
        0 < (certificate.cells index).item.before.stock (born index).child .seed) ∧
      certificate.baseline.amount = 1 ∧ 0 < certificate.baseline.amount ∧
      productionSource.currentAt 11 = withLabor (Cell.source.currentAt 11) 1 ∧
      ProgrammeLedger.transferReceiptOf productionSource.input (productionSource.taskWrite 9).2 =
        some (productionSource.writtenReceipt 9) ∧
      (productionSource.actualExecution 9).after = productionSource.currentAt 11 ∧
      HEq (publicBornCellFacade.readoutAt (activated 10) .family)
        ((activated 10).tick.generated.projectionOutcome (.component .family)) ∧
      HEq (activated 10).tick.generated.wholeLedgerWriteBack
        ((activated 10).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt (activated 10).current.visit.current) ∧
      (activated 10).tick.nextCurrent = publicBornCellFacade.process.stateAt
        (publicBornCellFacade.process.successor (activated 10).state) := by
  dsimp only
  let certificate := Born.Runtime.certificate
  have factor := publicBornCellFacade.readoutAt_factorizes (activated 10) .family
  exact ⟨certificate.births_generated ▸ four_births, certificate.keys, certificate.initially_live,
    certificate.terminal, certificate.future_archive,
    (fun index => ⟨(certificate.cells index).operation, (certificate.cells index).seed⟩),
    certificate.baseline.generated_amount.trans exact_strict_labor_dividend.1,
    certificate.baseline.positive, certificate.baseline.carrier, certificate.row, certificate.next,
    factor.2.2.2.1, factor.2.2.1, factor.2.2.2.2⟩

end SaturationMonoid.Tracks.LivingLawPublicBornCellInstance
