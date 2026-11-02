import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.Regression

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 32000000

namespace SaturationMonoid.Tracks.LivingLawPublicCellParticipationInstance

open ProcessGame.Society.PublicFunction
open ProcessGame.Society.PublicFunction.Productivity
open ProcessGame.Society.PublicFunction.Productivity.Cell
open ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit
open ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation
open ProcessGame.Society.Institutions.Capitalism.Universal.Root
open ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

abbrev productionSource := Participation.source true
abbrev publicCellParticipationFacade := Participation.Runtime.facade
abbrev activated := Participation.Runtime.activated

theorem every_dialogue_has_its_own_native_history_and_original_next
    (ordinal : Nat) (arrived : 12 ≤ ordinal) :
    let certificate := Participation.Runtime.projectionLaw.project .dialogue
      (ProgrammeSource.emitted productionSource.input (ProgrammeHistory.visitAt productionSource.input ordinal).current)
      () ordinal arrived rfl
    certificate.dialogue.state.history = certificate.dialogue.run.events ∧
      certificate.dialogue.state.slots = [.live (Participation.Native.obligation true)] ∧
      (∀ slot, (certificate.old_services slot).state =
        (OutstandingSource.NativeService.historyAt productionSource slot 1).state) ∧
      Financial.BalanceConservation.ledgerClaims productionSource.input
        (account true (ordinal + 1)).current = (productionSource.currentAt (ordinal + 1)).claims ∧
      ProgrammeLedger.transferReceiptOf productionSource.input (productionSource.taskWrite (ordinal - 1)).2 =
        some (productionSource.writtenReceipt (ordinal - 1)) ∧
      (productionSource.actualExecution (ordinal - 1)).after = productionSource.currentAt (ordinal + 1) ∧
      HEq (publicCellParticipationFacade.readoutAt (activated ordinal) .dialogue)
        ((activated ordinal).tick.generated.projectionOutcome (.component .dialogue)) ∧
      HEq (activated ordinal).tick.generated.wholeLedgerWriteBack
        ((activated ordinal).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt (activated ordinal).current.visit.current) ∧
      (activated ordinal).tick.nextCurrent = publicCellParticipationFacade.process.stateAt
        (publicCellParticipationFacade.process.successor (activated ordinal).state) := by
  dsimp only
  let certificate := Participation.Runtime.atVisit ordinal arrived
  have factor := publicCellParticipationFacade.readoutAt_factorizes (activated ordinal) .dialogue
  exact ⟨certificate.exact_history, certificate.original_responsibility, certificate.old_archives,
    certificate.full_claims, certificate.row, certificate.next,
    factor.2.2.2.1, factor.2.2.1, factor.2.2.2.2⟩

theorem actual_paid_exit_public_production_and_strict_dividend_are_in_one_root :
    let certificate := Participation.Runtime.projectionLaw.project .complete
      (ProgrammeSource.emitted productionSource.input (ProgrammeHistory.visitAt productionSource.input 24).current) () rfl
    certificate.current.dialogue.state.history.map LifecycleEvent.kind =
      [.admitted, .maintained, .deferred, .maintained, .bearerRelease, .maintained] ∧
      certificate.current.dialogue.state.history = certificate.current.dialogue.run.events ∧
      certificate.current.dialogue.state.slots = [.live (Participation.Native.obligation true)] ∧
      (∀ index kind, (certificate.newborn index kind).original.state.TerminalAt 0) ∧
      (frameAt true 21).register 1 = .released ∧ (frameAt true 21).register 2 = .declined ∧
      law.Valid (frameAt true 21).raw (audit 1) ∧ (wordAt true 21 (frameAt true 21)).isEmpty = true ∧
      (frameAt true 22).register 1 = .released ∧
      (frameAt true 23).raw.stock 1 .seed = (frameAt true 22).raw.stock 1 .seed + 2 ∧
      (frameAt true 25).register 1 = .active ∧
      certificate.amount = 1 ∧ 0 < certificate.amount ∧
      productionSource.currentAt 25 = withLabor ((Participation.source false).currentAt 25) 1 ∧
      ProgrammeLedger.transferReceiptOf productionSource.input (productionSource.taskWrite 23).2 =
        some (productionSource.writtenReceipt 23) ∧
      (productionSource.actualExecution 23).after = productionSource.currentAt 25 ∧
      HEq (publicCellParticipationFacade.readoutAt (activated 24) .complete)
        ((activated 24).tick.generated.projectionOutcome (.component .complete)) ∧
      HEq (activated 24).tick.generated.wholeLedgerWriteBack
        ((activated 24).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt (activated 24).current.visit.current) ∧
      (activated 24).tick.nextCurrent = publicCellParticipationFacade.process.stateAt
        (publicCellParticipationFacade.process.successor (activated 24).state) := by
  dsimp only
  let certificate := Participation.Runtime.certificate
  have factor := publicCellParticipationFacade.readoutAt_factorizes (activated 24) .complete
  exact ⟨certificate.boundaries, certificate.current.exact_history, certificate.current.original_responsibility,
    (fun index kind => (certificate.newborn index kind).terminal),
    certificate.chosen_silence.1, certificate.chosen_silence.2.1, certificate.chosen_silence.2.2.1,
    certificate.chosen_silence.2.2.2, certificate.own_production.1, certificate.own_production.2.2.2.1,
    certificate.voluntary_return.2.2.1, certificate.generated_amount.trans extended_strict_dividend.1,
    certificate.positive, certificate.carrier, certificate.current.row, certificate.current.next,
    factor.2.2.2.1, factor.2.2.1, factor.2.2.2.2⟩

end SaturationMonoid.Tracks.LivingLawPublicCellParticipationInstance
