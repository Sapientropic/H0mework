import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.ArtifactZero.Regression

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 24000000

namespace SaturationMonoid.Tracks.LivingLawPublicArtifactZeroInstance

open ProcessGame.Society.PublicFunction
open ProcessGame.Society.PublicFunction.Productivity
open ProcessGame.Society.PublicFunction.Productivity.Cell
open ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation
open ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.ArtifactZero
open ProcessGame.Society.Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

abbrev publicArtifactZeroFacade := ArtifactZero.Runtime.facade
abbrev activated := ArtifactZero.Runtime.activated
abbrev rawCertificate := Raw.certify ⟨fun row _ => Raw.actual_raw_rows_hold row⟩
abbrev ledgerCertificate := Ledger.certify ⟨fun row _ => Ledger.actual_ledger_rows_hold row⟩

theorem both_replays_accept_the_same_original_trace :
    ArtifactZero.Runtime.projectionLaw.project .raw
      (ProgrammeSource.emitted productionSource.input (ProgrammeHistory.visitAt productionSource.input 24).current) () rfl =
        Raw.Result.verified rawCertificate ∧
      ArtifactZero.Runtime.projectionLaw.project .ledger
        (ProgrammeSource.emitted productionSource.input (ProgrammeHistory.visitAt productionSource.input 24).current) () rfl =
          Ledger.Result.verified ledgerCertificate ∧
      Raw.amount = 1 ∧ 0 < Raw.amount ∧ Ledger.amount = 1 ∧ 0 < Ledger.amount ∧
      (∀ index kind, (ledgerCertificate.newborn index kind).state.TerminalAt 0) ∧
      (∀ actor good, Raw.stockFromItems actor good = (productionSource.currentAt 25).stock actor good) ∧
      (∀ actor good, Ledger.inventory actor good = (productionSource.currentAt 25).stock actor good) ∧
      HEq (publicArtifactZeroFacade.readoutAt (activated 24) .raw)
        ((activated 24).tick.generated.projectionOutcome (.component .raw)) ∧
      HEq (publicArtifactZeroFacade.readoutAt (activated 24) .ledger)
        ((activated 24).tick.generated.projectionOutcome (.component .ledger)) ∧
      HEq (activated 24).tick.generated.wholeLedgerWriteBack
        ((activated 24).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt (activated 24).current.visit.current) ∧
      (activated 24).tick.nextCurrent = publicArtifactZeroFacade.process.stateAt
        (publicArtifactZeroFacade.process.successor (activated 24).state) := by
  have raw := publicArtifactZeroFacade.readoutAt_factorizes (activated 24) .raw
  have ledger := publicArtifactZeroFacade.readoutAt_factorizes (activated 24) .ledger
  exact ⟨Raw.actual_raw_certificate_is_generated, Ledger.actual_ledger_certificate_is_generated,
    rawCertificate.amount_positive.1, rawCertificate.amount_positive.2,
    ledgerCertificate.amount_positive.1, ledgerCertificate.amount_positive.2,
    ledgerCertificate.newborn_terminal, rawCertificate.complete.exact_inventory,
    ledgerCertificate.complete.exact_inventory, raw.2.2.2.1, ledger.2.2.2.1, raw.2.2.1, raw.2.2.2.2⟩

theorem every_new_source_birth_has_its_own_native_history (ordinal : Nat)
    (index : Fin (births (Nat.succ (activated ordinal).state)).length) (kind : Kind) :
    let visit : Nat := (activated ordinal).state
    let birth := discovered visit index
    let certificate := ArtifactZero.Runtime.projectionLaw.project (.newborn birth kind)
      (ProgrammeSource.emitted productionSource.input (ProgrammeHistory.visitAt productionSource.input visit).current)
      () visit (discovered_has_arrived visit index) rfl
    birth.ordinal ≤ visit ∧ certificate.service.state.history = certificate.service.run.events ∧
      birth.instructionOrigin.instruction? productionSource.input = some birth.item ∧
      (productionSource.actualExecution (visit - 1)).after = productionSource.currentAt (visit + 1) ∧
      HEq (publicArtifactZeroFacade.readoutAt (activated ordinal) (.newborn index kind))
        ((activated ordinal).tick.generated.projectionOutcome (.component (.newborn birth kind))) ∧
      HEq (activated ordinal).tick.generated.wholeLedgerWriteBack
        ((activated ordinal).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt (activated ordinal).current.visit.current) ∧
      (activated ordinal).tick.nextCurrent = publicArtifactZeroFacade.process.stateAt
        (publicArtifactZeroFacade.process.successor (activated ordinal).state) := by
  dsimp only
  let visit : Nat := (activated ordinal).state
  let birth := discovered visit index
  let certificate := ArtifactZero.Runtime.atVisit birth kind visit (discovered_has_arrived visit index)
  have factor := publicArtifactZeroFacade.readoutAt_factorizes (activated ordinal) (.newborn index kind)
  exact ⟨certificate.arrived, certificate.history, certificate.birth_origin, certificate.next,
    factor.2.2.2.1, factor.2.2.1, factor.2.2.2.2⟩

theorem next_copy_review_preserves_the_real_resource_deficit (index : Fin 2) :
    let review := ArtifactZero.Runtime.projectionLaw.project .readiness
      (ProgrammeSource.emitted productionSource.input (ProgrammeHistory.visitAt productionSource.input 24).current) () rfl index
    review.deficit ∈ Feedback.deficits (rawFrame 25).raw (daughter index) ∧
      (rawFrame 25).raw.stock (daughter index) review.deficit.good < review.deficit.required ∧
      (productionSource.actualExecution 23).after = (rawFrame 25).raw ∧
      HEq (publicArtifactZeroFacade.readoutAt (activated 24) .readiness)
        ((activated 24).tick.generated.projectionOutcome (.component .readiness)) ∧
      HEq (activated 24).tick.generated.wholeLedgerWriteBack
        ((activated 24).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt (activated 24).current.visit.current) ∧
      (activated 24).tick.nextCurrent = publicArtifactZeroFacade.process.stateAt
        (publicArtifactZeroFacade.process.successor (activated 24).state) := by
  dsimp only
  let review := copyReview index
  have factor := publicArtifactZeroFacade.readoutAt_factorizes (activated 24) .readiness
  exact ⟨review.original_deficit, review.deficit.short, review.actual_after,
    factor.2.2.2.1, factor.2.2.1, factor.2.2.2.2⟩

end SaturationMonoid.Tracks.LivingLawPublicArtifactZeroInstance
