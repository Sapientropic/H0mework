import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Settlement.Regression

set_option autoImplicit false

namespace SaturationMonoid.Tracks.LivingLawPublicSettlementInstance

open ProcessGame.Society.PublicFunction.Distributed.Reaction
open ProcessGame.Society.Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

abbrev seed := Settlement.Regression.seed
abbrev feasible := Settlement.Regression.original_is_feasible
abbrev source := Settlement.replacement seed feasible
abbrev oldSource := Settlement.original seed
abbrev publicSettlementFacade := Settlement.Runtime.facade seed feasible
abbrev originalSettlementFacade := Native.Runtime.facade oldSource
abbrev activated := Settlement.Runtime.activated seed feasible
abbrev oldActivated := Native.Runtime.activated oldSource

theorem actual_receipted_settlement_is_consumed_by_both_original_roots
    {Party Good Port Technology Instrument : Type}
    [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
    [DecidableEq Technology] [DecidableEq Instrument]
    (seed : Machine Party Good Port Technology Instrument) (feasible : seed.code.feasible seed.reference) :
    let actual := Settlement.Runtime.activated seed feasible (seed.history.length + 1)
    let oldActual := Native.Runtime.activated (Settlement.original seed) (seed.history.length + 1)
    (∀ index (_inside : index < (Settlement.before seed.code (Settlement.reference seed)
        (Settlement.history seed) (Settlement.table seed)).current.slots.length), ∀ holder,
      Settlement.received seed.code (Settlement.reference seed) (Settlement.history seed)
        (Settlement.table seed) index holder ≤
      Settlement.received seed.code (Settlement.selection seed feasible).policy.policy
        (Settlement.history seed) (Settlement.table seed) index holder) ∧
      Settlement.verify seed.code (Settlement.reference seed) (Settlement.selection seed feasible).policy.policy = true ∧
      HEq ((Settlement.Runtime.facade seed feasible).readoutAt actual .settlement)
        (actual.tick.generated.projectionOutcome (.component .settlement)) ∧
      HEq ((Settlement.Runtime.facade seed feasible).readoutAt actual (.previous .responsibilities))
        (actual.tick.generated.projectionOutcome (.inherited (.component ()))) ∧
      HEq ((Native.Runtime.facade (Settlement.original seed)).readoutAt oldActual .responsibilities)
        (oldActual.tick.generated.projectionOutcome (.component ())) ∧
      HEq actual.tick.generated.wholeLedgerWriteBack
        (actual.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt actual.current.visit.current) ∧
      HEq oldActual.tick.generated.wholeLedgerWriteBack
        (oldActual.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt oldActual.current.visit.current) ∧
      actual.tick.nextCurrent = (Settlement.Runtime.facade seed feasible).process.stateAt
        ((Settlement.Runtime.facade seed feasible).process.successor actual.state) ∧
      oldActual.tick.nextCurrent = (Native.Runtime.facade (Settlement.original seed)).process.stateAt
        ((Native.Runtime.facade (Settlement.original seed)).process.successor oldActual.state) := by
  have settlement := (Settlement.Runtime.facade seed feasible).readoutAt_factorizes
    (Settlement.Runtime.activated seed feasible (seed.history.length + 1)) .settlement
  have native := (Settlement.Runtime.facade seed feasible).readoutAt_factorizes
    (Settlement.Runtime.activated seed feasible (seed.history.length + 1)) (.previous .responsibilities)
  have old := (Native.Runtime.facade (Settlement.original seed)).readoutAt_factorizes
    (Native.Runtime.activated (Settlement.original seed) (seed.history.length + 1)) .responsibilities
  exact ⟨Settlement.actual_payment_receipts_do_not_regress seed feasible,
    Settlement.independent_replay_accepts_selection _ _ (Settlement.selection seed feasible),
    settlement.2.2.2.1, native.2.2.2.1, old.2.2.2.1, settlement.2.2.1, old.2.2.1,
    settlement.2.2.2.2, old.2.2.2.2⟩

theorem named_real_payment_is_a_strict_gain_and_preserves_both_actual_ledgers :
    (source.actualExecution 1).after.stock true () = (oldSource.actualExecution 1).after.stock true () ∧
      (source.actualExecution 1).after.stock false () = 2 ∧
      (oldSource.actualExecution 1).after.stock false () = 0 ∧
      Financial.outstanding source.input (Native.generate source 1).finance.current = 0 ∧
      Financial.outstanding oldSource.input (Native.generate oldSource 1).finance.current = 2 ∧
      HEq (publicSettlementFacade.readoutAt (activated 2) .settlement)
        ((activated 2).tick.generated.projectionOutcome (.component .settlement)) ∧
      HEq (activated 2).tick.generated.wholeLedgerWriteBack
        ((activated 2).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt (activated 2).current.visit.current) ∧
      HEq (oldActivated 2).tick.generated.wholeLedgerWriteBack
        ((oldActivated 2).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt (oldActivated 2).current.visit.current) ∧
      (activated 2).tick.nextCurrent = publicSettlementFacade.process.stateAt
        (publicSettlementFacade.process.successor (activated 2).state) ∧
      (oldActivated 2).tick.nextCurrent = originalSettlementFacade.process.stateAt
        (originalSettlementFacade.process.successor (oldActivated 2).state) := by
  rcases Settlement.Regression.actual_payment_replaces_material_destruction_and_keeps_the_original_issue with
    ⟨_issue, _newWord, _oldWord, newStock, oldStock, gain, previous, paid, unpaid, _slots, _verified⟩
  have settlement := publicSettlementFacade.readoutAt_factorizes (activated 2) .settlement
  have old := originalSettlementFacade.readoutAt_factorizes (oldActivated 2) .responsibilities
  exact ⟨newStock.trans oldStock.symm, gain, previous, paid, unpaid,
    settlement.2.2.2.1, settlement.2.2.1, old.2.2.1, settlement.2.2.2.2, old.2.2.2.2⟩

end SaturationMonoid.Tracks.LivingLawPublicSettlementInstance
