import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Regression

set_option autoImplicit false

namespace SaturationMonoid.Tracks.LivingLawPublicReactiveComparisonInstance

open ProcessGame.Society.PublicFunction
open ProcessGame.Society.PublicFunction.Distributed
open ProcessGame.Society.PublicFunction.Distributed.Reaction
open ProcessGame.Society.Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

abbrev productionSource := Reaction.Regression.source.withSide .replacement
abbrev originalSource := Reaction.Regression.source.withSide .original
abbrev publicReactionFacade := Reaction.Runtime.facade productionSource
abbrev originalReactionFacade := Reaction.Runtime.facade originalSource
abbrev activated := Reaction.Runtime.activated productionSource

theorem same_opponent_comparison_is_consumed_by_both_original_roots
    {Party Good Port Technology Instrument : Type}
    [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
    [DecidableEq Technology] [DecidableEq Instrument]
    (source : Machine Party Good Port Technology Instrument)
    (choice : Reaction.Selection source.code source.reference)
    (generated : source.answer = .selected choice) :
    let new := source.withSide .replacement
    let old := source.withSide .original
    let newFacade := Reaction.Runtime.facade new
    let oldFacade := Reaction.Runtime.facade old
    let newActual := Reaction.Runtime.activated new (source.history.length + 1)
    let oldActual := Reaction.Runtime.activated old (source.history.length + 1)
    (∀ metric, new.actualScore metric ≤ old.actualScore metric) ∧
      Reaction.verify source.code source.reference choice.policy.policy = true ∧
      (∀ other ∈ source.code.policies, source.code.feasible other →
        ¬ StrictAgainstEveryOpponent source.code choice.policy.policy other) ∧
      HEq (newFacade.readoutAt newActual .receipts)
        (newActual.tick.generated.projectionOutcome (.component .receipts)) ∧
      HEq (oldFacade.readoutAt oldActual .receipts)
        (oldActual.tick.generated.projectionOutcome (.component .receipts)) ∧
      HEq (newFacade.readoutAt newActual .opponentKeys)
        (newActual.tick.generated.projectionOutcome (.component .opponentKeys)) ∧
      HEq newActual.tick.generated.wholeLedgerWriteBack
        (newActual.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt newActual.current.visit.current) ∧
      HEq oldActual.tick.generated.wholeLedgerWriteBack
        (oldActual.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt oldActual.current.visit.current) ∧
      newActual.tick.nextCurrent = newFacade.process.stateAt (newFacade.process.successor newActual.state) ∧
      oldActual.tick.nextCurrent = oldFacade.process.stateAt (oldFacade.process.successor oldActual.state) := by
  have newFactor := (Reaction.Runtime.facade (source.withSide .replacement)).readoutAt_factorizes
    (Reaction.Runtime.activated (source.withSide .replacement) (source.history.length + 1)) .receipts
  have oldFactor := (Reaction.Runtime.facade (source.withSide .original)).readoutAt_factorizes
    (Reaction.Runtime.activated (source.withSide .original) (source.history.length + 1)) .receipts
  have keys := (Reaction.Runtime.facade (source.withSide .replacement)).readoutAt_factorizes
    (Reaction.Runtime.activated (source.withSide .replacement) (source.history.length + 1)) .opponentKeys
  exact ⟨source.same_opponent_compares_both_actual_sources choice generated,
    independent_replay_accepts_selection source.code source.reference choice,
    selected_is_nondominated_against_all_history_adaptive_opponents source.code source.reference choice,
    newFactor.2.2.2.1, oldFactor.2.2.2.1, keys.2.2.2.1, newFactor.2.2.1, oldFactor.2.2.1,
    newFactor.2.2.2.2, oldFactor.2.2.2.2⟩

theorem actual_strict_material_dividend_preserves_both_original_claim_ledgers :
    (productionSource.actualExecution 0).after.stock true () = 2 ∧
      (originalSource.actualExecution 0).after.stock true () = 1 ∧
      (productionSource.actualExecution 0).after.claims () true false = 7 ∧
      (originalSource.actualExecution 0).after.claims () true false = 7 := by
  have actual := Reaction.Regression.both_source_occurrences_are_paid_and_preserve_original_claims
  exact ⟨actual.2.2.2.1, actual.2.2.1, actual.2.2.2.2.2, actual.2.2.2.2.1⟩

end SaturationMonoid.Tracks.LivingLawPublicReactiveComparisonInstance
