import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Learning

set_option autoImplicit false

namespace SaturationMonoid.Tracks.LivingLawPublicDistributedInstance

open ProcessGame.Society.PublicFunction
open ProcessGame.Society.PublicFunction.Distributed
open ProcessGame.Society.Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

abbrev productionSource := Distributed.Regression.source
abbrev publicDistributedFacade := Runtime.facade productionSource
abbrev activated := Runtime.activated productionSource

theorem generated_strategy_consumes_its_own_occurrence
    {Party Good Port Technology Instrument : Type}
    [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
    (source : Distributed.Source Party Good Port Technology Instrument)
    (choice : source.code.Selection source.reference)
    (generated : source.answer = .selected choice) :
    let facade := Runtime.facade source
    let actual := Runtime.activated source (source.history.length + 1)
    (source.actualExecution source.history.length).submitted =
        (source.code.executed choice.policy.policy (source.history, source.events)).word ∧
      ServiceAdequate source.code.law (source.actualExecution source.history.length).before source.code.task
        (source.actualExecution source.history.length).submitted ∧
      source.currentAt (source.history.length + 2) = source.code.law.next
        (source.code.historyCurrent source.history)
        (source.code.executed choice.policy.policy (source.history, source.events)).word ∧
      source.code.verify source.reference choice.policy.policy = true ∧
      (∀ other ∈ source.code.policies, source.code.feasible other →
        ¬ source.code.StrictlyImproves choice.policy.policy other) ∧
      HEq (facade.readoutAt actual .synthesis) (actual.tick.generated.projectionOutcome (.component ())) ∧
      HEq actual.tick.generated.wholeLedgerWriteBack
        (actual.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt actual.current.visit.current) ∧
      actual.tick.nextCurrent = facade.process.stateAt (facade.process.successor actual.state) := by
  have paid := source.selected_plan_is_paid_on_its_own_root choice generated
  have factor := (Runtime.facade source).readoutAt_factorizes
    (Runtime.activated source (source.history.length + 1)) .synthesis
  exact ⟨paid.1, paid.2.1, paid.2.2.1, paid.2.2.2,
    source.code.selected_has_no_feasible_improvement source.reference choice,
    factor.2.2.2.1, factor.2.2.1, factor.2.2.2.2⟩

theorem actual_observation_program_saves_material_without_erasing_debt :
    Distributed.Regression.isSelected productionSource.answer = true ∧
      (productionSource.actualExecution 0).submitted =
        [Distributed.Regression.transfer, Distributed.Regression.transfer, Distributed.Regression.use] ∧
      (productionSource.actualExecution 0).after.stock false () = 1 ∧
      (productionSource.actualExecution 0).after.claims () true false = 7 :=
  Distributed.Regression.actual_strict_improvement_is_generated

theorem paid_local_information_repairs_the_hidden_history_obstruction :
    Distributed.Learning.code.feasible Distributed.Learning.reference ∧
      Distributed.Learning.isSelected (Distributed.Learning.code.compile Distributed.Learning.reference) = true ∧
      ((Distributed.Learning.source false).actualExecution 0).after.stock true true = 0 ∧
      ((Distributed.Learning.source true).actualExecution 1).after.stock false false = 1 :=
  ⟨Distributed.Learning.the_same_local_program_solves_both_histories_after_paid_observation.2,
    Distributed.Learning.paid_observation_generates_a_feasible_selection,
    Distributed.Learning.both_actual_sources_pay_for_the_observation_and_the_task.1,
    Distributed.Learning.both_actual_sources_pay_for_the_observation_and_the_task.2.2.2.2.1⟩

end SaturationMonoid.Tracks.LivingLawPublicDistributedInstance
