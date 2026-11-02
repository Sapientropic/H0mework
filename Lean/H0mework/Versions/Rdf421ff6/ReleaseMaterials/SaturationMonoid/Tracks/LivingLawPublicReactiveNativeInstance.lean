import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Regression

set_option autoImplicit false

namespace SaturationMonoid.Tracks.LivingLawPublicReactiveNativeInstance

open ProcessGame.Society.PublicFunction
open ProcessGame.Society.PublicFunction.Distributed.Reaction
open ProcessGame.Society.Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

abbrev productionSource := Native.Regression.source
abbrev originalSource := productionSource.withSide .original
abbrev originalReactiveNativeFacade := Native.Runtime.facade originalSource
abbrev publicReactiveNativeFacade := Native.Runtime.facade productionSource
abbrev publicReactiveAuthorityFacade := Native.AuthorityRuntime.facade Native.Regression.bound
abbrev activated := Native.Runtime.activated productionSource

theorem selected_actual_services_and_finance_are_consumed_by_both_original_roots
    {Party Good Port Technology Instrument : Type}
    [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
    [DecidableEq Technology] [DecidableEq Instrument]
    (source : Machine Party Good Port Technology Instrument)
    (choice : Selection source.code source.reference) (selected : source.answer = .selected choice)
    (originalFeasible : source.code.feasible source.reference)
    (eligible : source.code.eligible (trace source.code source.reference source.history source.opponent) = true) :
    let new := source.withSide .replacement
    let old := source.withSide .original
    let newActual := Native.Runtime.activated new (source.history.length + 1)
    let oldActual := Native.Runtime.activated old (source.history.length + 1)
    (∀ metric, new.actualScore metric ≤ old.actualScore metric) ∧
      (∀ index, ((Native.generate new source.history.length).services index).state.TerminalAt 0) ∧
      (∀ index, ((Native.generate old source.history.length).services index).state.TerminalAt 0) ∧
      HEq ((Native.Runtime.facade new).readoutAt newActual .responsibilities)
        (newActual.tick.generated.projectionOutcome (.component ())) ∧
      HEq ((Native.Runtime.facade old).readoutAt oldActual .responsibilities)
        (oldActual.tick.generated.projectionOutcome (.component ())) ∧
      HEq ((Native.Runtime.facade new).readoutAt newActual (.previous .receipts))
        (newActual.tick.generated.projectionOutcome (.inherited (.component .receipts))) ∧
      HEq newActual.tick.generated.wholeLedgerWriteBack
        (newActual.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt newActual.current.visit.current) ∧
      HEq oldActual.tick.generated.wholeLedgerWriteBack
        (oldActual.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt oldActual.current.visit.current) ∧
      newActual.tick.nextCurrent = (Native.Runtime.facade new).process.stateAt
        ((Native.Runtime.facade new).process.successor newActual.state) ∧
      oldActual.tick.nextCurrent = (Native.Runtime.facade old).process.stateAt
        ((Native.Runtime.facade old).process.successor oldActual.state) := by
  have paid := Native.selected_and_original_native_services_are_actually_settled source choice selected originalFeasible eligible
  have new := (Native.Runtime.facade (source.withSide .replacement)).readoutAt_factorizes
    (Native.Runtime.activated (source.withSide .replacement) (source.history.length + 1)) .responsibilities
  have old := (Native.Runtime.facade (source.withSide .original)).readoutAt_factorizes
    (Native.Runtime.activated (source.withSide .original) (source.history.length + 1)) .responsibilities
  have receipts := (Native.Runtime.facade (source.withSide .replacement)).readoutAt_factorizes
    (Native.Runtime.activated (source.withSide .replacement) (source.history.length + 1)) (.previous .receipts)
  exact ⟨source.same_opponent_compares_both_actual_sources choice selected, paid.2, paid.1,
    new.2.2.2.1, old.2.2.2.1, receipts.2.2.2.1, new.2.2.1, old.2.2.1, new.2.2.2.2, old.2.2.2.2⟩

theorem original_services_all_actual_grants_and_finance_share_one_root
    {Party Good Port Technology Instrument : Type}
    [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
    [DecidableEq Technology] [DecidableEq Instrument]
    (bound : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument)) (depth : Nat) :
    let actual := Native.AuthorityRuntime.activated bound (depth + 1)
    HEq ((Native.AuthorityRuntime.facade bound).readoutAt actual .responsibilities)
      (actual.tick.generated.projectionOutcome (.component ())) ∧
      HEq ((Native.AuthorityRuntime.facade bound).readoutAt actual (.previous .responsibilities))
        (actual.tick.generated.projectionOutcome (.inherited (.component ()))) ∧
      HEq actual.tick.generated.wholeLedgerWriteBack
        (actual.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt actual.current.visit.current) ∧
      actual.tick.nextCurrent = (Native.AuthorityRuntime.facade bound).process.stateAt
        ((Native.AuthorityRuntime.facade bound).process.successor actual.state) := by
  have all := (Native.AuthorityRuntime.facade bound).readoutAt_factorizes
    (Native.AuthorityRuntime.activated bound (depth + 1)) .responsibilities
  have joint := (Native.AuthorityRuntime.facade bound).readoutAt_factorizes
    (Native.AuthorityRuntime.activated bound (depth + 1)) (.previous .responsibilities)
  exact ⟨all.2.2.2.1, joint.2.2.2.1, all.2.2.1, all.2.2.2.2⟩

theorem named_native_sources_consume_their_actual_archives_and_own_next :
    Native.Regression.serviceKinds productionSource 0 ⟨0, by decide⟩ = [true] ∧
      Native.Regression.serviceKinds originalSource 0 ⟨0, by decide⟩ = [true] ∧
      HEq (publicReactiveNativeFacade.readoutAt (activated 1) .responsibilities)
        ((activated 1).tick.generated.projectionOutcome (.component ())) ∧
      HEq (originalReactiveNativeFacade.readoutAt (Native.Runtime.activated originalSource 1) .responsibilities)
        ((Native.Runtime.activated originalSource 1).tick.generated.projectionOutcome (.component ())) ∧
      HEq (activated 1).tick.generated.wholeLedgerWriteBack
        ((activated 1).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt (activated 1).current.visit.current) ∧
      (activated 1).tick.nextCurrent = publicReactiveNativeFacade.process.stateAt
        (publicReactiveNativeFacade.process.successor (activated 1).state) := by
  have new := publicReactiveNativeFacade.readoutAt_factorizes (activated 1) .responsibilities
  have old := originalReactiveNativeFacade.readoutAt_factorizes (Native.Runtime.activated originalSource 1) .responsibilities
  exact ⟨Native.Regression.actual_selected_service_has_a_native_archive.1,
    Native.Regression.actual_selected_service_has_a_native_archive.2,
    new.2.2.2.1, old.2.2.2.1, new.2.2.1, new.2.2.2.2⟩

theorem named_authority_source_consumes_unpaid_services_grant_and_original_principal :
    (Native.Regression.authoritySource.actualExecution 0).after.technology.holder = none ∧
      Native.Regression.serviceKinds Native.Regression.authoritySource 0 ⟨0, by decide⟩ = [false] ∧
      Native.Regression.serviceKinds Native.Regression.authoritySource 0 ⟨1, by decide⟩ = [false] ∧
      (Native.Authority.generate Native.Regression.bound 1).mandates.length = 1 ∧
      Financial.outstanding Native.Regression.authoritySource.input
        (Native.generate Native.Regression.authoritySource 1).finance.current = 2 ∧
      HEq (publicReactiveAuthorityFacade.readoutAt (Native.AuthorityRuntime.activated Native.Regression.bound 2) .responsibilities)
        ((Native.AuthorityRuntime.activated Native.Regression.bound 2).tick.generated.projectionOutcome (.component ())) ∧
      HEq (Native.AuthorityRuntime.activated Native.Regression.bound 2).tick.generated.wholeLedgerWriteBack
        ((Native.AuthorityRuntime.activated Native.Regression.bound 2).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          (Native.AuthorityRuntime.activated Native.Regression.bound 2).current.visit.current) ∧
      (Native.AuthorityRuntime.activated Native.Regression.bound 2).tick.nextCurrent = publicReactiveAuthorityFacade.process.stateAt
        (publicReactiveAuthorityFacade.process.successor (Native.AuthorityRuntime.activated Native.Regression.bound 2).state) := by
  have actual := Native.Regression.actual_exit_keeps_all_original_services_grants_and_new_principal
  have factor := publicReactiveAuthorityFacade.readoutAt_factorizes
    (Native.AuthorityRuntime.activated Native.Regression.bound 2) .responsibilities
  exact ⟨actual.1, actual.2.1, actual.2.2.1, actual.2.2.2.2.1, actual.2.2.2.2.2.2,
    factor.2.2.2.1, factor.2.2.1, factor.2.2.2.2⟩

end SaturationMonoid.Tracks.LivingLawPublicReactiveNativeInstance
