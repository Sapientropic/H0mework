import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Identity.Regression

set_option autoImplicit false

namespace SaturationMonoid.Tracks.LivingLawPublicNativeIdentityInstance

open ProcessGame.Society.PublicFunction
open ProcessGame.Society.PublicFunction.Distributed.Reaction
open ProcessGame.Society.Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

abbrev seed := Identity.Regression.seed
abbrev feasible := Identity.Regression.original_is_feasible
abbrev source := Identity.replacement seed feasible
abbrev oldSource := Identity.original seed
abbrev publicNativeIdentityFacade := Identity.Runtime.facade seed feasible
abbrev originalNativeIdentityFacade := Native.Runtime.facade oldSource
abbrev activated := Identity.Runtime.activated seed feasible
abbrev oldActivated := Native.Runtime.activated oldSource

theorem selected_native_counterparts_are_consumed_by_their_actual_roots
    {Party Good Port Technology Instrument : Type}
    [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
    [DecidableEq Technology] [DecidableEq Instrument]
    (seed : Machine Party Good Port Technology Instrument) (feasible : seed.code.feasible seed.reference) :
    let new := Identity.replacement seed feasible
    let old := Identity.original seed
    let actual := Identity.Runtime.activated seed feasible (seed.history.length + 1)
    let oldActual := Native.Runtime.activated old (seed.history.length + 1)
    (∀ index (inside : index < (Native.generate old seed.history.length).finance.current.slots.length),
      ∃ replacement ∈ (Native.generate new seed.history.length).finance.current.slots,
        Identity.DebtCorrespondence seed.code old.input new.input
          (Native.generate old seed.history.length).finance.current.slots[index] replacement) ∧
      Identity.verify seed.code (Identity.reference seed) (Identity.selection seed feasible).policy.policy = true ∧
      HEq ((Identity.Runtime.facade seed feasible).readoutAt actual .identities)
        (actual.tick.generated.projectionOutcome (.component .identities)) ∧
      HEq ((Identity.Runtime.facade seed feasible).readoutAt actual (.previous .responsibilities))
        (actual.tick.generated.projectionOutcome (.inherited (.component ()))) ∧
      HEq ((Native.Runtime.facade old).readoutAt oldActual .responsibilities)
        (oldActual.tick.generated.projectionOutcome (.component ())) ∧
      HEq actual.tick.generated.wholeLedgerWriteBack
        (actual.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt actual.current.visit.current) ∧
      HEq oldActual.tick.generated.wholeLedgerWriteBack
        (oldActual.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt oldActual.current.visit.current) ∧
      actual.tick.nextCurrent = (Identity.Runtime.facade seed feasible).process.stateAt
        ((Identity.Runtime.facade seed feasible).process.successor actual.state) ∧
      oldActual.tick.nextCurrent = (Native.Runtime.facade old).process.stateAt
        ((Native.Runtime.facade old).process.successor oldActual.state) := by
  have identities := (Identity.Runtime.facade seed feasible).readoutAt_factorizes
    (Identity.Runtime.activated seed feasible (seed.history.length + 1)) .identities
  have native := (Identity.Runtime.facade seed feasible).readoutAt_factorizes
    (Identity.Runtime.activated seed feasible (seed.history.length + 1)) (.previous .responsibilities)
  have old := (Native.Runtime.facade (Identity.original seed)).readoutAt_factorizes
    (Native.Runtime.activated (Identity.original seed) (seed.history.length + 1)) .responsibilities
  exact ⟨Identity.every_original_debt_has_its_actual_native_counterpart seed feasible,
    Identity.independent_replay_accepts_selection _ _ (Identity.selection seed feasible),
    identities.2.2.2.1, native.2.2.2.1, old.2.2.2.1, identities.2.2.1, old.2.2.1,
    identities.2.2.2.2, old.2.2.2.2⟩

theorem named_strict_material_gain_preserves_the_original_issue_and_both_actual_ledgers :
    (source.actualExecution 1).after.stock true () = 2 ∧
      (oldSource.actualExecution 1).after.stock true () = 1 ∧
      Financial.outstanding source.input (Native.generate source 1).finance.current = 2 ∧
      HEq (publicNativeIdentityFacade.readoutAt (activated 2) .identities)
        ((activated 2).tick.generated.projectionOutcome (.component .identities)) ∧
      HEq (publicNativeIdentityFacade.readoutAt (activated 2) (.previous .responsibilities))
        ((activated 2).tick.generated.projectionOutcome (.inherited (.component ()))) ∧
      HEq (originalNativeIdentityFacade.readoutAt (oldActivated 2) .responsibilities)
        ((oldActivated 2).tick.generated.projectionOutcome (.component ())) ∧
      HEq (activated 2).tick.generated.wholeLedgerWriteBack
        ((activated 2).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt (activated 2).current.visit.current) ∧
      HEq (oldActivated 2).tick.generated.wholeLedgerWriteBack
        ((oldActivated 2).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt (oldActivated 2).current.visit.current) ∧
      (activated 2).tick.nextCurrent = publicNativeIdentityFacade.process.stateAt
        (publicNativeIdentityFacade.process.successor (activated 2).state) ∧
      (oldActivated 2).tick.nextCurrent = originalNativeIdentityFacade.process.stateAt
        (originalNativeIdentityFacade.process.successor (oldActivated 2).state) := by
  have facts := Identity.Regression.actual_improvement_keeps_the_original_native_debt
  have identities := publicNativeIdentityFacade.readoutAt_factorizes (activated 2) .identities
  have native := publicNativeIdentityFacade.readoutAt_factorizes (activated 2) (.previous .responsibilities)
  have old := originalNativeIdentityFacade.readoutAt_factorizes (oldActivated 2) .responsibilities
  exact ⟨facts.2.1, facts.2.2.1, facts.2.2.2.2.1, identities.2.2.2.1, native.2.2.2.1,
    old.2.2.2.1, identities.2.2.1, old.2.2.1, identities.2.2.2.2, old.2.2.2.2⟩

end SaturationMonoid.Tracks.LivingLawPublicNativeIdentityInstance
