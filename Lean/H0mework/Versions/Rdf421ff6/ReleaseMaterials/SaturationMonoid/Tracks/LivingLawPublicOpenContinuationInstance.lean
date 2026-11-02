import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Open.Regression

set_option autoImplicit false

namespace SaturationMonoid.Tracks.LivingLawPublicOpenContinuationInstance

open ProcessGame.Society.PublicFunction
open ProcessGame.Society.PublicFunction.Distributed.Reaction
open ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program
open ProcessGame.Society.Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

abbrev seed := Open.Regression.seed
abbrev feasible := Open.Regression.original_is_feasible
abbrev stable := Open.Regression.source_laws_are_stable
abbrev productionSource := Open.replacement seed feasible
abbrev originalSource := Open.original seed
abbrev publicOpenContinuationFacade := Open.Runtime.facade seed feasible stable
abbrev originalOpenContinuationFacade := Native.Runtime.facade originalSource
abbrev activated := Open.Runtime.activated seed feasible stable


abbrev replayWords := Open.Regression.futureWords
abbrev replayLegal := Open.Regression.original_future_is_legal
abbrev replaySource := Open.Replay.replacement seed feasible replayWords
abbrev replayOriginal := Open.Replay.original seed replayWords
abbrev publicReplayContinuationFacade := Open.ReplayRuntime.facade seed feasible stable replayWords replayLegal
abbrev originalReplayContinuationFacade := Native.Runtime.facade replayOriginal
abbrev replayActivated := Open.ReplayRuntime.activated seed feasible stable replayWords replayLegal

theorem original_native_accounts_and_unbounded_legal_histories_are_consumed_by_the_same_root
    {Party Good Port Technology Instrument : Type}
    [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
    [DecidableEq Technology] [DecidableEq Instrument]
    (seed : Machine Party Good Port Technology Instrument) (feasible : seed.code.feasible seed.reference)
    (stable : Open.Stable seed.code.law) :
    let new := Open.replacement seed feasible
    let old := Open.original seed
    let actual := Open.Runtime.activated seed feasible stable (seed.history.length + 1)
    let oldActual := Native.Runtime.activated old (seed.history.length + 1)
    (∀ metric, new.actualScore metric ≤ old.actualScore metric) ∧
      (∀ words, Open.LegalHistory seed.code.law (old.actualExecution seed.history.length).after words →
        Open.LegalHistory seed.code.law (new.actualExecution seed.history.length).after words ∧
          words.foldl seed.code.law.next (new.actualExecution seed.history.length).after =
            (words.foldl seed.code.law.next (old.actualExecution seed.history.length).after).addReserve
              (Open.reserve seed.code (Open.selection seed feasible).policy.policy seed.reference seed.history seed.opponent)) ∧
      Open.verify seed.code seed.reference (Open.selection seed feasible).policy.policy = true ∧
      (∀ other ∈ seed.code.policies, seed.code.feasible other →
        ¬ Open.StrictAgainstEveryOpponent seed.code (Open.selection seed feasible).policy.policy other) ∧
      HEq ((Open.Runtime.facade seed feasible stable).readoutAt actual .continuation)
        (actual.tick.generated.projectionOutcome (.component .continuation)) ∧
      HEq ((Open.Runtime.facade seed feasible stable).readoutAt actual (.previous .responsibilities))
        (actual.tick.generated.projectionOutcome (.inherited (.component ()))) ∧
      HEq ((Native.Runtime.facade old).readoutAt oldActual .responsibilities)
        (oldActual.tick.generated.projectionOutcome (.component ())) ∧
      HEq actual.tick.generated.wholeLedgerWriteBack
        (actual.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt actual.current.visit.current) ∧
      HEq oldActual.tick.generated.wholeLedgerWriteBack
        (oldActual.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt oldActual.current.visit.current) ∧
      actual.tick.nextCurrent = (Open.Runtime.facade seed feasible stable).process.stateAt
        ((Open.Runtime.facade seed feasible stable).process.successor actual.state) ∧
      oldActual.tick.nextCurrent = (Native.Runtime.facade old).process.stateAt
        ((Native.Runtime.facade old).process.successor oldActual.state) := by
  have continuation := (Open.Runtime.facade seed feasible stable).readoutAt_factorizes
    (Open.Runtime.activated seed feasible stable (seed.history.length + 1)) .continuation
  have native := (Open.Runtime.facade seed feasible stable).readoutAt_factorizes
    (Open.Runtime.activated seed feasible stable (seed.history.length + 1)) (.previous .responsibilities)
  have old := (Native.Runtime.facade (Open.original seed)).readoutAt_factorizes
    (Native.Runtime.activated (Open.original seed) (seed.history.length + 1)) .responsibilities
  exact ⟨Open.raw_responsibility_vector_is_not_worse seed feasible,
    Open.all_old_legal_histories_remain_actually_open seed feasible stable,
    Open.independent_replay_accepts_selection _ _ (Open.selection seed feasible),
    Open.selected_is_nondominated_against_every_same_opponent _ _ (Open.selection seed feasible),
    continuation.2.2.2.1, native.2.2.2.1, old.2.2.2.1, continuation.2.2.1, old.2.2.1,
    continuation.2.2.2.2, old.2.2.2.2⟩

theorem named_strict_material_reserve_and_open_successor_share_the_actual_root :
    (productionSource.actualExecution 0).after.stock true () = 2 ∧
      (originalSource.actualExecution 0).after.stock true () = 1 ∧
      HEq (publicOpenContinuationFacade.readoutAt (activated 1) .continuation)
        ((activated 1).tick.generated.projectionOutcome (.component .continuation)) ∧
      HEq (publicOpenContinuationFacade.readoutAt (activated 1) (.previous .responsibilities))
        ((activated 1).tick.generated.projectionOutcome (.inherited (.component ()))) ∧
      HEq (activated 1).tick.generated.wholeLedgerWriteBack
        ((activated 1).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt (activated 1).current.visit.current) ∧
      (activated 1).tick.nextCurrent = publicOpenContinuationFacade.process.stateAt
        (publicOpenContinuationFacade.process.successor (activated 1).state) := by
  have facts := Open.Regression.actual_strict_reserve_and_independent_replay
  have continuation := publicOpenContinuationFacade.readoutAt_factorizes (activated 1) .continuation
  have native := publicOpenContinuationFacade.readoutAt_factorizes (activated 1) (.previous .responsibilities)
  exact ⟨facts.2.1, facts.2.2.1, continuation.2.2.2.1, native.2.2.2.1,
    continuation.2.2.1, continuation.2.2.2.2⟩

theorem named_original_root_keeps_its_own_ledger_and_successor :
    HEq (originalOpenContinuationFacade.readoutAt (Native.Runtime.activated originalSource 1) .responsibilities)
      ((Native.Runtime.activated originalSource 1).tick.generated.projectionOutcome (.component ())) ∧
      HEq (Native.Runtime.activated originalSource 1).tick.generated.wholeLedgerWriteBack
        ((Native.Runtime.activated originalSource 1).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          (Native.Runtime.activated originalSource 1).current.visit.current) ∧
      (Native.Runtime.activated originalSource 1).tick.nextCurrent = originalOpenContinuationFacade.process.stateAt
        (originalOpenContinuationFacade.process.successor (Native.Runtime.activated originalSource 1).state) := by
  have factor := originalOpenContinuationFacade.readoutAt_factorizes (Native.Runtime.activated originalSource 1) .responsibilities
  exact ⟨factor.2.2.2.1, factor.2.2.1, factor.2.2.2.2⟩

theorem every_submitted_legal_cut_is_consumed_by_its_actual_roots
    {Party Good Port Technology Instrument : Type}
    [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
    [DecidableEq Technology] [DecidableEq Instrument]
    (seed : Machine Party Good Port Technology Instrument) (feasible : seed.code.feasible seed.reference)
    (stable : Open.Stable seed.code.law) (words : List (RawEvent Party Good Port Technology Instrument))
    (accepted : Open.LegalHistory seed.code.law (Open.terminal seed.code seed.reference seed.history seed.opponent) words)
    (count : Nat) (bounded : count ≤ words.length) :
    let source := Open.Replay.replacement seed feasible words
    let old := Open.Replay.original seed words
    let actual := Open.ReplayRuntime.activated seed feasible stable words accepted (seed.history.length + 1 + count)
    let oldActual := Native.Runtime.activated old (seed.history.length + 1 + count)
    source.currentAt (seed.history.length + 2 + count) =
      (old.currentAt (seed.history.length + 2 + count)).addReserve
        (Open.reserve seed.code (Open.selection seed feasible).policy.policy seed.reference seed.history seed.opponent) ∧
      HEq ((Open.ReplayRuntime.facade seed feasible stable words accepted).readoutAt actual .replay)
        (actual.tick.generated.projectionOutcome (.component ())) ∧
      HEq ((Open.ReplayRuntime.facade seed feasible stable words accepted).readoutAt actual (.previous (.previous .responsibilities)))
        (actual.tick.generated.projectionOutcome (.inherited (.inherited (.component ())))) ∧
      HEq actual.tick.generated.wholeLedgerWriteBack
        (actual.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt actual.current.visit.current) ∧
      HEq oldActual.tick.generated.wholeLedgerWriteBack
        (oldActual.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt oldActual.current.visit.current) ∧
      actual.tick.nextCurrent = (Open.ReplayRuntime.facade seed feasible stable words accepted).process.stateAt
        ((Open.ReplayRuntime.facade seed feasible stable words accepted).process.successor actual.state) ∧
      oldActual.tick.nextCurrent = (Native.Runtime.facade old).process.stateAt
        ((Native.Runtime.facade old).process.successor oldActual.state) := by
  have replay := (Open.ReplayRuntime.facade seed feasible stable words accepted).readoutAt_factorizes
    (Open.ReplayRuntime.activated seed feasible stable words accepted (seed.history.length + 1 + count)) .replay
  have native := (Open.ReplayRuntime.facade seed feasible stable words accepted).readoutAt_factorizes
    (Open.ReplayRuntime.activated seed feasible stable words accepted (seed.history.length + 1 + count)) (.previous (.previous .responsibilities))
  have old := (Native.Runtime.facade (Open.Replay.original seed words)).readoutAt_factorizes
    (Native.Runtime.activated (Open.Replay.original seed words) (seed.history.length + 1 + count)) .responsibilities
  exact ⟨Open.Replay.every_actual_cut_keeps_the_full_original_carrier seed feasible stable words accepted count bounded,
    replay.2.2.2.1, native.2.2.2.1, replay.2.2.1, old.2.2.1, replay.2.2.2.2, old.2.2.2.2⟩

theorem named_later_payment_and_issue_enter_the_actual_native_ledger_and_next :
    (replaySource.actualExecution 1).submitted = [Distributed.Reaction.Regression.need] ∧
      (replaySource.actualExecution 2).submitted = [Open.Regression.laterIssue] ∧
      (replaySource.currentAt 4).stock true () = 1 ∧ (replayOriginal.currentAt 4).stock true () = 0 ∧
      Financial.outstanding replaySource.input (Native.generate replaySource 2).finance.current = 1 ∧
      HEq (publicReplayContinuationFacade.readoutAt (replayActivated 3) .replay)
        ((replayActivated 3).tick.generated.projectionOutcome (.component ())) ∧
      HEq (replayActivated 3).tick.generated.wholeLedgerWriteBack
        ((replayActivated 3).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt (replayActivated 3).current.visit.current) ∧
      (replayActivated 3).tick.nextCurrent = publicReplayContinuationFacade.process.stateAt
        (publicReplayContinuationFacade.process.successor (replayActivated 3).state) := by
  have facts := Open.Regression.later_requests_actually_run_with_original_native_archives_and_new_issue
  have factor := publicReplayContinuationFacade.readoutAt_factorizes (replayActivated 3) .replay
  exact ⟨facts.1, facts.2.1, facts.2.2.1, facts.2.2.2.1, facts.2.2.2.2.2.2,
    factor.2.2.2.1, factor.2.2.1, factor.2.2.2.2⟩

end SaturationMonoid.Tracks.LivingLawPublicOpenContinuationInstance
