import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Selection
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Trace.OrderRegression
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Runtime
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.ResidualRegression
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.ExecutionRegression
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.FutureRegression
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Cut.Regression
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Regression
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Settlement
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Settlement.Regression

set_option autoImplicit false

namespace SaturationMonoid.Tracks.LivingLawPublicFeedbackInstance

open ProcessGame.Society.PublicFunction.Distributed.Reaction
open ProcessGame.Society.Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

abbrev source := Feedback.Regression.source
abbrev input := Feedback.Regression.input
abbrev publicFeedbackFacade := Feedback.Runtime.facade source input rfl rfl
abbrev activated := Feedback.Runtime.activated source input rfl rfl

abbrev selectedSeed := Settlement.Regression.seed
abbrev selectedFeasible := Settlement.Regression.original_is_feasible
abbrev selectedSource := Feedback.selectedSource selectedSeed selectedFeasible 4
abbrev selectedInput : Feedback.Input selectedSource.code := ⟨selectedSeed.opponent, 4⟩
abbrev publicSelectedFeedbackFacade := Feedback.Runtime.facade selectedSource selectedInput rfl rfl
abbrev selectedActivated := Feedback.Runtime.activated selectedSource selectedInput rfl rfl

theorem every_actual_feedback_cut_consumes_its_memory_native_accounts_and_own_next (index : Nat) :
    let actual := activated (source.history.length + 2 + index)
    (source.feedbackState input index).current =
        (source.actualExecution (source.history.length + 1 + index)).before ∧
      (source.feedbackState input index).history =
        source.history ++ [source.responseFrame.word] ++ source.feedbackWords index ∧
      HEq (publicFeedbackFacade.readoutAt actual .feedback)
        (actual.tick.generated.projectionOutcome (.component ())) ∧
      HEq (publicFeedbackFacade.readoutAt actual (.previous .responsibilities))
        (actual.tick.generated.projectionOutcome (.inherited (.component ()))) ∧
      HEq actual.tick.generated.wholeLedgerWriteBack
        (actual.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt actual.current.visit.current) ∧
      actual.tick.nextCurrent = publicFeedbackFacade.process.stateAt
        (publicFeedbackFacade.process.successor actual.state) := by
  have feedback := publicFeedbackFacade.readoutAt_factorizes
    (activated (source.history.length + 2 + index)) .feedback
  have native := publicFeedbackFacade.readoutAt_factorizes
    (activated (source.history.length + 2 + index)) (.previous .responsibilities)
  exact ⟨source.feedback_body_reads_the_actual_local_current input rfl rfl index,
    source.feedback_keeps_the_complete_actual_history input rfl rfl index,
    feedback.2.2.2.1, native.2.2.2.1, feedback.2.2.1, feedback.2.2.2.2⟩

theorem actual_local_debt_payment_is_consumed_with_the_original_native_slot :
    Financial.outstanding source.input (Native.generate source 1).finance.current = 2 ∧
      Financial.outstanding source.input (Native.generate source 4).finance.current = 0 ∧
      (source.actualExecution 4).after.stock false () = 2 ∧
      (Native.generate source 4).finance.current.slots.length = 1 ∧
      HEq (publicFeedbackFacade.readoutAt (activated 5) .feedback)
        ((activated 5).tick.generated.projectionOutcome (.component ())) ∧
      HEq (activated 5).tick.generated.wholeLedgerWriteBack
        ((activated 5).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt (activated 5).current.visit.current) ∧
      (activated 5).tick.nextCurrent = publicFeedbackFacade.process.stateAt
        (publicFeedbackFacade.process.successor (activated 5).state) := by
  rcases Feedback.Regression.local_debt_reading_drives_actual_payment_and_preserves_its_native_archive with
    ⟨unpaid, _stock, paidStock, paid, slots, _archive, _refused⟩
  have rooted := publicFeedbackFacade.readoutAt_factorizes (activated 5) .feedback
  exact ⟨unpaid, paid, paidStock, slots, rooted.2.2.2.1, rooted.2.2.1, rooted.2.2.2.2⟩

theorem selected_initial_plan_and_actual_feedback_are_consumed_by_the_selected_root :
    (selectedSource.actualExecution selectedSeed.history.length).submitted =
      ((Settlement.replacement selectedSeed selectedFeasible).actualExecution selectedSeed.history.length).submitted ∧
      HEq (publicSelectedFeedbackFacade.readoutAt (selectedActivated 3) .feedback)
        ((selectedActivated 3).tick.generated.projectionOutcome (.component ())) ∧
      HEq (selectedActivated 3).tick.generated.wholeLedgerWriteBack
        ((selectedActivated 3).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          (selectedActivated 3).current.visit.current) ∧
      (selectedActivated 3).tick.nextCurrent = publicSelectedFeedbackFacade.process.stateAt
        (publicSelectedFeedbackFacade.process.successor (selectedActivated 3).state) := by
  have rooted := publicSelectedFeedbackFacade.readoutAt_factorizes (selectedActivated 3) .feedback
  exact ⟨Feedback.selected_response_is_preserved selectedSeed selectedFeasible 4,
    rooted.2.2.2.1, rooted.2.2.1, rooted.2.2.2.2⟩


def cutDispositionFromRuntime (index : Nat) : Feedback.Runtime.Disposition source input index :=
  match publicFeedbackFacade.readoutAt (activated (source.history.length + 2 + index)) .feedback with
  | .inl active => active.2 index (by
      change (ProgrammeHistory.visitAt source.input
        (activated (source.history.length + 2 + index)).state).current = _
      rw [Feedback.Runtime.activated_state_is_the_generated_ordinal])
  | .inr impossible => nomatch impossible

theorem every_cut_generates_its_joint_opponent_domain_and_consumes_the_actual_baseline (index : Nat) :
    let payload := (cutDispositionFromRuntime index).residual
    let actual := activated (source.history.length + 2 + index)
    Feedback.Residual.FutureCoverage source input index ∧
      payload.table ∈ Feedback.Residual.tables source.code (source.feedbackState input index)
        (Feedback.Residual.schedules source input index) ∧
      (∀ n ≤ (source.feedbackState input index).remaining,
        (Feedback.Residual.run source.code (Feedback.Residual.scheduleAt source index [])
          ⟨Feedback.Residual.respond source.code (source.feedbackState input index)
            (Feedback.Residual.schedules source input index) payload.table, input.budget⟩
          (source.feedbackState input index) n).current =
            (source.actualExecution (source.history.length + 1 + (index + n))).before) ∧
      HEq (publicFeedbackFacade.readoutAt actual .feedback)
        (actual.tick.generated.projectionOutcome (.component ())) ∧
      HEq (publicFeedbackFacade.readoutAt actual (.previous .responsibilities))
        (actual.tick.generated.projectionOutcome (.inherited (.component ()))) ∧
      HEq actual.tick.generated.wholeLedgerWriteBack
        (actual.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt actual.current.visit.current) ∧
      actual.tick.nextCurrent = publicFeedbackFacade.process.stateAt
        (publicFeedbackFacade.process.successor actual.state) := by
  let payload := (cutDispositionFromRuntime index).residual
  have feedback := publicFeedbackFacade.readoutAt_factorizes (activated (source.history.length + 2 + index)) .feedback
  have native := publicFeedbackFacade.readoutAt_factorizes (activated (source.history.length + 2 + index)) (.previous .responsibilities)
  refine ⟨payload.future_coverage, payload.generated, ?_, feedback.2.2.2.1,
    native.2.2.2.1, feedback.2.2.1, feedback.2.2.2.2⟩
  intro n bounded
  exact (congrArg Feedback.State.current (payload.baseline_actual n bounded)).trans
    (source.feedback_body_reads_the_actual_local_current input rfl rfl (index + n))


namespace Scheduled

abbrev original := Feedback.Execution.Regression.source
abbrev input := Feedback.Execution.Regression.input
abbrev term := Feedback.Execution.Regression.term
abbrev candidate := Feedback.Execution.Regression.candidate
abbrev originalFacade := Feedback.Runtime.facade original input rfl rfl
abbrev originalActivated := Feedback.Runtime.activated original input rfl rfl
abbrev publicScheduledFeedbackFacade := Feedback.Runtime.facade candidate input rfl rfl
abbrev activated := Feedback.Runtime.activated candidate input rfl rfl

def originalCutFromRuntime : Feedback.Runtime.Disposition original input 2 :=
  match originalFacade.readoutAt (originalActivated 5) .feedback with
  | .inl actual => actual.2 2 rfl
  | .inr impossible => nomatch impossible

def executionFromRuntime : Feedback.Execution.Disposition original input 2 term :=
  originalCutFromRuntime.executions ⟨term, Feedback.Execution.Regression.the_schedule_is_generated_from_the_actual_cut⟩

theorem the_scheduled_source_and_its_native_payment_are_consumed_with_their_own_next :
    Native.Coupling.Match original.code original.input candidate.input
      (Financial.accountAt original.input 5) (Financial.accountAt candidate.input 5) ∧
      Native.Coupling.verify original.code original.input candidate.input
        (Financial.accountAt original.input 5) (Financial.accountAt candidate.input 5) = true ∧
      (∀ n, ((Feedback.Execution.target original 2 term).actualExecution (original.history.length + 1 + (2 + n))).submitted =
        Feedback.word original.code (Feedback.Residual.scheduleAt original 2 term n) input
          (Feedback.Residual.run original.code (Feedback.Residual.scheduleAt original 2 term) input
            (Feedback.Residual.seed original input 2) n)) ∧
      (∀ n ≤ (original.feedbackState input 2).remaining,
        candidate.feedbackState input (2 + n) =
          Feedback.Residual.run original.code (Feedback.Residual.scheduleAt original 2 term)
            ⟨Feedback.Residual.respond original.code (Feedback.Residual.seed original input 2)
              (Feedback.Residual.schedules original input 2) originalCutFromRuntime.residual.table, input.budget⟩
            (Feedback.Residual.seed original input 2) n) ∧
      Financial.outstanding candidate.input (executionFromRuntime.native 0).finance.current = 2 ∧
      Financial.outstanding candidate.input (executionFromRuntime.native 1).finance.current = 0 ∧
      HEq (originalFacade.readoutAt (originalActivated 5) .feedback)
        ((originalActivated 5).tick.generated.projectionOutcome (.component ())) ∧
      HEq (originalActivated 5).tick.generated.wholeLedgerWriteBack
        ((originalActivated 5).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          (originalActivated 5).current.visit.current) ∧
      (originalActivated 5).tick.nextCurrent = originalFacade.process.stateAt
        (originalFacade.process.successor (originalActivated 5).state) ∧
      HEq (publicScheduledFeedbackFacade.readoutAt (activated 6) (.previous .responsibilities))
        ((activated 6).tick.generated.projectionOutcome (.inherited (.component ()))) ∧
      HEq (activated 6).tick.generated.wholeLedgerWriteBack
        ((activated 6).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt (activated 6).current.visit.current) ∧
      (activated 6).tick.nextCurrent = publicScheduledFeedbackFacade.process.stateAt
        (publicScheduledFeedbackFacade.process.successor (activated 6).state) := by
  have sourceFace := originalFacade.readoutAt_factorizes (originalActivated 5) .feedback
  have native := publicScheduledFeedbackFacade.readoutAt_factorizes (activated 6) (.previous .responsibilities)
  have facts := Feedback.Execution.Regression.the_candidate_really_pauses_then_pays_its_own_original_debt
  have same := executionFromRuntime.native_exact
  let matched := executionFromRuntime.finance_prefix 5 (by decide +kernel)
  refine ⟨matched, (Native.Coupling.verify_iff _ _ _ _ _).mpr matched, executionFromRuntime.actual_words,
    originalCutFromRuntime.joint_executions ⟨term, Feedback.Execution.Regression.the_schedule_is_generated_from_the_actual_cut⟩,
    ?_, ?_, sourceFace.2.2.2.1, sourceFace.2.2.1, sourceFace.2.2.2.2,
    native.2.2.2.1, native.2.2.1, native.2.2.2.2⟩
  · rw [congrFun same 0]
    exact facts.2.2.1
  · rw [congrFun same 1]
    exact facts.2.2.2.1

end Scheduled


theorem every_cut_generates_native_sources_for_all_future_opponents (index : Nat) :
    let payload := cutDispositionFromRuntime index
    (∀ opponent : Opponent source.code,
      (payload.future opponent).table ∈ Feedback.Residual.tables source.code
        (Feedback.Residual.seed source input index) (Feedback.Residual.schedules source input index) ∧
      ∀ term : {term : List (Option source.code.Policy) // term ∈ Feedback.Residual.scheduleTerms source input index},
        (Feedback.Future.target source input index opponent term.val).feedbackState
          (Feedback.Future.takeover source input index opponent) index = source.feedbackState input index ∧
        ∀ n ≤ (Feedback.Residual.seed source input index).remaining,
          (Feedback.Future.target source input index opponent term.val).feedbackState
            (Feedback.Future.takeover source input index opponent) (index + n) =
          Feedback.Residual.run source.code (Feedback.Residual.scheduleAt source index term.val)
            ⟨Feedback.Residual.respond source.code (Feedback.Residual.seed source input index)
              (Feedback.Residual.schedules source input index) (payload.future opponent).table, input.budget⟩
            (Feedback.Residual.seed source input index) n) ∧
      HEq (publicFeedbackFacade.readoutAt (activated (source.history.length + 2 + index)) .feedback)
        ((activated (source.history.length + 2 + index)).tick.generated.projectionOutcome (.component ())) ∧
      (activated (source.history.length + 2 + index)).tick.nextCurrent = publicFeedbackFacade.process.stateAt
        (publicFeedbackFacade.process.successor (activated (source.history.length + 2 + index)).state) := by
  have rooted := publicFeedbackFacade.readoutAt_factorizes (activated (source.history.length + 2 + index)) .feedback
  refine ⟨?_, rooted.2.2.2.1, rooted.2.2.2.2⟩
  intro opponent
  refine ⟨((cutDispositionFromRuntime index).future opponent).generated, ?_⟩
  intro term
  exact ⟨(((cutDispositionFromRuntime index).future opponent).executions term).prior_state,
    ((cutDispositionFromRuntime index).future opponent).joint_executions term⟩

theorem every_future_joint_table_preserves_all_native_financial_images (index : Nat) :
    let payload := cutDispositionFromRuntime index
    (∀ (opponent : Opponent source.code)
      (term : {term : List (Option source.code.Policy) // term ∈ Feedback.Residual.scheduleTerms source input index})
      (ordinal : Nat), ordinal ≤ source.history.length + 2 + index + (Feedback.Residual.seed source input index).remaining →
      let candidate := Feedback.Future.target source input index opponent term.val
      let finite := Feedback.Future.target source input index
        (Feedback.Residual.respond source.code (Feedback.Residual.seed source input index)
          (Feedback.Residual.schedules source input index) (payload.future opponent).table) term.val
      Native.Coupling.Match source.code candidate.input finite.input
          (Financial.accountAt candidate.input ordinal) (Financial.accountAt finite.input ordinal) ∧
        Native.Coupling.verify source.code candidate.input finite.input
          (Financial.accountAt candidate.input ordinal) (Financial.accountAt finite.input ordinal) = true ∧
        ((payload.future opponent).executions term).native =
          (fun n => Native.generate candidate (source.history.length + 1 + (index + n))) ∧
        ((payload.future opponent).table_executions term).native =
          (fun n => Native.generate finite (source.history.length + 1 + (index + n)))) ∧
      HEq (activated (source.history.length + 2 + index)).tick.generated.wholeLedgerWriteBack
        ((activated (source.history.length + 2 + index)).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          (activated (source.history.length + 2 + index)).current.visit.current) ∧
      (activated (source.history.length + 2 + index)).tick.nextCurrent = publicFeedbackFacade.process.stateAt
        (publicFeedbackFacade.process.successor (activated (source.history.length + 2 + index)).state) := by
  have rooted := publicFeedbackFacade.readoutAt_factorizes (activated (source.history.length + 2 + index)) .feedback
  refine ⟨?_, rooted.2.2.1, rooted.2.2.2.2⟩
  intro opponent term ordinal bounded
  let matched := ((cutDispositionFromRuntime index).future opponent).financial_images term ordinal bounded
  exact ⟨matched, (Native.Coupling.verify_iff _ _ _ _ _).mpr matched,
    (((cutDispositionFromRuntime index).future opponent).executions term).native_exact,
    (((cutDispositionFromRuntime index).future opponent).table_executions term).native_exact⟩

namespace FutureTakeover

abbrev original := Feedback.Future.Regression.source
abbrev input := Feedback.Future.Regression.input
abbrev opponent := Feedback.Future.Regression.opponent
abbrev term := Feedback.Future.Regression.term
abbrev candidate := Feedback.Future.Regression.candidate
abbrev candidateInput := Feedback.Future.Regression.candidateInput
abbrev publicFutureFeedbackFacade := Feedback.Runtime.facade candidate candidateInput rfl rfl
abbrev activated := Feedback.Runtime.activated candidate candidateInput rfl rfl

def familyFromRuntime : Feedback.Future.Disposition original input 2 opponent :=
  Scheduled.originalCutFromRuntime.future opponent

def executionFromRuntime : Feedback.Future.Execution original input 2 opponent term :=
  familyFromRuntime.executions ⟨term, Feedback.Future.Regression.the_baseline_term_is_generated⟩

theorem the_future_source_pays_its_original_debt_and_consumes_its_own_next :
    Native.Coupling.Match original.code original.input candidate.input
      (Financial.accountAt original.input 5) (Financial.accountAt candidate.input 5) ∧
      Native.Coupling.verify original.code original.input candidate.input
        (Financial.accountAt original.input 5) (Financial.accountAt candidate.input 5) = true ∧
      Financial.outstanding candidate.input (executionFromRuntime.native 0).finance.current = 2 ∧
      Financial.outstanding candidate.input (executionFromRuntime.native 1).finance.current = 0 ∧
      HEq (Scheduled.originalFacade.readoutAt (Scheduled.originalActivated 5) .feedback)
        ((Scheduled.originalActivated 5).tick.generated.projectionOutcome (.component ())) ∧
      HEq (Scheduled.originalActivated 5).tick.generated.wholeLedgerWriteBack
        ((Scheduled.originalActivated 5).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          (Scheduled.originalActivated 5).current.visit.current) ∧
      (Scheduled.originalActivated 5).tick.nextCurrent = Scheduled.originalFacade.process.stateAt
        (Scheduled.originalFacade.process.successor (Scheduled.originalActivated 5).state) ∧
      HEq (publicFutureFeedbackFacade.readoutAt (activated 6) (.previous .responsibilities))
        ((activated 6).tick.generated.projectionOutcome (.inherited (.component ()))) ∧
      HEq (activated 6).tick.generated.wholeLedgerWriteBack
        ((activated 6).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt (activated 6).current.visit.current) ∧
      (activated 6).tick.nextCurrent = publicFutureFeedbackFacade.process.stateAt
        (publicFutureFeedbackFacade.process.successor (activated 6).state) := by
  have old := Scheduled.originalFacade.readoutAt_factorizes (Scheduled.originalActivated 5) .feedback
  have current := publicFutureFeedbackFacade.readoutAt_factorizes (activated 6) (.previous .responsibilities)
  have facts := Feedback.Future.Regression.the_future_opponent_cannot_rewrite_its_actual_past_or_reset_its_budget
  have same := executionFromRuntime.native_exact
  let matched := executionFromRuntime.finance_prefix 5 (by decide +kernel)
  refine ⟨matched, (Native.Coupling.verify_iff _ _ _ _ _).mpr matched, ?_, ?_,
    old.2.2.2.1, old.2.2.1, old.2.2.2.2, current.2.2.2.1, current.2.2.1, current.2.2.2.2⟩
  · rw [congrFun same 0]
    exact facts.2.2.2.2.2.1
  · rw [congrFun same 1]
    exact facts.2.2.2.2.2.2.1

end FutureTakeover


theorem every_actual_cut_consumes_its_generated_settlement_and_independent_verifier (index : Nat) :
    let payload := (cutDispositionFromRuntime index).settlement
    payload.outcome = Feedback.Cut.compile source input index (Feedback.Cut.baseline source input index) ∧
      Feedback.Cut.AnswerSound source input index payload.outcome ∧
      HEq (publicFeedbackFacade.readoutAt (activated (source.history.length + 2 + index)) .feedback)
        ((activated (source.history.length + 2 + index)).tick.generated.projectionOutcome (.component ())) ∧
      HEq (activated (source.history.length + 2 + index)).tick.generated.wholeLedgerWriteBack
        ((activated (source.history.length + 2 + index)).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          (activated (source.history.length + 2 + index)).current.visit.current) ∧
      (activated (source.history.length + 2 + index)).tick.nextCurrent = publicFeedbackFacade.process.stateAt
        (publicFeedbackFacade.process.successor (activated (source.history.length + 2 + index)).state) := by
  have rooted := publicFeedbackFacade.readoutAt_factorizes (activated (source.history.length + 2 + index)) .feedback
  exact ⟨(cutDispositionFromRuntime index).settlement.generated,
    Feedback.Cut.answer_sound source input index rfl rfl _, rooted.2.2.2.1, rooted.2.2.1, rooted.2.2.2.2⟩

namespace CutSelection

abbrev original := Feedback.Cut.Regression.source
abbrev input := Feedback.Cut.Regression.input
abbrev originalFacade := Feedback.Runtime.facade original input rfl rfl
abbrev originalActivated := Feedback.Runtime.activated original input rfl rfl

def originalCutFromRuntime : Feedback.Runtime.Disposition original input 0 :=
  match originalFacade.readoutAt (originalActivated 3) .feedback with
  | .inl actual => actual.2 0 rfl
  | .inr impossible => nomatch impossible

def choiceFromRuntime : Feedback.Cut.Selection original input 0 (Feedback.Cut.baseline original input 0) :=
  Feedback.Cut.selectionFrom original input 0 originalCutFromRuntime.settlement.outcome Feedback.Cut.Regression.original_is_feasible

def executionFromRuntime : Feedback.Future.Execution original input 0 input.opponent choiceFromRuntime.policy.term.val :=
  Feedback.Cut.selectedExecution original input 0 originalCutFromRuntime.settlement Feedback.Cut.Regression.original_is_feasible input.opponent

abbrev candidate := Feedback.Cut.machine original input 0 input.opponent choiceFromRuntime.policy.term
abbrev candidateInput := Feedback.Cut.replacementInput original input 0
abbrev publicCutSettlementFacade := Feedback.Runtime.facade candidate candidateInput rfl rfl
abbrev activated := Feedback.Runtime.activated candidate candidateInput rfl rfl

theorem the_runtime_choice_is_the_generated_cut_choice : choiceFromRuntime = Feedback.Cut.Regression.chosen := rfl

theorem the_actual_cut_selects_a_strict_material_dividend_with_its_own_native_accounts :
    originalCutFromRuntime.settlement.outcome = Feedback.Cut.compile original input 0 (Feedback.Cut.baseline original input 0) ∧
      Feedback.Cut.StrictAgainstEveryOpponent original input 0 (Feedback.Cut.baseline original input 0) choiceFromRuntime.policy.term ∧
      Feedback.Cut.verify original input 0 (Feedback.Cut.baseline original input 0) choiceFromRuntime.policy.term = true ∧
      (candidate.actualExecution 2).after.stock true () = 2 ∧
      Financial.outstanding candidate.input (executionFromRuntime.native 0).finance.current = 0 ∧
      Native.Coupling.Match original.code original.input candidate.input
        (Financial.accountAt original.input 3) (Financial.accountAt candidate.input 3) ∧
      HEq (originalFacade.readoutAt (originalActivated 3) .feedback)
        ((originalActivated 3).tick.generated.projectionOutcome (.component ())) ∧
      HEq (originalActivated 3).tick.generated.wholeLedgerWriteBack
        ((originalActivated 3).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          (originalActivated 3).current.visit.current) ∧
      (originalActivated 3).tick.nextCurrent = originalFacade.process.stateAt
        (originalFacade.process.successor (originalActivated 3).state) ∧
      HEq (publicCutSettlementFacade.readoutAt (activated 3) (.previous .responsibilities))
        ((activated 3).tick.generated.projectionOutcome (.inherited (.component ()))) ∧
      HEq (activated 3).tick.generated.wholeLedgerWriteBack
        ((activated 3).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt (activated 3).current.visit.current) ∧
      (activated 3).tick.nextCurrent = publicCutSettlementFacade.process.stateAt
        (publicCutSettlementFacade.process.successor (activated 3).state) := by
  have old := originalFacade.readoutAt_factorizes (originalActivated 3) .feedback
  have current := publicCutSettlementFacade.readoutAt_factorizes (activated 3) (.previous .responsibilities)
  have strict := Feedback.Cut.every_available_improvement_is_realized original input 0 _ choiceFromRuntime
    ⟨Feedback.Cut.Regression.quiet, Feedback.Cut.Regression.quiet_is_feasible,
      Feedback.Cut.Regression.quiet_is_a_strict_improvement_against_the_same_future_opponents⟩
  have native := executionFromRuntime.native_exact
  refine ⟨originalCutFromRuntime.settlement.generated,
    (Feedback.Cut.finite_strictness_iff_every_future_opponent original input 0 rfl rfl _ _).mp strict,
    Feedback.Cut.independent_replay_accepts_selection original input 0 _ choiceFromRuntime,
    ?_, ?_, executionFromRuntime.finance_prefix 3 (by decide +kernel),
    old.2.2.2.1, old.2.2.1, old.2.2.2.2, current.2.2.2.1, current.2.2.1, current.2.2.2.2⟩
  · exact Feedback.Cut.Regression.the_actual_candidate_keeps_resources_with_its_own_native_accounts.2.1
  · rw [congrFun native 0]
    exact Feedback.Cut.Regression.the_actual_candidate_keeps_resources_with_its_own_native_accounts.2.2.2.1

end CutSelection

namespace NativeAuthority

abbrev bound := Feedback.Authority.Regression.bound
abbrev source := bound.source
abbrev input : Feedback.Input bound.source.code := Feedback.Authority.Regression.input
abbrev publicFeedbackAuthorityFacade := Feedback.Authority.Runtime.facade bound input rfl rfl
abbrev activated := Feedback.Authority.Runtime.activated bound input rfl rfl

def cutFromRuntime (index : Nat) : Feedback.Authority.Disposition bound input index rfl rfl :=
  match publicFeedbackAuthorityFacade.readoutAt (activated (source.history.length + 2 + index)) .responsibilities with
  | .inl actual => actual.2 index (by
      change (ProgrammeHistory.visitAt source.input (activated (source.history.length + 2 + index)).state).current = _
      exact congrArg (fun ordinal => (ProgrammeHistory.visitAt source.input ordinal).current)
        (Feedback.Authority.Runtime.activated_state_is_the_generated_ordinal bound input rfl rfl _))
  | .inr impossible => nomatch impossible

def responsibilitySelectionFromRuntime (index : Nat) (reference : Feedback.Cut.Term source input index) :=
  (cutFromRuntime index).selection reference

def verifiedExecutionFromRuntime (index : Nat) (reference term : Feedback.Cut.Term source input index)
    (verified : Feedback.Authority.Trace.Selection.verify bound input index rfl reference term = true)
    (rival : Opponent source.code) :=
  (responsibilitySelectionFromRuntime index reference).verified_realization term verified rival

theorem every_independently_verified_planner_is_sound_and_actually_executed
    (index : Nat) (reference term : Feedback.Cut.Term source input index)
    (verified : Feedback.Authority.Trace.Selection.verify bound input index rfl reference term = true)
    (rival : Opponent source.code) (offset : Nat) :
    Feedback.Authority.Trace.Selection.AnswerSound bound input index rfl reference
        (.selected (Feedback.Authority.Trace.Selection.choiceOfVerified bound input index rfl reference term verified)) ∧
      (verifiedExecutionFromRuntime index reference term verified rival).native offset =
        Native.generate (Feedback.Cut.machine source input index rival term) (source.history.length + 1 + (index + offset)) ∧
      HEq (activated (source.history.length + 2 + index)).tick.generated.wholeLedgerWriteBack
        ((activated (source.history.length + 2 + index)).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          (activated (source.history.length + 2 + index)).current.visit.current) ∧
      (activated (source.history.length + 2 + index)).tick.nextCurrent = publicFeedbackAuthorityFacade.process.stateAt
        (publicFeedbackAuthorityFacade.process.successor (activated (source.history.length + 2 + index)).state) := by
  have rooted := publicFeedbackAuthorityFacade.readoutAt_factorizes (activated (source.history.length + 2 + index)) .responsibilities
  exact ⟨Feedback.Authority.Trace.Selection.answer_sound bound input index rfl rfl reference _,
    congrFun (verifiedExecutionFromRuntime index reference term verified rival).native_exact offset,
    rooted.2.2.1, rooted.2.2.2.2⟩

theorem every_verified_planner_continues_from_its_own_residual_and_root
    (index : Nat) (reference term : Feedback.Cut.Term source input index)
    (verified : Feedback.Authority.Trace.Selection.verify bound input index rfl reference term = true)
    (rival : Opponent source.code) :
    let target := Feedback.Authority.Selection.verifiedTarget bound input rfl index reference term verified rival
    let targetInput := Feedback.Future.takeover source input index rival
    let actual := Feedback.Authority.Runtime.activated target targetInput rfl rfl (source.history.length + 2 + (index + 1))
    (Feedback.Authority.Selection.verifiedNext bound input rfl rfl index reference term verified rival).feedback.state =
        Feedback.Residual.run source.code (Feedback.Residual.scheduleAt source index term.val)
          ⟨rival, input.budget⟩ (Feedback.Residual.seed source input index) 1 ∧
      (Feedback.Authority.Selection.verifiedNext bound input rfl rfl index reference term verified rival).current =
          Native.Authority.fullGenerate target (source.history.length + 1 + (index + 1)) ∧
        HEq ((Feedback.Authority.Runtime.facade target targetInput rfl rfl).readoutAt actual .responsibilities)
          (actual.tick.generated.projectionOutcome (.component ())) ∧
        HEq actual.tick.generated.wholeLedgerWriteBack
          (actual.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt actual.current.visit.current) ∧
        actual.tick.nextCurrent = (Feedback.Authority.Runtime.facade target targetInput rfl rfl).process.stateAt
          ((Feedback.Authority.Runtime.facade target targetInput rfl rfl).process.successor actual.state) :=
  And.intro
    (Feedback.Authority.Selection.verified_next_reads_the_supplied_planners_actual_residual bound input rfl rfl index reference term verified rival)
    (Feedback.Authority.Selection.every_verified_planner_owns_its_next_search_root bound input rfl rfl index reference term verified rival)

theorem every_actual_cut_generates_a_lawful_nondominated_selection_or_exact_blocking
    (index : Nat) (reference : Feedback.Cut.Term source input index) :
    (responsibilitySelectionFromRuntime index reference).outcome =
        Feedback.Authority.Trace.Selection.compile bound input index rfl reference ∧
      Feedback.Authority.Trace.Selection.AnswerSound bound input index rfl reference
        (responsibilitySelectionFromRuntime index reference).outcome ∧
      HEq (publicFeedbackAuthorityFacade.readoutAt (activated (source.history.length + 2 + index)) .responsibilities)
        ((activated (source.history.length + 2 + index)).tick.generated.projectionOutcome (.component ())) ∧
      HEq (activated (source.history.length + 2 + index)).tick.generated.wholeLedgerWriteBack
        ((activated (source.history.length + 2 + index)).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          (activated (source.history.length + 2 + index)).current.visit.current) ∧
      (activated (source.history.length + 2 + index)).tick.nextCurrent = publicFeedbackAuthorityFacade.process.stateAt
        (publicFeedbackAuthorityFacade.process.successor (activated (source.history.length + 2 + index)).state) := by
  have rooted := publicFeedbackAuthorityFacade.readoutAt_factorizes (activated (source.history.length + 2 + index)) .responsibilities
  refine ⟨?_, Feedback.Authority.Trace.Selection.answer_sound bound input index rfl rfl reference _,
    rooted.2.2.2.1, rooted.2.2.1, rooted.2.2.2.2⟩
  exact (responsibilitySelectionFromRuntime index reference).generated

theorem every_actual_cut_generates_each_candidates_own_service_grant_finance_and_challenge
    (index : Nat) (rival : Opponent source.code) (term : Feedback.Cut.Term source input index) :
    (cutFromRuntime index).candidates rival term =
        Native.Authority.fullGenerate (Feedback.Authority.candidate bound input index rival term)
          (Feedback.Authority.terminalDepth bound input index) ∧
      ProcessGame.Society.PublicFunction.Mandate.Challenge.I
        (Native.Authority.programme (Feedback.Authority.candidate bound input index rival term))
        (Native.Authority.sourceIndex (Feedback.Authority.candidate bound input index rival term)) =
          (Feedback.Cut.machine source input index rival term).input ∧
      HEq (publicFeedbackAuthorityFacade.readoutAt (activated (source.history.length + 2 + index)) .responsibilities)
        ((activated (source.history.length + 2 + index)).tick.generated.projectionOutcome (.component ())) ∧
      HEq (publicFeedbackAuthorityFacade.readoutAt (activated (source.history.length + 2 + index)) (.previous .feedback))
        ((activated (source.history.length + 2 + index)).tick.generated.projectionOutcome (.inherited (.component ()))) ∧
      HEq (activated (source.history.length + 2 + index)).tick.generated.wholeLedgerWriteBack
        ((activated (source.history.length + 2 + index)).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          (activated (source.history.length + 2 + index)).current.visit.current) ∧
      (activated (source.history.length + 2 + index)).tick.nextCurrent = publicFeedbackAuthorityFacade.process.stateAt
        (publicFeedbackAuthorityFacade.process.successor (activated (source.history.length + 2 + index)).state) := by
  have own := publicFeedbackAuthorityFacade.readoutAt_factorizes (activated (source.history.length + 2 + index)) .responsibilities
  have old := publicFeedbackAuthorityFacade.readoutAt_factorizes (activated (source.history.length + 2 + index)) (.previous .feedback)
  exact ⟨(cutFromRuntime index).candidates_exact rival term, rfl, own.2.2.2.1, old.2.2.2.1, own.2.2.1, own.2.2.2.2⟩

def originalChallengeRunFromRuntime (index : Nat) (rival : Opponent source.code)
    (term : Feedback.Cut.Term source input index)
    (record : {record // record ∈ (cutFromRuntime index).challenges rival term}) :=
  record.val.actualRun bound input index rival term rfl

def originalGrantRunFromRuntime (index : Nat) (rival : Opponent source.code)
    (term : Feedback.Cut.Term source input index)
    (record : {record // record ∈ (cutFromRuntime index).grants rival term}) :=
  record.val.actualRun bound input index rival term rfl

theorem every_actual_cut_consumes_the_entire_original_responsibility_census_and_its_own_next
    (index : Nat) (rival : Opponent source.code) (term : Feedback.Cut.Term source input index) :
    ((cutFromRuntime index).grants rival term).map (fun record => record.original.val) =
        Native.Authority.recordsAt bound (Feedback.Authority.arrivalDepth bound index) ∧
      ((cutFromRuntime index).challenges rival term).map (fun record => record.original.val) =
        Native.Authority.challengesAt bound (Feedback.Cut.start source index) ∧
      HEq (publicFeedbackAuthorityFacade.readoutAt (activated (source.history.length + 2 + index)) .responsibilities)
        ((activated (source.history.length + 2 + index)).tick.generated.projectionOutcome (.component ())) ∧
      HEq (activated (source.history.length + 2 + index)).tick.generated.wholeLedgerWriteBack
        ((activated (source.history.length + 2 + index)).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          (activated (source.history.length + 2 + index)).current.visit.current) ∧
      (activated (source.history.length + 2 + index)).tick.nextCurrent = publicFeedbackAuthorityFacade.process.stateAt
        (publicFeedbackAuthorityFacade.process.successor (activated (source.history.length + 2 + index)).state) := by
  have own := publicFeedbackAuthorityFacade.readoutAt_factorizes (activated (source.history.length + 2 + index)) .responsibilities
  rw [(cutFromRuntime index).grants_exact, (cutFromRuntime index).challenges_exact]
  exact ⟨Feedback.Authority.grant_migration_keeps_the_entire_original_census bound input index rival term rfl,
    Feedback.Authority.challenge_migration_keeps_the_entire_original_census bound input index rival term rfl,
    own.2.2.2.1, own.2.2.1, own.2.2.2.2⟩

theorem every_actual_cut_consumes_complete_receipts_with_joint_grant_transport_and_its_own_next
    (index : Nat) (rival : Opponent source.code) (term : Feedback.Cut.Term source input index) :
    Feedback.Authority.Trace.verify bound input index rival term rfl ((cutFromRuntime index).traces rival term) = true ∧
      ((cutFromRuntime index).traces (Feedback.Future.jointOpponent source input index rival) term).worlds =
        ((cutFromRuntime index).traces rival term).worlds ∧
      ((cutFromRuntime index).traces (Feedback.Future.jointOpponent source input index rival) term).originalGrants =
        ((cutFromRuntime index).traces rival term).originalGrants ∧
      (∀ record : Feedback.Authority.GrantAtArrival bound index,
        Feedback.Authority.Trace.JointGrantAgreement bound input index rival term rfl record) ∧
      HEq (publicFeedbackAuthorityFacade.readoutAt (activated (source.history.length + 2 + index)) .responsibilities)
        ((activated (source.history.length + 2 + index)).tick.generated.projectionOutcome (.component ())) ∧
      HEq (activated (source.history.length + 2 + index)).tick.generated.wholeLedgerWriteBack
        ((activated (source.history.length + 2 + index)).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          (activated (source.history.length + 2 + index)).current.visit.current) ∧
      (activated (source.history.length + 2 + index)).tick.nextCurrent = publicFeedbackAuthorityFacade.process.stateAt
        (publicFeedbackAuthorityFacade.process.successor (activated (source.history.length + 2 + index)).state) := by
  have own := publicFeedbackAuthorityFacade.readoutAt_factorizes (activated (source.history.length + 2 + index)) .responsibilities
  have originals := (congrArg Feedback.Authority.Trace.Manifest.originalGrants
    ((cutFromRuntime index).traces_exact (Feedback.Future.jointOpponent source input index rival) term)).trans
      ((Feedback.Authority.Trace.joint_original_grant_manifest bound input index rival term rfl rfl).trans
        (congrArg Feedback.Authority.Trace.Manifest.originalGrants ((cutFromRuntime index).traces_exact rival term)).symm)
  exact ⟨(Feedback.Authority.Trace.verify_iff bound input index rival term rfl _).mpr ((cutFromRuntime index).traces_exact rival term),
    (cutFromRuntime index).worlds_joint rival term, originals, (cutFromRuntime index).grants_joint rival term,
    own.2.2.2.1, own.2.2.1, own.2.2.2.2⟩

theorem every_actual_cut_consumes_complete_challenge_births_and_read_sources_with_its_own_next
    (index : Nat) (rival : Opponent source.code) (term : Feedback.Cut.Term source input index) :
    (((cutFromRuntime index).traces (Feedback.Future.jointOpponent source input index rival) term).candidateChallenges.map Prod.fst) =
        (((cutFromRuntime index).traces rival term).candidateChallenges.map Prod.fst) ∧
      Feedback.Authority.Trace.JointChallengeReads bound input index rival term rfl rfl ∧
      HEq (publicFeedbackAuthorityFacade.readoutAt (activated (source.history.length + 2 + index)) .responsibilities)
        ((activated (source.history.length + 2 + index)).tick.generated.projectionOutcome (.component ())) ∧
      HEq (activated (source.history.length + 2 + index)).tick.generated.wholeLedgerWriteBack
        ((activated (source.history.length + 2 + index)).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          (activated (source.history.length + 2 + index)).current.visit.current) ∧
      (activated (source.history.length + 2 + index)).tick.nextCurrent = publicFeedbackAuthorityFacade.process.stateAt
        (publicFeedbackAuthorityFacade.process.successor (activated (source.history.length + 2 + index)).state) := by
  have own := publicFeedbackAuthorityFacade.readoutAt_factorizes (activated (source.history.length + 2 + index)) .responsibilities
  exact ⟨(cutFromRuntime index).challenge_births_joint rival term, (cutFromRuntime index).challenge_reads_joint rival term,
    own.2.2.2.1, own.2.2.1, own.2.2.2.2⟩

theorem every_actual_cut_consumes_complete_original_challenge_lifecycles_and_its_own_next
    (index : Nat) (rival : Opponent source.code) (term : Feedback.Cut.Term source input index) :
    ((cutFromRuntime index).traces (Feedback.Future.jointOpponent source input index rival) term).originalChallenges =
        ((cutFromRuntime index).traces rival term).originalChallenges ∧
      (∀ record : Feedback.Authority.ChallengeAtArrival bound index,
        Feedback.Authority.Trace.JointChallengeLifecycleAgreement bound input index rival term rfl record) ∧
      HEq (publicFeedbackAuthorityFacade.readoutAt (activated (source.history.length + 2 + index)) .responsibilities)
        ((activated (source.history.length + 2 + index)).tick.generated.projectionOutcome (.component ())) ∧
      HEq (activated (source.history.length + 2 + index)).tick.generated.wholeLedgerWriteBack
        ((activated (source.history.length + 2 + index)).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          (activated (source.history.length + 2 + index)).current.visit.current) ∧
      (activated (source.history.length + 2 + index)).tick.nextCurrent = publicFeedbackAuthorityFacade.process.stateAt
        (publicFeedbackAuthorityFacade.process.successor (activated (source.history.length + 2 + index)).state) := by
  have own := publicFeedbackAuthorityFacade.readoutAt_factorizes (activated (source.history.length + 2 + index)) .responsibilities
  have original := (congrArg Feedback.Authority.Trace.Manifest.originalChallenges
    ((cutFromRuntime index).traces_exact (Feedback.Future.jointOpponent source input index rival) term)).trans
      ((Feedback.Authority.Trace.joint_original_challenge_manifest bound input index rival term rfl rfl).trans
        (congrArg Feedback.Authority.Trace.Manifest.originalChallenges ((cutFromRuntime index).traces_exact rival term)).symm)
  exact ⟨original, (cutFromRuntime index).challenges_joint rival term, own.2.2.2.1, own.2.2.1, own.2.2.2.2⟩

theorem every_actual_cut_consumes_all_candidate_grants_and_its_own_next
    (index : Nat) (rival : Opponent source.code) (term : Feedback.Cut.Term source input index) :
    ((cutFromRuntime index).traces (Feedback.Future.jointOpponent source input index rival) term).candidateGrants =
        ((cutFromRuntime index).traces rival term).candidateGrants ∧
      HEq (publicFeedbackAuthorityFacade.readoutAt (activated (source.history.length + 2 + index)) .responsibilities)
        ((activated (source.history.length + 2 + index)).tick.generated.projectionOutcome (.component ())) ∧
      HEq (activated (source.history.length + 2 + index)).tick.generated.wholeLedgerWriteBack
        ((activated (source.history.length + 2 + index)).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          (activated (source.history.length + 2 + index)).current.visit.current) ∧
      (activated (source.history.length + 2 + index)).tick.nextCurrent = publicFeedbackAuthorityFacade.process.stateAt
        (publicFeedbackAuthorityFacade.process.successor (activated (source.history.length + 2 + index)).state) := by
  have own := publicFeedbackAuthorityFacade.readoutAt_factorizes (activated (source.history.length + 2 + index)) .responsibilities
  exact ⟨(cutFromRuntime index).candidate_grants_joint rival term, own.2.2.2.1, own.2.2.1, own.2.2.2.2⟩

theorem every_actual_cut_consumes_the_complete_joint_manifest_and_each_local_challenge_with_its_own_next
    (index : Nat) (rival : Opponent source.code) (term : Feedback.Cut.Term source input index) :
    (cutFromRuntime index).traces (Feedback.Future.jointOpponent source input index rival) term =
        (cutFromRuntime index).traces rival term ∧
      (∀ (claim : Native.Authority.Challenge (Feedback.Authority.candidate bound input index rival term))
        (inside : claim.position.ordinal < Feedback.Cut.finish source input index),
        Feedback.Authority.Trace.JointCandidateChallengeAgreement bound input index rival term rfl rfl claim inside) ∧
      HEq (publicFeedbackAuthorityFacade.readoutAt (activated (source.history.length + 2 + index)) .responsibilities)
        ((activated (source.history.length + 2 + index)).tick.generated.projectionOutcome (.component ())) ∧
      HEq (activated (source.history.length + 2 + index)).tick.generated.wholeLedgerWriteBack
        ((activated (source.history.length + 2 + index)).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          (activated (source.history.length + 2 + index)).current.visit.current) ∧
      (activated (source.history.length + 2 + index)).tick.nextCurrent = publicFeedbackAuthorityFacade.process.stateAt
        (publicFeedbackAuthorityFacade.process.successor (activated (source.history.length + 2 + index)).state) := by
  have own := publicFeedbackAuthorityFacade.readoutAt_factorizes (activated (source.history.length + 2 + index)) .responsibilities
  exact ⟨(cutFromRuntime index).traces_joint rival term, (cutFromRuntime index).candidate_challenge_lifecycles_joint rival term,
    own.2.2.2.1, own.2.2.1, own.2.2.2.2⟩

theorem every_actual_cut_consumes_complete_responsibility_comparison_against_all_future_opponents
    (index : Nat)
    (relation : Feedback.Authority.Trace.Manifest Bool Unit ProcessGame.Society.PublicFunction.Mandate.Source.Port Unit Unit →
      Feedback.Authority.Trace.Manifest Bool Unit ProcessGame.Society.PublicFunction.Mandate.Source.Port Unit Unit → Prop)
    (new old : Feedback.Cut.Term source input index) :
    ((∀ table ∈ Feedback.Cut.tables source input index,
      relation ((cutFromRuntime index).traces (Feedback.Cut.opponent source input index table) new)
        ((cutFromRuntime index).traces (Feedback.Cut.opponent source input index table) old)) ↔
      ∀ rival : Opponent source.code,
        relation ((cutFromRuntime index).traces rival new) ((cutFromRuntime index).traces rival old)) ∧
      HEq (publicFeedbackAuthorityFacade.readoutAt (activated (source.history.length + 2 + index)) .responsibilities)
        ((activated (source.history.length + 2 + index)).tick.generated.projectionOutcome (.component ())) ∧
      HEq (activated (source.history.length + 2 + index)).tick.generated.wholeLedgerWriteBack
        ((activated (source.history.length + 2 + index)).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          (activated (source.history.length + 2 + index)).current.visit.current) ∧
      (activated (source.history.length + 2 + index)).tick.nextCurrent = publicFeedbackAuthorityFacade.process.stateAt
        (publicFeedbackAuthorityFacade.process.successor (activated (source.history.length + 2 + index)).state) := by
  have own := publicFeedbackAuthorityFacade.readoutAt_factorizes (activated (source.history.length + 2 + index)) .responsibilities
  refine ⟨?_, own.2.2.2.1, own.2.2.1, own.2.2.2.2⟩
  simp only [(cutFromRuntime index).traces_exact]
  exact Feedback.Authority.Trace.finite_manifest_relation_iff_every_future_opponent bound input index rfl rfl relation new old

theorem the_actual_cut_consumes_paid_challenge_settlement_and_retains_the_grant_and_principal :
    ((cutFromRuntime 0).current.challenges.map fun record =>
      record.2.state.current.history.map LifecycleEvent.kind) = [[.admitted, .deferred, .obligationTerminal]] ∧
      (cutFromRuntime 0).current.authority.mandates.length = 1 ∧
      Financial.outstanding source.input (cutFromRuntime 0).current.authority.joint.finance.current = 2 ∧
      HEq (publicFeedbackAuthorityFacade.readoutAt (activated 3) .responsibilities)
        ((activated 3).tick.generated.projectionOutcome (.component ())) ∧
      HEq (activated 3).tick.generated.wholeLedgerWriteBack
        ((activated 3).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt (activated 3).current.visit.current) ∧
      (activated 3).tick.nextCurrent = publicFeedbackAuthorityFacade.process.stateAt
        (publicFeedbackAuthorityFacade.process.successor (activated 3).state) := by
  have own := publicFeedbackAuthorityFacade.readoutAt_factorizes (activated 3) .responsibilities
  rw [(cutFromRuntime 0).current_exact]
  refine ⟨?_, ?_, ?_, own.2.2.2.1, own.2.2.1, own.2.2.2.2⟩
  · exact Feedback.Authority.Regression.paid_actual_exit_settles_the_same_native_challenge_without_erasing_other_responsibilities.2.2.2.1
  · decide +kernel
  · decide +kernel

theorem the_actual_cut_consumes_distinct_paid_and_quiet_original_responsibility_runs :
    (((cutFromRuntime 0).challenges Feedback.Authority.Regression.rival (Feedback.Cut.baseline source input 0)).map
      (fun record => (record.original.val.2.state.current.history.map LifecycleEvent.kind,
        record.after.state.current.history.map LifecycleEvent.kind))) =
        [([.admitted, .deferred], [.admitted, .deferred, .obligationTerminal])] ∧
      (((cutFromRuntime 0).challenges Feedback.Authority.Regression.rival Feedback.Authority.Regression.quiet).map
        (fun record => (record.original.val.2.state.current.history.map LifecycleEvent.kind,
          record.after.state.current.history.map LifecycleEvent.kind))) =
        [([.admitted, .deferred], [.admitted, .deferred])] ∧
      (((cutFromRuntime 0).grants Feedback.Authority.Regression.rival (Feedback.Cut.baseline source input 0)).map
        (fun record => (record.original.val.2.continuation.state.history.map LifecycleEvent.kind,
          record.after.continuation.state.history.map LifecycleEvent.kind))) =
        [([.admitted, .deferred], [.admitted, .deferred, .bearerRelease])] := by
  have paid := congrArg (fun records : List (Feedback.Authority.ChallengeContinuation bound input 0
      Feedback.Authority.Regression.rival (Feedback.Cut.baseline source input 0) rfl) =>
    records.map fun record => (record.original.val.2.state.current.history.map LifecycleEvent.kind,
      record.after.state.current.history.map LifecycleEvent.kind))
    ((cutFromRuntime 0).challenges_exact Feedback.Authority.Regression.rival (Feedback.Cut.baseline source input 0))
  have quiet := congrArg (fun records : List (Feedback.Authority.ChallengeContinuation bound input 0
      Feedback.Authority.Regression.rival Feedback.Authority.Regression.quiet rfl) =>
    records.map fun record => (record.original.val.2.state.current.history.map LifecycleEvent.kind,
      record.after.state.current.history.map LifecycleEvent.kind))
    ((cutFromRuntime 0).challenges_exact Feedback.Authority.Regression.rival Feedback.Authority.Regression.quiet)
  have grant := congrArg (fun records : List (Feedback.Authority.GrantContinuation bound input 0
      Feedback.Authority.Regression.rival (Feedback.Cut.baseline source input 0) rfl) =>
    records.map fun record => (record.original.val.2.continuation.state.history.map LifecycleEvent.kind,
      record.after.continuation.state.history.map LifecycleEvent.kind))
    ((cutFromRuntime 0).grants_exact Feedback.Authority.Regression.rival (Feedback.Cut.baseline source input 0))
  exact ⟨paid.trans Feedback.Authority.Regression.the_original_census_precedes_the_candidate_first_word.1,
    quiet.trans Feedback.Authority.Regression.the_original_census_precedes_the_candidate_first_word.2.1,
    grant.trans Feedback.Authority.Regression.a_paid_candidate_releases_jurisdiction_but_keeps_the_original_grant_residue.1⟩

abbrev quietBound := Feedback.Authority.Regression.quietBound
abbrev quietInput : Feedback.Input quietBound.source.code := Feedback.Future.takeover source input 0 Feedback.Authority.Regression.rival
abbrev publicPendingChallengeFacade := Feedback.Authority.Runtime.facade quietBound quietInput rfl rfl
abbrev quietActivated := Feedback.Authority.Runtime.activated quietBound quietInput rfl rfl

def quietCutFromRuntime : Feedback.Authority.Disposition quietBound quietInput 0 rfl rfl :=
  match publicPendingChallengeFacade.readoutAt (quietActivated 3) .responsibilities with
  | .inl actual => actual.2 0 rfl
  | .inr impossible => nomatch impossible

theorem the_explicit_none_root_consumes_its_own_pending_challenge :
    (quietCutFromRuntime.current.challenges.map fun record => record.2.state.current.history.map LifecycleEvent.kind) =
        [[.admitted, .deferred]] ∧
      HEq (publicPendingChallengeFacade.readoutAt (quietActivated 3) .responsibilities)
        ((quietActivated 3).tick.generated.projectionOutcome (.component ())) ∧
      HEq (quietActivated 3).tick.generated.wholeLedgerWriteBack
        ((quietActivated 3).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt (quietActivated 3).current.visit.current) ∧
      (quietActivated 3).tick.nextCurrent = publicPendingChallengeFacade.process.stateAt
        (publicPendingChallengeFacade.process.successor (quietActivated 3).state) := by
  have own := publicPendingChallengeFacade.readoutAt_factorizes (quietActivated 3) .responsibilities
  refine ⟨?_, own.2.2.2.1, own.2.2.1, own.2.2.2.2⟩
  rw [quietCutFromRuntime.current_exact]
  decide +kernel

end NativeAuthority

namespace LawfulSelection

abbrev fixture := Feedback.Authority.Trace.OrderRegression.bound
abbrev source := fixture.source
abbrev input := Feedback.Authority.Trace.OrderRegression.input
abbrev reference := Feedback.Cut.baseline source input 0
abbrev feasible := Feedback.Authority.Trace.OrderRegression.reference_is_feasible
abbrev choice := Feedback.Authority.Selection.choice fixture input rfl rfl 0 reference feasible
abbrev selected := Feedback.Authority.Selection.selected fixture input rfl rfl 0 reference feasible input.opponent
abbrev selectedInput := Feedback.Authority.Selection.selectedInput fixture input 0 input.opponent
abbrev selectedActive := Feedback.Authority.Selection.selected_active fixture input rfl rfl 0 reference feasible input.opponent
abbrev selectedEmpty := Feedback.Authority.Selection.selected_empty fixture input rfl rfl 0 reference feasible input.opponent
abbrev publicLawfulSelectionFacade := Feedback.Authority.Runtime.facade selected selectedInput selectedActive selectedEmpty
abbrev activated := Feedback.Authority.Runtime.activated selected selectedInput selectedActive selectedEmpty
abbrev nextFromRuntime := Feedback.Authority.Selection.next fixture input rfl rfl 0 reference feasible input.opponent

theorem the_actual_selected_source_and_next_cut_keep_their_own_native_accounts_and_roots :
    let original := Feedback.Authority.Runtime.activated fixture input rfl rfl 3
    let successor := activated 4
    Feedback.Authority.Trace.Selection.AgainstEveryOpponent fixture input 0 rfl choice.policy.term reference ∧
      Feedback.Authority.Trace.Selection.verify fixture input 0 rfl reference choice.policy.term = true ∧
      nextFromRuntime.current = Native.Authority.fullGenerate selected 3 ∧
      HEq original.tick.generated.wholeLedgerWriteBack
        (original.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt original.current.visit.current) ∧
      original.tick.nextCurrent = (Feedback.Authority.Runtime.facade fixture input rfl rfl).process.stateAt
        ((Feedback.Authority.Runtime.facade fixture input rfl rfl).process.successor original.state) ∧
      HEq successor.tick.generated.wholeLedgerWriteBack
        (successor.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt successor.current.visit.current) ∧
      successor.tick.nextCurrent = publicLawfulSelectionFacade.process.stateAt
        (publicLawfulSelectionFacade.process.successor successor.state) :=
  Feedback.Authority.Selection.selected_and_next_are_consumed_by_their_own_roots fixture input rfl rfl 0 reference feasible input.opponent

theorem the_next_actual_search_reads_the_selected_full_residual :
    nextFromRuntime.feedback.state = Feedback.Residual.run source.code
      (Feedback.Residual.scheduleAt source 0 choice.policy.term.val) ⟨input.opponent, input.budget⟩
      (Feedback.Residual.seed source input 0) 1 :=
  Feedback.Authority.Selection.next_reads_the_actual_selected_residual fixture input rfl rfl 0 reference feasible input.opponent

end LawfulSelection

end SaturationMonoid.Tracks.LivingLawPublicFeedbackInstance
