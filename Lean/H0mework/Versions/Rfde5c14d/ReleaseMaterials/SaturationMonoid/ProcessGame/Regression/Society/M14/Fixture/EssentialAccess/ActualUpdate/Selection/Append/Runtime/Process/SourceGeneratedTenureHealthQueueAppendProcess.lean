import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.Runtime.Process.State.SourceGeneratedTenureHealthPlatformRelationProcessState

/-!
# Canonical U8-to-cross-compiler recurrence process

This is the sole inquiry-engine process for the append chain.  Its finite
queue prefix and one homogeneous relation bootstrap hand control to the
source-generated heterogeneous recurrence, which alternates actual action
with its generated selection occurrence.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedTenureQueueAppendRuntime

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open ConstructiveRoot.ObstructionGeneratedMinimalCoface
open M14SourceGeneratedHealthTargetCriticalEventSelectionU8Runtime
open M14SourceGeneratedCriticalEventSelectionRevisedLedger
open M14SourceGeneratedCriticalEventSelectionRevisedRoot
open M14SourceGeneratedEssentialAccessCriticalActionAppendLedger
open M14SourceGeneratedRootedAccountedUnfoldingAppendLedger
open M14SourceGeneratedTenureQueueAppendTarget
open M14SourceGeneratedSequentialTenureQueueAppend
open M14SourceGeneratedQueueAppendContinuation
open M14SourceGeneratedCriticalActionAppendContinuation
open M14SourceGeneratedRootedAccountedUnfoldingAppendContinuation
open M14SourceGeneratedTenureQueueAppendContinuation
open M14SourceGeneratedHealthQueueActionAtTenureRoot
open M14SourceGeneratedSequentialHealthQueueAppend
open M14SourceGeneratedHealthQueueAppendContinuation
open M14SourceGeneratedPlatformQueueActionAtHealthRoot
open M14SourceGeneratedSequentialPlatformQueueAppend
open M14SourceGeneratedLineageFoldRelationRecurrenceStage
open M14SourceGeneratedLineageFoldRelationRecurrencePresentation
open M14SourceGeneratedCrossCompilerRelationCurrentRecurrence
open M14SourceGeneratedCrossCompilerRelationAppendStage
open M14SourceGeneratedCrossCompilerRelationAppendPresentation

set_option linter.unusedSimpArgs false in
theorem processPresentation_lineageLabel_exact (state : ProcessState) :
    erasedLineageLabel (processPresentation state).erase =
      processExpectedLineageLabel state := by
  cases state <;>
    simp [processExpectedLineageLabel, erasedLineageLabel,
      processPresentation, processRank, RootInquiryStatePresentation.erase,
      RootInquiryEngineStateAt.create,
      revisedTenureActionPresentation, revisedTenureActionInquiryState,
      tenureAppendSelectionPresentationAt,
      tenureAppendSelectionEngineStateAt, tenureAppendSelectionInquiryStateAt,
      tenureHealthActionPresentation, tenureHealthActionInquiryState,
      healthAppendPresentationAt, queueAppendPresentationAt,
      queueAppendInquiryStateAt,
      healthPlatformActionPresentation, healthPlatformActionInquiryState,
      RelationLineageRecurrenceStage.selectionPresentation,
      RelationLineageRecurrenceStage.actionCurrent,
      criticalActionAppendPresentationAt,
      criticalActionAppendInquiryStateAt,
      actionPresentation, actionEngineState, actionInquiryState,
      crossCompilerActionPresentationAt,
      crossCompilerActionEngineStateAt, crossCompilerActionInquiryStateAt,
      crossCompilerSelectionPresentationAt, rootedAppendPresentationAt,
      rootedAppendInquiryStateAt,
      NewV, revisedVocabulary, AppendVAt, appendVocabulary,
      RootedAppendVAt, rootedAppendVocabulary,
      tenureAppendPrior, healthAppendPrior, platformAppendPrior,
      tenureAppendTemporalVisitAt, healthAppendTemporalVisitAt,
      queueAppendTemporalVisitAt, criticalActionAppendTemporalVisitAt,
      rootedAppendTemporalVisitAt, SourceNativeTemporalVisitAt.finite,
      tenureAppendRootVisitAt_zero_current,
      healthAppendRootVisitAt_zero_current,
      criticalActionAppendRootVisitAt_zero_current,
      rootedAppendRootVisitAt_zero_current,
      appendedCriticalSelectionCurrent_traceLength,
      retainedSelectionNext_traceLength,
      healthAppendPrior_traceLength, platformAppendPrior_traceLength,
      initialRelationSelectionCurrent_traceLength,
      stageAt_actionCurrent_traceLength,
      stageAt_nextSelectionCurrent_traceLength,
      crossCompilerActionCurrent_traceLength,
      crossCompilerSelectionCurrent_traceLength,
      crossCompilerTargetCurrent_traceLength]
  case healthAction =>
    exact healthAppendPrior_traceLength
  case healthSelection =>
    change (healthAppendRootVisitAt 0).current.trace.length =
      tenureAppendPrior.trace.length + 3
    rw [healthAppendRootVisitAt_zero_current]
    rw [appendedCriticalSelectionCurrent_traceLength,
      healthAppendPrior_traceLength]
  case platformAction =>
    exact platformAppendPrior_traceLength
  case platformSelection =>
    change platformAppendPrior.trace.length =
      tenureAppendPrior.trace.length + 4
    exact platformAppendPrior_traceLength
  case relationAction index =>
    have index_eq : index = 0 := Fin.eq_zero index
    subst index
    exact stageAt_actionCurrent_traceLength 0
  case relationSelection index =>
    have index_eq : index = 0 := Fin.eq_zero index
    subst index
    change (stageAt 0).actionCurrent.trace.length =
      tenureAppendPrior.trace.length + 6
    exact stageAt_actionCurrent_traceLength 0
  case crossSelection depth =>
    rw [← (M14SourceGeneratedSequentialCrossCompilerRelationAppend.appendStageAt
      depth).targetCurrent_exact]
    exact crossCompilerSelectionCurrent_traceLength depth
  case crossAction depth =>
    let lineageExact :=
      crossCompilerRelationAppendStageAt_sourceLineage_exact depth
    refine ⟨lineageExact.1, lineageExact.2.trans ?_⟩
    exact heq_of_eq (congrArg
      (fun length =>
        (NewN.lineageAt minimalCoface.cofaceSupport, length))
      (crossCompilerActionCurrent_traceLength depth))

theorem processState_eq_of_nonold_rank_eq
    {left right : ProcessState}
    (left_ne : left ≠ .oldU8) (right_ne : right ≠ .oldU8)
    (rank_eq : processRank left = processRank right) : left = right := by
  cases left <;> cases right <;>
    simp [processRank] at left_ne right_ne rank_eq ⊢ <;> omega

theorem processPresentation_nonold_support_exact
    (state : ProcessState) (nonold : state ≠ .oldU8) :
    (processPresentation state).N.Support = NewN.Support := by
  cases state with
  | oldU8 => exact False.elim (nonold rfl)
  | tenureAction | tenureSelection | healthAction | healthSelection |
      platformAction | platformSelection | relationAction | relationSelection |
      crossAction | crossSelection => rfl

theorem processPresentation_erase_injective :
    Function.Injective (fun state => (processPresentation state).erase) := by
  intro left right equality
  have network_eq := congrArg AnyAuthoritativeRootCurrent.N equality
  have support_eq := congrArg WorldRelationNetwork.Support network_eq
  have lineage_eq := congrArg erasedLineageLabel equality
  rw [processPresentation_lineageLabel_exact left,
    processPresentation_lineageLabel_exact right] at lineage_eq
  by_cases left_ne : left ≠ .oldU8
  · by_cases right_ne : right ≠ .oldU8
    · have exactLineage_eq :
          (⟨NewN.Lineage × Nat,
              (NewN.lineageAt minimalCoface.cofaceSupport,
                tenureAppendPrior.trace.length + processRank left)⟩ :
              Sigma fun Lineage : Type => Lineage) =
            ⟨NewN.Lineage × Nat,
              (NewN.lineageAt minimalCoface.cofaceSupport,
                tenureAppendPrior.trace.length + processRank right)⟩ := by
          simpa [processExpectedLineageLabel, left_ne, right_ne] using lineage_eq
      have pair_eq :
          (NewN.lineageAt minimalCoface.cofaceSupport,
              tenureAppendPrior.trace.length + processRank left) =
            (NewN.lineageAt minimalCoface.cofaceSupport,
              tenureAppendPrior.trace.length + processRank right) :=
        eq_of_heq (Sigma.mk.inj_iff.mp exactLineage_eq).2
      have rank_eq := congrArg Prod.snd pair_eq
      exact processState_eq_of_nonold_rank_eq left_ne right_ne (by omega)
    · have right_eq : right = .oldU8 := not_ne_iff.mp right_ne
      subst right
      exact False.elim (healthTargetOldSupport_ne_revisedSelectionSupport
        (support_eq.symm.trans
          (processPresentation_nonold_support_exact left left_ne)))
  · have left_eq : left = .oldU8 := not_ne_iff.mp left_ne
    subst left
    by_cases right_ne : right ≠ .oldU8
    · exact False.elim (healthTargetOldSupport_ne_revisedSelectionSupport
        (support_eq.trans
          (processPresentation_nonold_support_exact right right_ne)))
    · exact congrArg id (not_ne_iff.mp right_ne).symm

def process : SourceNativeInquiryEngineProcess.{0} where
  State := ProcessState
  stateAt := fun state => .active (processPresentation state)
  erase_injective := by
    intro left right leftState rightState leftActive rightActive equality
    cases leftActive
    cases rightActive
    exact processPresentation_erase_injective equality
  initial := .oldU8
  successorAt := by
    intro state query
    cases state with
    | oldU8 =>
        change Unit at query
        cases query
        refine ⟨.tenureAction, ?_, ?_⟩
        · change revisedTenureActionPresentation.erase =
            ⟨NewN,
              (ConstructiveRoot.TypedSemanticWorldNetworkU8Recovery.generatedNewTargetAnswerAndNext
                typedRevisionSource).nextCurrent⟩
          rfl
        · exact HEq.rfl
    | tenureAction =>
        change Unit at query
        cases query
        refine ⟨.tenureSelection, ?_⟩
        exact RootInquiryProcessNode.active_actualAction_successor_valid
          revisedTenureActionPresentation
          (tenureAppendSelectionPresentationAt 0) ()
          generatedTenureQueueAppendAction rfl rfl HEq.rfl
    | tenureSelection =>
        change Unit at query
        cases query
        refine ⟨.healthAction, ?_⟩
        exact RootInquiryProcessNode.active_directlyAnswered_successor_valid
          (tenureAppendSelectionPresentationAt 0)
          tenureHealthActionPresentation ()
          (tenureAppendSelectionAnswerFaceAt 0)
          (tenureAppendSelectionAnswerConsumerAt 0)
          rfl rfl HEq.rfl
    | healthAction =>
        change Unit at query
        cases query
        refine ⟨.healthSelection, ?_⟩
        exact RootInquiryProcessNode.active_actualAction_successor_valid
          tenureHealthActionPresentation (healthAppendPresentationAt 0) ()
          generatedHealthQueueAppendAction rfl rfl HEq.rfl
    | healthSelection =>
        change Unit at query
        cases query
        refine ⟨.platformAction, ?_⟩
        exact RootInquiryProcessNode.active_directlyAnswered_successor_valid
          (healthAppendPresentationAt 0) healthPlatformActionPresentation ()
          (healthAppendAnswerFaceAt 0) (healthAppendAnswerConsumerAt 0)
          rfl rfl HEq.rfl
    | platformAction =>
        change Unit at query
        cases query
        refine ⟨.platformSelection, ?_⟩
        exact RootInquiryProcessNode.active_actualAction_successor_valid
          healthPlatformActionPresentation (stageAt 0).selectionPresentation ()
          generatedPlatformQueueAppendAction rfl rfl HEq.rfl
    | platformSelection =>
        change Unit at query
        cases query
        refine ⟨.relationAction 0, ?_⟩
        exact selectionToActionSuccessorValid (stageAt 0)
    | relationAction index =>
        change Unit at query
        cases query
        refine ⟨.relationSelection index, ?_⟩
        exact actionToNextSelectionSuccessorValid (stageAt index.val)
    | relationSelection index =>
        change Unit at query
        cases query
        have index_eq : index = 0 := Fin.eq_zero index
        subst index
        refine ⟨.crossAction 0, ?_⟩
        exact homogeneousSelectionToFirstCrossActionSuccessorValid
    | crossAction depth =>
        change Unit at query
        cases query
        refine ⟨.crossSelection depth, ?_⟩
        exact crossActionToSelectionSuccessorValid depth
    | crossSelection depth =>
        change Unit at query
        cases query
        refine ⟨.crossAction (depth + 1), ?_⟩
        exact crossSelectionToNextActionSuccessorValid depth

def runtimeInitialQuery : (process.stateAt process.initial).Query := ()

theorem runtimeInitialQuery_unique
    (candidate : (process.stateAt process.initial).Query) :
    candidate = runtimeInitialQuery := by
  cases candidate
  rfl

def runtimeNextQueryAt
    (state : ProcessState) (query : (process.stateAt state).Query) :
    (process.stateAt (process.successorAt state query).1).Query := by
  cases state with
  | relationSelection index =>
      change Unit at query
      cases query
      have index_eq : index = 0 := Fin.eq_zero index
      subst index
      change Unit
      exact ()
  | oldU8 | tenureAction | tenureSelection | healthAction | healthSelection |
      platformAction | platformSelection | relationAction | crossAction |
      crossSelection =>
      change Unit at query
      cases query
      change Unit
      exact ()

theorem runtimeNextQuery_unique
    (state : ProcessState) (query : (process.stateAt state).Query)
    (candidate :
      (process.stateAt (process.successorAt state query).1).Query) :
    candidate = runtimeNextQueryAt state query := by
  cases state with
  | relationSelection index =>
      change Unit at query
      cases query
      have index_eq : index = 0 := Fin.eq_zero index
      subst index
      change Unit at candidate
      cases candidate
      rfl
  | oldU8 | tenureAction | tenureSelection | healthAction | healthSelection |
      platformAction | platformSelection | relationAction | crossAction |
      crossSelection =>
      change Unit at query
      cases query
      change Unit at candidate
      cases candidate
      rfl

end
end M14SourceGeneratedTenureQueueAppendRuntime
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedTenureQueueAppendRuntime.process
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedTenureQueueAppendRuntime.processPresentation_erase_injective
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedTenureQueueAppendRuntime.runtimeNextQuery_unique
