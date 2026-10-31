import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.Runtime.SourceGeneratedTenureQueueAppendRuntime
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.CrossCompiler.Recurrence.SourceGeneratedCrossCompilerRelationAppendUBI

/-!
# Canonical cross-compiler relation append runtime

The unique U8-to-append runtime cuts over after one homogeneous relation
bootstrap.  Tick `9 + 2*n` executes the `n`th heterogeneous actual action;
tick `10 + 2*n` answers only its distinct target selection.  Both stage and
runtime states are generated recursively, so the theorem reaches every
finite depth without storing an infinite future.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedCrossCompilerRelationAppendRuntime

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open M14EssentialAccessRelationFixture
open M14SourceGeneratedTenureQueueAppendRuntime
open M14SourceGeneratedRootedAccountedUnfoldingAppendLedger
open M14SourceGeneratedRootedAccountedUnfoldingAppendRoot
open M14SourceGeneratedEssentialAccessCriticalActionQueueSuccession
open M14SourceGeneratedCrossCompilerRelationCurrentRecurrence
open M14SourceGeneratedCrossCompilerRelationAppendStage
open M14SourceGeneratedCrossCompilerRelationAppendPresentation
open M14SourceGeneratedCrossCompilerRelationAppendUBI
open M14SourceGeneratedSequentialCrossCompilerRelationAppend

def crossActionRuntimeDepth : Nat → Nat
  | 0 => 9
  | depth + 1 => crossActionRuntimeDepth depth + 2

def crossSelectionRuntimeDepth (depth : Nat) : Nat :=
  crossActionRuntimeDepth depth + 1

@[simp] theorem crossActionRuntimeDepth_closed (depth : Nat) :
    crossActionRuntimeDepth depth = 9 + 2 * depth := by
  induction depth with
  | zero => rfl
  | succ depth inductionHypothesis =>
      rw [crossActionRuntimeDepth, inductionHypothesis]
      omega

@[simp] theorem crossSelectionRuntimeDepth_closed (depth : Nat) :
    crossSelectionRuntimeDepth depth = 10 + 2 * depth := by
  rw [crossSelectionRuntimeDepth, crossActionRuntimeDepth_closed]
  omega

theorem crossActionState_node_exact : ∀ depth : Nat,
    (runtime.stateAt (crossActionRuntimeDepth depth)).engine.node =
      .active (crossCompilerActionPresentationAt depth) := by
  intro depth
  induction depth with
  | zero => rfl
  | succ depth inductionHypothesis =>
      change
        (((runtime.stateAt (crossActionRuntimeDepth depth)).tick.nextState
          ).tick.nextState).engine.node =
          .active (crossCompilerActionPresentationAt (depth + 1))
      generalize state_eq :
        runtime.stateAt (crossActionRuntimeDepth depth) = state
        at inductionHypothesis ⊢
      cases state
      rename_i engine activation
      cases engine
      rename_i processState
      have processStateExact :
          processState = ProcessState.crossAction depth := by
        have erasedExact := congrArg RootInquiryProcessNode.erase
          inductionHypothesis
        change (processPresentation processState).erase =
          (crossCompilerActionPresentationAt depth).erase at erasedExact
        exact processPresentation_erase_injective erasedExact
      subst processState
      rfl

theorem crossSelectionState_node_exact (depth : Nat) :
    (runtime.stateAt (crossSelectionRuntimeDepth depth)).engine.node =
      .active (crossCompilerSelectionPresentationAt depth) := by
  change ((runtime.stateAt (crossActionRuntimeDepth depth)).tick.nextState
    ).engine.node = _
  have actionNode := crossActionState_node_exact depth
  generalize state_eq :
    runtime.stateAt (crossActionRuntimeDepth depth) = state
    at actionNode ⊢
  cases state
  rename_i engine activation
  cases engine
  rename_i processState
  have processStateExact : processState = ProcessState.crossAction depth := by
    have erasedExact := congrArg RootInquiryProcessNode.erase actionNode
    change (processPresentation processState).erase =
      (crossCompilerActionPresentationAt depth).erase at erasedExact
    exact processPresentation_erase_injective erasedExact
  subst processState
  rfl

def crossActionTickAt (depth : Nat) :=
  runtime.tickAt (crossActionRuntimeDepth depth)

def crossSelectionTickAt (depth : Nat) :=
  runtime.tickAt (crossSelectionRuntimeDepth depth)

theorem crossActionTick_resolution_heq (depth : Nat) :
    HEq (crossActionTickAt depth).resolution
      ((InternalInquiryResolutionAt.actualAction
        (generatedCrossCompilerRelationAppendActionAt depth)) :
        InternalInquiryResolutionAt
          (crossCompilerActionPresentationAt depth) ()) := by
  unfold crossActionTickAt SourceNativeInquiryRuntime.tickAt
  have actionNode := crossActionState_node_exact depth
  generalize state_eq :
    runtime.stateAt (crossActionRuntimeDepth depth) = state
    at actionNode ⊢
  cases state
  rename_i engine activation
  cases engine
  rename_i processState
  have processStateExact : processState = ProcessState.crossAction depth := by
    have erasedExact := congrArg RootInquiryProcessNode.erase actionNode
    change (processPresentation processState).erase =
      (crossCompilerActionPresentationAt depth).erase at erasedExact
    exact processPresentation_erase_injective erasedExact
  subst processState
  exact HEq.rfl

theorem crossSelectionTick_resolution_heq (depth : Nat) :
    HEq (crossSelectionTickAt depth).resolution
      ((InternalInquiryResolutionAt.directlyAnswered
        (crossCompilerSelectionAnswerFaceAt depth)
        (crossCompilerSelectionAnswerConsumerAt depth)) :
        InternalInquiryResolutionAt
          (crossCompilerSelectionPresentationAt depth) ()) := by
  unfold crossSelectionTickAt SourceNativeInquiryRuntime.tickAt
  have selectionNode := crossSelectionState_node_exact depth
  generalize state_eq :
    runtime.stateAt (crossSelectionRuntimeDepth depth) = state
    at selectionNode ⊢
  cases state
  rename_i engine activation
  cases engine
  rename_i processState
  have processStateExact :
      processState = ProcessState.crossSelection depth := by
    have erasedExact := congrArg RootInquiryProcessNode.erase selectionNode
    change (processPresentation processState).erase =
      (crossCompilerSelectionPresentationAt depth).erase at erasedExact
    exact processPresentation_erase_injective erasedExact
  subst processState
  exact HEq.rfl

theorem crossActionRuntimeResumption (depth : Nat) :
    SourceNativeInquiryRuntime.SequentialActualActionResumptionAt
      (generatedCrossCompilerRelationAppendActionAt depth) runtime
        (crossActionRuntimeDepth depth) := by
  constructor
  unfold SourceNativeInquiryRuntime.tickAt
  have actionNode := crossActionState_node_exact depth
  generalize state_eq :
    runtime.stateAt (crossActionRuntimeDepth depth) = state
    at actionNode ⊢
  cases state
  rename_i engine activation
  cases engine
  rename_i processState
  have processStateExact : processState = ProcessState.crossAction depth := by
    have erasedExact := congrArg RootInquiryProcessNode.erase actionNode
    change (processPresentation processState).erase =
      (crossCompilerActionPresentationAt depth).erase at erasedExact
    exact processPresentation_erase_injective erasedExact
  subst processState
  exact HEq.rfl

theorem crossActionPresentation_erase_injective :
    Function.Injective
      (fun depth : Nat => (crossCompilerActionPresentationAt depth).erase) := by
  intro left right equality
  have stateEquality : ProcessState.crossAction left =
      ProcessState.crossAction right :=
    processPresentation_erase_injective equality
  exact ProcessState.crossAction.inj stateEquality

theorem adjacentSeed_differentCrossCompilerOccurrence (depth : Nat) :
    (crossCompilerCurrentStageAt (depth + 1)).targetSeed ≠
        (crossCompilerCurrentStageAt depth).targetSeed ∧
      (crossCompilerActionPresentationAt (depth + 1)).erase ≠
        (crossCompilerActionPresentationAt depth).erase := by
  refine ⟨crossCompilerCurrentStageAt_targetSeed_ne_succ depth, ?_⟩
  intro equality
  exact Nat.succ_ne_self depth
    (crossActionPresentation_erase_injective equality)

theorem periodThreeSeed_differentCrossCompilerOccurrence (depth : Nat) :
    (crossCompilerCurrentStageAt (depth + 3)).targetSeed =
        (crossCompilerCurrentStageAt depth).targetSeed ∧
      (crossCompilerActionPresentationAt (depth + 3)).erase ≠
        (crossCompilerActionPresentationAt depth).erase := by
  refine ⟨crossCompilerCurrentStageAt_targetSeed_add_three depth, ?_⟩
  intro equality
  have depthEquality : depth + 3 = depth :=
    crossActionPresentation_erase_injective equality
  omega

theorem noDormantHomogeneousRelationActionOne :
    IsEmpty { index : Fin 1 // index.val = 1 } :=
  ⟨fun indexed => by omega⟩

theorem crossCompilerRuntime_directConsumer (depth : Nat) :
    SourceNativeInquiryRuntime.SequentialActualActionResumptionAt
        (generatedCrossCompilerRelationAppendActionAt depth) runtime
          (crossActionRuntimeDepth depth) ∧
      (runtime.stateAt (crossActionRuntimeDepth depth)).engine.node =
        .active (crossCompilerActionPresentationAt depth) ∧
      (runtime.stateAt (crossSelectionRuntimeDepth depth)).engine.node =
        .active (crossCompilerSelectionPresentationAt depth) ∧
      CrossCompilerRelationAppendReceiptCoreAt depth
        (appendStageAt depth).exactSource ∧
      (generatedCrossCompilerRelationAppendActionAt depth
        ).target.targetRoot = (appendStageAt (depth + 1)).sourceRoot ∧
      (generatedCrossCompilerRelationAppendActionAt depth
        ).target.firstSuccessor.targetCurrent =
          (crossCompilerCurrentStageAt depth).targetCurrent ∧
      (crossCompilerCurrentStageAt depth).targetCurrent.root =
        .inr (crossCompilerCurrentStageAt depth).targetSeed ∧
      (crossCompilerCurrentStageAt depth).targetCurrent.branches =
        AccountedBranches.singleton
          ((crossCompilerCurrentStageAt depth).actionCurrent.map Sum.inl) ∧
      HEq (crossCompilerUBIPayloadAt depth).consumer
        M14UBIProofCarryingRootRestriction.sourceGeneratedUBIRootRestriction :=
  ⟨crossActionRuntimeResumption depth,
    crossActionState_node_exact depth,
    crossSelectionState_node_exact depth,
    (generatedCrossCompilerRelationAppendActionAt depth).receipt.down.down,
    rfl,
    (generatedCrossCompilerRelationAppendActionAt depth
      ).receipt.down.down.targetFirstWrite,
    crossCompilerCurrentStageAt_targetRoot_exact depth,
    crossCompilerCurrentStageAt_targetBranches_exact depth,
    crossCompilerUBIPayloadConsumer_exact depth⟩

theorem finiteQueueExhaustion_crossCompilerRuntimeContinues :
    IsEmpty RecurrentQueueCriticalActionSuccessorAt ∧
      ∀ depth : Nat,
        SourceNativeInquiryRuntime.SequentialActualActionResumptionAt
          (generatedCrossCompilerRelationAppendActionAt depth) runtime
            (crossActionRuntimeDepth depth) :=
  ⟨recurrentQueueCriticalActionSuccessor_isEmpty,
    crossActionRuntimeResumption⟩

end
end M14SourceGeneratedCrossCompilerRelationAppendRuntime
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCrossCompilerRelationAppendRuntime.crossActionRuntimeResumption
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCrossCompilerRelationAppendRuntime.crossCompilerRuntime_directConsumer
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCrossCompilerRelationAppendRuntime.finiteQueueExhaustion_crossCompilerRuntimeContinues
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCrossCompilerRelationAppendRuntime.adjacentSeed_differentCrossCompilerOccurrence
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCrossCompilerRelationAppendRuntime.periodThreeSeed_differentCrossCompilerOccurrence
