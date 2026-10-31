import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.Runtime.SourceGeneratedTenureQueueAppendRuntime
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.Relation.Recurrence.SourceGeneratedLineageFoldRelationRecurrenceUBI

/-!
# Homogeneous relation-lineage runtime bootstrap

The unique runtime executes only stage zero at ticks 7/8 before handing the
tail to the cross-compiler recurrence.  Later homogeneous stages remain
source-generated domain objects, but have no sibling runtime authority.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedRelationLineageRecurrenceRuntime

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open M14EssentialAccessRelationFixture
open M14SourceGeneratedSelectedEssentialAccessCriticalEvent
open M14SourceGeneratedTenureQueueAppendRuntime
open M14SourceGeneratedLineageFoldRelationRecurrenceStage
open M14SourceGeneratedLineageFoldRelationRecurrencePresentation
open M14SourceGeneratedLineageFoldRelationRecurrenceUBI
open M14SourceGeneratedEssentialAccessCriticalActionAppendLedger
open M14SourceGeneratedSequentialCriticalActionAppendTarget
open M14SourceGeneratedEssentialAccessCriticalActionQueueSuccession
open M14SourceGeneratedEssentialAccessCriticalActionAppendRoot
open M14SourceGeneratedEssentialAccessCriticalTerminal
open M14SourceGeneratedCriticalActionAppendContinuation
open M14UBIProofCarryingRootRestriction

def relationActionRuntimeDepth (_index : Fin 1) : Nat := 7

def relationSelectionRuntimeDepth (_index : Fin 1) : Nat := 8

@[simp] theorem relationActionRuntimeDepth_closed (index : Fin 1) :
    relationActionRuntimeDepth index = 7 :=
  rfl

@[simp] theorem relationSelectionRuntimeDepth_closed (index : Fin 1) :
    relationSelectionRuntimeDepth index = 8 :=
  rfl

theorem relationActionState_node_exact (index : Fin 1) :
    (runtime.stateAt (relationActionRuntimeDepth index)).engine.node =
      .active (actionPresentation (stageAt index.val)) := by
  have index_eq : index = 0 := Fin.eq_zero index
  subst index
  rfl

theorem relationSelectionState_node_exact (index : Fin 1) :
    (runtime.stateAt (relationSelectionRuntimeDepth index)).engine.node =
      .active (stageAt (index.val + 1)).selectionPresentation := by
  have index_eq : index = 0 := Fin.eq_zero index
  subst index
  rfl

def relationActionTickAt (index : Fin 1) :=
  runtime.tickAt (relationActionRuntimeDepth index)

def relationSelectionTickAt (index : Fin 1) :=
  runtime.tickAt (relationSelectionRuntimeDepth index)

theorem relationActionTick_resolution_heq (index : Fin 1) :
    HEq (relationActionTickAt index).resolution
      ((InternalInquiryResolutionAt.actualAction
        (stageAt index.val).generatedAction) :
        InternalInquiryResolutionAt
          (actionPresentation (stageAt index.val)) ()) := by
  have index_eq : index = 0 := Fin.eq_zero index
  subst index
  exact HEq.rfl

theorem relationSelectionTick_resolution_heq (index : Fin 1) :
    HEq (relationSelectionTickAt index).resolution
      ((InternalInquiryResolutionAt.directlyAnswered
        (stageAt (index.val + 1)).selectionAnswerFace
        (stageAt (index.val + 1)).selectionAnswerConsumer) :
        InternalInquiryResolutionAt
          (stageAt (index.val + 1)).selectionPresentation ()) := by
  have index_eq : index = 0 := Fin.eq_zero index
  subst index
  exact HEq.rfl

theorem relationActionRuntimeResumption (index : Fin 1) :
    SourceNativeInquiryRuntime.SequentialActualActionResumptionAt
      (stageAt index.val).generatedAction runtime
        (relationActionRuntimeDepth index) := by
  have index_eq : index = 0 := Fin.eq_zero index
  subst index
  constructor
  exact HEq.rfl

theorem relationActionInstalled_exact (depth : Nat) :
    (stageAt depth).installedRenewal.selected.selectedEvent =
        (stageAt depth).nextCarrier.event ∧
      (stageAt depth).installedRenewal.payload.consumer.action =
        (stageAt depth).nextCarrier.action ∧
      (stageAt depth).installedRenewal.payload.disposition.update =
        sourceGeneratedEssentialAccessCriticalActualUpdateAt
          (stageAt depth).nextCarrier.event :=
  let core := (stageAt depth).generatedAction.receipt.down.down.2
  ⟨core.selectedRenewal.1, core.selectedRenewal.2.1,
    core.selectedRenewal.2.2⟩

theorem relationLineageBootstrapRuntime_directConsumer :
    SourceNativeInquiryRuntime.SequentialActualActionResumptionAt
        (stageAt 0).generatedAction runtime 7 ∧
      (runtime.stateAt 7).engine.node =
        .active (actionPresentation (stageAt 0)) ∧
      (runtime.stateAt 8).engine.node =
        .active (stageAt 1).selectionPresentation ∧
      RelationLineageRecurrenceStage.SourceSealAt (stageAt 0)
        (stageAt 0).exactSource ∧
      SequentialCriticalActionAppendReceiptCoreAt
        (stageAt 0).predecessorRoot
        (stageAt 0).predecessorOccurrence
        (stageAt 0).sourcePrior (stageAt 0).sourceCarrier
        (stageAt 0).actionVisit (criticalActionAppendEntryAt 1)
        (stageAt 0).actionCurrent (stageAt 0).nextCarrier
        (stageAt 0).exactSource ∧
      (stageAt 0).generatedAction.target.targetRoot =
        (stageAt 1).sourceRoot ∧
      (stageAt 0).generatedAction.target.firstSuccessor.targetCurrent =
        (stageAt 1).selectionVisit.current ∧
      (stageAt 0).nextCarrier.action.criticalBearer.bearerLineage.seed =
        (stageAt 0).actionCurrent.root ∧
      (stageAt 0).installedRenewal.selected.selectedEvent =
        (stageAt 0).nextCarrier.event ∧
      (stageAt 0).installedRenewal.payload.consumer.action =
        (stageAt 0).nextCarrier.action ∧
      (stageAt 0).installedRenewal.payload.disposition.update =
        sourceGeneratedEssentialAccessCriticalActualUpdateAt
          (stageAt 0).nextCarrier.event ∧
      IsEmpty (AppendedSelectionReplayAt (stageAt 0).sourceRoot
        (stageAt 0).exactSource.occurrence
        (stageAt 0).actionCurrent (stageAt 0).nextCarrier) ∧
      HEq (recurrenceUBIPayloadAt 0).consumer
        sourceGeneratedUBIRootRestriction :=
  ⟨relationActionRuntimeResumption 0,
    relationActionState_node_exact 0,
    relationSelectionState_node_exact 0,
    (stageAt 0).generatedAction.receipt.down.down.1,
    (stageAt 0).generatedAction.receipt.down.down.2,
    (stageAt 0).generatedAction_targetRoot_exact,
    (stageAt 0).generatedAction_targetCurrent_exact,
    (stageAt 0).actionSeed_eq_currentRoot,
    (relationActionInstalled_exact 0).1,
    (relationActionInstalled_exact 0).2.1,
    (relationActionInstalled_exact 0).2.2,
    (stageAt 0).selectionReplay_isEmpty,
    recurrenceUBIPayloadConsumer_exact 0⟩

theorem finiteQueueExhaustion_relationBootstrapRuns :
    IsEmpty RecurrentQueueCriticalActionSuccessorAt ∧
      SourceNativeInquiryRuntime.SequentialActualActionResumptionAt
        (stageAt 0).generatedAction runtime 7 :=
  ⟨recurrentQueueCriticalActionSuccessor_isEmpty,
    relationActionRuntimeResumption 0⟩

theorem relationActionCurrent_injective :
    Function.Injective (fun depth : Nat => (stageAt depth).actionCurrent) := by
  intro left right equality
  have lengths := congrArg
    (fun current => current.trace.length) equality
  rw [stageAt_actionCurrent_traceLength,
    stageAt_actionCurrent_traceLength] at lengths
  omega

theorem sameRelationSeed_differentGeneratedOccurrence (depth : Nat) :
    (stageAt (depth + 1)).actionCurrent.root =
        (stageAt depth).actionCurrent.root ∧
      (stageAt (depth + 1)).actionCurrent ≠
        (stageAt depth).actionCurrent := by
  constructor
  · rw [stageAt_succ,
      RelationLineageRecurrenceStage.next_actionCurrent_exact]
    change (stageAt depth).nextCarrier.action.criticalBearer.bearerLineage.seed =
      (stageAt depth).actionCurrent.root
    exact (stageAt depth).actionSeed_eq_currentRoot
  · intro equality
    exact Nat.succ_ne_self depth
      (relationActionCurrent_injective equality)

theorem callerEventReplacement_isEmpty
    (depth : Nat) (event : EssentialAccessEvent)
    (different : event ≠ (stageAt depth).actionCurrent.root.1) :
    IsEmpty (CallerSelectedCriticalEventAt
      (stageAt depth).actionCurrent event) :=
  callerSelectedCriticalEvent_isEmpty
    (stageAt depth).actionCurrent event different

theorem twoEventsAtRelationActionOccurrence_isEmpty (depth : Nat) :
    IsEmpty (TwoSelectedCriticalEventsAt
      (stageAt depth).actionCurrent) :=
  twoSelectedCriticalEventsAt_isEmpty (stageAt depth).actionCurrent

end
end M14SourceGeneratedRelationLineageRecurrenceRuntime
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedRelationLineageRecurrenceRuntime.relationActionRuntimeResumption
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedRelationLineageRecurrenceRuntime.relationLineageBootstrapRuntime_directConsumer
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedRelationLineageRecurrenceRuntime.finiteQueueExhaustion_relationBootstrapRuns
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedRelationLineageRecurrenceRuntime.sameRelationSeed_differentGeneratedOccurrence
