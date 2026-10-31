import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.Relation.Recurrence.SourceGeneratedLineageFoldRelationRecurrenceStage

/-!
# Inquiry presentations for relation-lineage recurrence

Each stage has exactly two active compiler occurrences: its `Fin 1` selection
answer at visit zero and its lineage-fold actual action at retained visit one.
The action target is definitionally the next stage's selection root.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedLineageFoldRelationRecurrencePresentation

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open M14SourceGeneratedCriticalEventSelectionRevisedLedger
open M14SourceGeneratedCriticalEventSelectionRevisedRoot
open M14SourceGeneratedCriticalEventSelectionRevisedInquiry
open M14SourceGeneratedEssentialAccessCriticalActionAppendLedger
open M14SourceGeneratedEssentialAccessCriticalActionAppendRoot
open M14SourceGeneratedCriticalActionAppendContinuation
open M14SourceGeneratedLineageFoldRelationRecurrenceStage

def actionInquiryState (stage : RelationLineageRecurrenceStage) :
    RootInquiryStateAt NewN
      (AppendVAt stage.sourcePrior stage.sourceCarrier) where
  root := stage.sourceRoot
  visit := stage.actionVisit
  U7 := revisedInquiryU7
  calculus := revisedInquiryCalculus
  Query := Unit
  entryAt := fun _ => criticalActionAppendEntryAt 1
  authorityAt := fun _ => criticalActionAppendAuthorityAt
    stage.predecessorRoot stage.predecessorOccurrence stage.sourcePrior
      stage.sourceCarrier 1
  compilationProgramAt := fun _ =>
    { compile := fun _ => stage.actualActionCompilation }
  compilationFaceAt := fun _ =>
    { projection := .inquiry
      active := PUnit.unit
      classifier_eq := rfl
      project_heq := HEq.rfl }
  u7RootDisposition_commutes := by
    intro _query _obstruction _audit audit_eq
    cases audit_eq

def actionEngineState (stage : RelationLineageRecurrenceStage) :
    RootInquiryEngineStateAt NewN
      (AppendVAt stage.sourcePrior stage.sourceCarrier) :=
  RootInquiryEngineStateAt.create (actionInquiryState stage)

def actionPresentation (stage : RelationLineageRecurrenceStage) :
    RootInquiryStatePresentation where
  N := NewN
  V := AppendVAt stage.sourcePrior stage.sourceCarrier
  state := actionEngineState stage

@[simp] theorem actionPresentation_current_exact
    (stage : RelationLineageRecurrenceStage) :
    (actionPresentation stage).state.base.visit.current =
      stage.actionCurrent := by
  change stage.actionVisit.current = stage.actionCurrent
  rfl

@[simp] theorem actionPresentation_compilation_exact
    (stage : RelationLineageRecurrenceStage) :
    (actionInquiryState stage).compileInquiry () =
      .actualAction stage.generatedAction :=
  rfl

set_option linter.defProp false in
def selectionToActionSuccessorValid
    (stage : RelationLineageRecurrenceStage) :=
  RootInquiryProcessNode.active_directlyAnswered_successor_valid
    stage.selectionPresentation (actionPresentation stage) ()
    stage.selectionAnswerFace stage.selectionAnswerConsumer
    rfl rfl (by
      change HEq stage.sourceRoot stage.sourceRoot
      exact HEq.rfl)

set_option linter.defProp false in
def actionToNextSelectionSuccessorValid
    (stage : RelationLineageRecurrenceStage) :=
  RootInquiryProcessNode.active_actualAction_successor_valid
    (actionPresentation stage) stage.next.selectionPresentation ()
    stage.generatedAction rfl rfl HEq.rfl

theorem recurrencePresentation_directConsumer
    (stage : RelationLineageRecurrenceStage) :
    (actionInquiryState stage).root = stage.sourceRoot ∧
      (actionInquiryState stage).visit = stage.actionVisit ∧
      (actionInquiryState stage).compileInquiry () =
        .actualAction stage.generatedAction ∧
      stage.generatedAction.target.targetRoot = stage.next.sourceRoot :=
  ⟨rfl, rfl, rfl, stage.generatedAction_targetRoot_exact⟩

end
end M14SourceGeneratedLineageFoldRelationRecurrencePresentation
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedLineageFoldRelationRecurrencePresentation.actionPresentation_compilation_exact
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedLineageFoldRelationRecurrencePresentation.actionToNextSelectionSuccessorValid
