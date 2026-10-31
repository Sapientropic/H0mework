import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.CrossCompiler.Action.SourceGeneratedSequentialCrossCompilerRelationAppend
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.Relation.Recurrence.SourceGeneratedLineageFoldRelationRecurrencePresentation

/-!
# Inquiry presentations for cross-compiler relation recurrence

The homogeneous tail cuts over after stage-zero relation selection.  Each
heterogeneous stage then has one actual-action occurrence and one distinct
`Fin 1` target selection.  The three process edges are kernel-certified; no
same-current answered sibling or parallel compiler is installed.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedCrossCompilerRelationAppendPresentation

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open M14SourceGeneratedCriticalEventSelectionRevisedLedger
open M14SourceGeneratedCriticalEventSelectionRevisedInquiry
open M14SourceGeneratedEssentialAccessCriticalActionAppendRoot
open M14SourceGeneratedLineageFoldRelationRecurrenceStage
open M14SourceGeneratedLineageFoldRelationRecurrencePresentation
open M14SourceGeneratedRootedAccountedUnfoldingAppendRoot
open M14SourceGeneratedRootedAccountedUnfoldingAppendContinuation
open M14SourceGeneratedCrossCompilerRelationAppendStage
open M14SourceGeneratedCrossCompilerRelationAppendStage.CrossCompilerRelationAppendStageAt
open M14SourceGeneratedSequentialCrossCompilerRelationAppend

def crossCompilerActionInquiryStateAt (depth : Nat) :
    RootInquiryStateAt NewN (appendStageAt depth).SourceV where
  root := (appendStageAt depth).sourceRoot
  visit := (appendStageAt depth).sourceVisit
  U7 := revisedInquiryU7
  calculus := revisedInquiryCalculus
  Query := Unit
  entryAt := fun _ => (appendStageAt depth).sourceEntry
  authorityAt := fun _ => (appendStageAt depth).sourceAuthority
  compilationProgramAt := fun _ =>
    crossCompilerRelationAppendCompilationProgramAt depth
  compilationFaceAt := fun _ => by
    cases depth with
    | zero =>
        exact
          { projection := AppendProjection.inquiry
            active := PUnit.unit
            classifier_eq := rfl
            project_heq := HEq.rfl }
    | succ priorDepth =>
        exact
          { projection := RootedAppendProjection.inquiry
            active := PUnit.unit
            classifier_eq := rfl
            project_heq := HEq.rfl }
  u7RootDisposition_commutes := by
    intro _query _obstruction _audit audit_eq
    cases audit_eq

def crossCompilerActionEngineStateAt (depth : Nat) :
    RootInquiryEngineStateAt NewN (appendStageAt depth).SourceV :=
  RootInquiryEngineStateAt.create (crossCompilerActionInquiryStateAt depth)

def crossCompilerActionPresentationAt (depth : Nat) :
    RootInquiryStatePresentation where
  N := NewN
  V := (appendStageAt depth).SourceV
  state := crossCompilerActionEngineStateAt depth

def crossCompilerSelectionPresentationAt (depth : Nat) :
    RootInquiryStatePresentation :=
  rootedAppendPresentationAt (appendStageAt depth).sourceRoot
    (appendStageAt depth).exactSource.occurrence
    (appendStageAt depth).targetPrior (appendStageAt depth).targetAtom
    (0 : Fin 1)

def crossCompilerSelectionAnswerFaceAt (depth : Nat) :=
  rootedAppendAnswerFaceAt (appendStageAt depth).sourceRoot
    (appendStageAt depth).exactSource.occurrence
    (appendStageAt depth).targetPrior (appendStageAt depth).targetAtom
    (0 : Fin 1)

def crossCompilerSelectionAnswerConsumerAt (depth : Nat) :=
  rootedAppendAnswerConsumerAt (appendStageAt depth).sourceRoot
    (appendStageAt depth).exactSource.occurrence
    (appendStageAt depth).targetPrior (appendStageAt depth).targetAtom
    (0 : Fin 1)

@[simp] theorem crossCompilerActionPresentation_compilation_exact
    (depth : Nat) :
    (crossCompilerActionInquiryStateAt depth).compileInquiry () =
      .actualAction (generatedCrossCompilerRelationAppendActionAt depth) :=
  rfl

@[simp] theorem crossCompilerActionPresentation_current_exact
    (depth : Nat) :
    HEq (crossCompilerActionPresentationAt depth).state.base.visit.current
      (M14SourceGeneratedCrossCompilerRelationCurrentRecurrence.crossCompilerCurrentStageAt
        depth).actionCurrent :=
  (appendStageAt depth).sourceCurrentExact

set_option linter.defProp false in
def homogeneousSelectionToFirstCrossActionSuccessorValid :=
  RootInquiryProcessNode.active_directlyAnswered_successor_valid
    (stageAt 1).selectionPresentation
    (crossCompilerActionPresentationAt 0) ()
    (stageAt 1).selectionAnswerFace (stageAt 1).selectionAnswerConsumer
    rfl rfl (by
      change HEq (stageAt 1).sourceRoot (appendStageAt 0).sourceRoot
      exact HEq.rfl)

set_option linter.defProp false in
def crossActionToSelectionSuccessorValid (depth : Nat) :=
  RootInquiryProcessNode.active_actualAction_successor_valid
    (crossCompilerActionPresentationAt depth)
    (crossCompilerSelectionPresentationAt depth) ()
    (generatedCrossCompilerRelationAppendActionAt depth)
    (crossCompilerActionPresentation_compilation_exact depth) rfl HEq.rfl

set_option linter.defProp false in
def crossSelectionToNextActionSuccessorValid (depth : Nat) :=
  RootInquiryProcessNode.active_directlyAnswered_successor_valid
    (crossCompilerSelectionPresentationAt depth)
    (crossCompilerActionPresentationAt (depth + 1)) ()
    (crossCompilerSelectionAnswerFaceAt depth)
    (crossCompilerSelectionAnswerConsumerAt depth)
    rfl rfl (by
      change HEq (appendStageAt depth).targetRoot
        (appendStageAt (depth + 1)).sourceRoot
      exact HEq.rfl)

theorem crossCompilerPresentation_directConsumer (depth : Nat) :
    (crossCompilerActionInquiryStateAt depth).root =
        (appendStageAt depth).sourceRoot ∧
      (crossCompilerActionInquiryStateAt depth).visit =
        (appendStageAt depth).sourceVisit ∧
      (crossCompilerActionInquiryStateAt depth).compileInquiry () =
        .actualAction (generatedCrossCompilerRelationAppendActionAt depth) ∧
      (generatedCrossCompilerRelationAppendActionAt depth
        ).target.targetRoot = (appendStageAt depth).targetRoot ∧
      HEq (crossCompilerSelectionPresentationAt depth).state.base.visit.current
        (M14SourceGeneratedCrossCompilerRelationCurrentRecurrence.crossCompilerCurrentStageAt
          depth).targetCurrent :=
  ⟨rfl, rfl, crossCompilerActionPresentation_compilation_exact depth, rfl,
    (appendStageAt depth).selectionCurrent_exact⟩

end
end M14SourceGeneratedCrossCompilerRelationAppendPresentation
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCrossCompilerRelationAppendPresentation.crossCompilerActionPresentation_compilation_exact
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCrossCompilerRelationAppendPresentation.homogeneousSelectionToFirstCrossActionSuccessorValid
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCrossCompilerRelationAppendPresentation.crossActionToSelectionSuccessorValid
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCrossCompilerRelationAppendPresentation.crossSelectionToNextActionSuccessorValid
