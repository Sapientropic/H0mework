import H0mework.Versions.AE.Realization.Operations.Tree.Fold.Dependent.Branch.Complete
import H0mework.Versions.AE.Realization.Perfectification.Occurrence.Temporal.History.Common.Evaluator.Consumer
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.Side
open RootLawDependentJointStateController RootLawDependentJointTransition RootLawDependentJointPassiveEffect
open CofinalHistoryTransition
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V) (recognition : RecognitionAt H root)
variable (code : SourceTemporalMaterial.Code root.toAuthoritativeRoot.toLedgerRoot)
variable (successor : StepLedgerSuccessorAt (step root recognition code))
abbrev left := SourceHistoryCommon.Root.left root (visit root code) recognition successor
abbrev right := SourceHistoryCommon.Root.right root (visit root code) recognition successor

theorem source_fibre (word : (StepSourceHistory (step root recognition code)).generatorClosure) :
    GeneratedTransition.completionMap (StepSourceHistory (step root recognition code)) (commonRead root recognition code successor)
      (left root recognition code successor) ((StepSourceHistory (step root recognition code)).completionProjection word) = 0 ↔
      word.val ∈ (commonRead root recognition code successor).relationClosure :=
  SourceHistoryCommon.transition_fibre_zero _ _ _ word

theorem target_fibre (word : (StepTargetHistory (step root recognition code) successor).generatorClosure) :
    GeneratedTransition.completionMap (StepTargetHistory (step root recognition code) successor) (commonRead root recognition code successor)
      (right root recognition code successor) ((StepTargetHistory (step root recognition code) successor).completionProjection word) = 0 ↔
      word.val ∈ (commonRead root recognition code successor).relationClosure :=
  SourceHistoryCommon.transition_fibre_zero _ _ _ word

theorem source_word (word : SourceHistoryCommon.Root.G root recognition →₀ ℤ) :
    ((evaluationFace root recognition code successor).freeEvaluation word).down.1 =
      (SourceHistoryCommon.Root.Evaluator.sourceFace root (visit root code) recognition).freeEvaluation word :=
  SourceHistoryCommon.Root.Evaluator.source_word root (visit root code) recognition successor word

theorem target_word (word : SourceHistoryCommon.Root.G root recognition →₀ ℤ) :
    ((evaluationFace root recognition code successor).freeEvaluation word).down.2 =
      (SourceHistoryCommon.Root.Evaluator.targetFace root (visit root code) recognition successor).freeEvaluation word :=
  SourceHistoryCommon.Root.Evaluator.target_word root (visit root code) recognition successor word

abbrev inverseOutput := SourceHistoryCommon.Root.Evaluator.generatedOutput root (visit root code) recognition successor
end SourceOperationNative.Tree.Fold.Dependent.Branch.Side
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
