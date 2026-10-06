import H0mework.Versions.AD.Realization.Operations.Tree.Fold.Dependent.Branch.Rich
import H0mework.Versions.AD.Realization.Operations.Tree.Fold.Dependent.Branch.Maps
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.Side
open RootLawDependentJointStateController RootLawDependentJointTransition RootLawDependentJointPassiveEffect
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V) (recognition : RecognitionAt H root)
variable (code : SourceTemporalMaterial.Code root.toAuthoritativeRoot.toLedgerRoot)
variable (successor : StepLedgerSuccessorAt (step root recognition code))
variable (word : SourceHistoryCommon.Root.G root recognition →₀ ℤ)

theorem generated_source_word :
    (wordEvaluation root recognition code (some successor) (generateAt root recognition code (some successor)) word).down.down.1 =
      (SourceHistoryCommon.Root.Evaluator.sourceFace root (visit root code) recognition).freeEvaluation word :=
  source_word root recognition code successor word

theorem generated_target_word :
    (wordEvaluation root recognition code (some successor) (generateAt root recognition code (some successor)) word).down.down.2 =
      (SourceHistoryCommon.Root.Evaluator.targetFace root (visit root code) recognition successor).freeEvaluation word :=
  target_word root recognition code successor word

theorem source_map_fibre (datum : (StepSourceHistory (step root recognition code)).generatorClosure) :
    (mapsAt root recognition code (some successor)).down.1
      ((StepSourceHistory (step root recognition code)).completionProjection datum) = 0 ↔
        datum.val ∈ (commonRead root recognition code successor).relationClosure :=
  source_fibre root recognition code successor datum

theorem target_map_fibre (datum : (StepTargetHistory (step root recognition code) successor).generatorClosure) :
    (mapsAt root recognition code (some successor)).down.2
      ((StepTargetHistory (step root recognition code) successor).completionProjection datum) = 0 ↔
        datum.val ∈ (commonRead root recognition code successor).relationClosure :=
  target_fibre root recognition code successor datum
end SourceOperationNative.Tree.Fold.Dependent.Branch.Side
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
