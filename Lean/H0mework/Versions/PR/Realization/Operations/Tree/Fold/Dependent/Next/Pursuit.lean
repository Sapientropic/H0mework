import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Next.Material
import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.Relation.Complete
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Next.Pursuit
open RootLawDependentJointStateController RootLawDependentJointTransition RootLawDependentJointPassiveEffect
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (recognition : RecognitionAt H root)
variable (successor : StepLedgerSuccessorAt (recognition.generateStepAt visit))
abbrev nextVisit := Material.nextVisit root visit recognition successor
abbrev nextStep := recognition.generateStepAt (nextVisit root visit recognition successor)
namespace Tr
export SourceOperationNative.Tree.Fold.Dependent.Joint.Transport (TargetWord SourceWord targetCalculationRuntime)
end Tr
namespace J
export SourceOperationNative.Tree.Fold.Dependent.Joint (OriginalResult actualEffect)
end J
variable (oldWord : Tr.TargetWord root visit recognition successor)
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7)
variable (nextSuccessor : StepLedgerSuccessorAt (nextStep root visit recognition successor))
variable (transition : GeneratedStepJointTransitionAt (nextStep root visit recognition successor) nextSuccessor)
variable (alignment : RootedAccountedUnfoldingZip.GeneratedZipAt
  (stepSourcePairingOccurrence (nextStep root visit recognition successor))
  (stepTargetPairingOccurrence (nextStep root visit recognition successor) nextSuccessor))

abbrev NodeFollow := Σ node : GeneratedNodeAt (nextStep root visit recognition successor) nextSuccessor transition.history,
  (targetWord : Tr.TargetWord root (nextVisit root visit recognition successor) recognition nextSuccessor) →
    type_of% (Tr.targetCalculationRuntime root (nextVisit root visit recognition successor) recognition nextSuccessor transition node
      (Material.generatedNextWord root visit recognition successor oldWord) targetWord U7 calculus)

def nodeFollow (node : GeneratedNodeAt (nextStep root visit recognition successor) nextSuccessor transition.history) :
    NodeFollow root visit recognition successor oldWord U7 calculus nextSuccessor transition :=
  ⟨node, fun targetWord => Tr.targetCalculationRuntime root (nextVisit root visit recognition successor) recognition nextSuccessor transition node
    (Material.generatedNextWord root visit recognition successor oldWord) targetWord U7 calculus⟩

def OutputAt (selected : J.OriginalResult root (nextVisit root visit recognition successor) recognition nextSuccessor transition) : Type (u+15) :=
  match selected with
  | .inl _tree => ULift.{u+15} (RootedAccountedUnfolding (NodeFollow root visit recognition successor oldWord U7 calculus nextSuccessor transition))
  | .inr _residual => ULift.{u+15} (ExactResidualAt (nextStep root visit recognition successor) nextSuccessor transition.history)

def eliminate (selected : J.OriginalResult root (nextVisit root visit recognition successor) recognition nextSuccessor transition) :
    OutputAt root visit recognition successor oldWord U7 calculus nextSuccessor transition selected :=
  match selected with
  | .inl tree => ⟨tree.map (nodeFollow root visit recognition successor oldWord U7 calculus nextSuccessor transition)⟩
  | .inr residual => ⟨residual⟩

abbrev actual := eliminate root visit recognition successor oldWord U7 calculus nextSuccessor transition
  (J.actualEffect root (nextVisit root visit recognition successor) recognition nextSuccessor transition alignment U7 calculus 0)

abbrev selected := settlePassiveEffect (nextStep root visit recognition successor)
def RunAt (phase : PassiveEffectDispositionAt (nextStep root visit recognition successor)) : Type (u+15) :=
  match phase with
  | .allGenerated next _ carry => OutputAt root visit recognition successor oldWord U7 calculus next carry.historyTransition
      (J.actualEffect root (nextVisit root visit recognition successor) recognition next carry.historyTransition carry.pairingAlignment U7 calculus 0)
  | .jointResidual next _ transition alignment _ _ _ => OutputAt root visit recognition successor oldWord U7 calculus next transition
      (J.actualEffect root (nextVisit root visit recognition successor) recognition next transition alignment U7 calculus 0)
  | other => ULift.{u+15} (Tr.SourceWord root (nextVisit root visit recognition successor) recognition ×
      SourceOperationNative.Tree.Fold.Dependent.FeedAt (nextStep root visit recognition successor) other ×
      type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.Relation.completeRuntime root (nextVisit root visit recognition successor) recognition U7 calculus))

def generated : RunAt root visit recognition successor oldWord U7 calculus (selected root visit recognition successor) := by
  generalize selected_eq : selected root visit recognition successor = phase
  cases phase with
  | allGenerated next _ carry => exact actual root visit recognition successor oldWord U7 calculus next carry.historyTransition carry.pairingAlignment
  | jointResidual next _ transition alignment _ _ _ => exact actual root visit recognition successor oldWord U7 calculus next transition alignment
  | terminal eq => exact ⟨Material.generatedNextWord root visit recognition successor oldWord,
      root.toAuthoritativeRoot.toLedgerRoot.source.ledgerCompiler.compile (nextStep root visit recognition successor).sourceOccurrence,
      SourceOperationNative.Tree.Fold.Dependent.Branch.Relation.completeRuntime root (nextVisit root visit recognition successor) recognition U7 calculus⟩
  | generatorResidual next eq residual => exact ⟨Material.generatedNextWord root visit recognition successor oldWord,residual,
      SourceOperationNative.Tree.Fold.Dependent.Branch.Relation.completeRuntime root (nextVisit root visit recognition successor) recognition U7 calculus⟩
  | relationResidual next eq compatible residual => exact ⟨Material.generatedNextWord root visit recognition successor oldWord,residual,
      SourceOperationNative.Tree.Fold.Dependent.Branch.Relation.completeRuntime root (nextVisit root visit recognition successor) recognition U7 calculus⟩
  | pairingShapeResidual next eq transition residual => exact ⟨Material.generatedNextWord root visit recognition successor oldWord,residual,
      SourceOperationNative.Tree.Fold.Dependent.Branch.Relation.completeRuntime root (nextVisit root visit recognition successor) recognition U7 calculus⟩
end SourceOperationNative.Tree.Fold.Dependent.Next.Pursuit
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
