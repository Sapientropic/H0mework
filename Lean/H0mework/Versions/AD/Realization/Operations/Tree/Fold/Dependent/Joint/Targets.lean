import H0mework.Versions.AD.Realization.Operations.Tree.Fold.Dependent.Joint.Fibres
import H0mework.Versions.AD.Realization.Operations.Tree.Fold.Dependent.Joint.TargetFaces
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint
open SourceOperationEffects SourceOperationExecution
open RootLawDependentJointStateController RootLawDependentJointTransition RootLawDependentJointPassiveEffect
namespace T
export SourceTemporalMaterial.Action (Result actual receipt nextCode residualRaw materialRoot materialVisit)
end T
namespace D
export SourceOperationNative.Tree.Fold.Dependent (nativeTree nativeRaw nativeReader)
end D
namespace F
export SourceOperationNative.Tree.Fold (Value Var environment program program_value program_budget budget)
end F
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (recognition : RecognitionAt H root)
variable (successor : StepLedgerSuccessorAt (step root visit recognition))
variable (transition : GeneratedStepJointTransitionAt (step root visit recognition) successor)
variable (alignment : RootedAccountedUnfoldingZip.GeneratedZipAt
  (stepSourcePairingOccurrence (step root visit recognition))
  (stepTargetPairingOccurrence (step root visit recognition) successor))
open RootInquiryCompletion SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceGeneratedScalarDifferentialResidual
variable (U7' : U7ProducerCalculus N) (calculus' : U7ObstructionEvolutionCalculus N U7')
namespace TargetTr
export SourceOperationNative.Tree.Fold.Dependent.Joint.Transport (SourceWord TargetWord targetCalculationRuntime)
end TargetTr
abbrev NodeTargets := Σ node : GeneratedNodeAt (step root visit recognition) successor transition.history,
  (sourceWord : TargetTr.SourceWord root visit recognition) →
  (targetWord : TargetTr.TargetWord root visit recognition successor) →
    type_of% (TargetTr.targetCalculationRuntime root visit recognition successor transition node sourceWord targetWord U7' calculus')

def nodeTargets (node : GeneratedNodeAt (step root visit recognition) successor transition.history) :
    NodeTargets root visit recognition successor transition U7' calculus' :=
  ⟨node, fun sourceWord targetWord => TargetTr.targetCalculationRuntime root visit recognition successor transition node sourceWord targetWord U7' calculus'⟩

def TargetsOutputAt (selected : OriginalResult root visit recognition successor transition) : Type (u+15) :=
  match selected with
  | .inl _tree => ULift.{u+15} (RootedAccountedUnfolding (NodeTargets root visit recognition successor transition U7' calculus'))
  | .inr _residual => ULift.{u+15} (ExactResidualAt (step root visit recognition) successor transition.history)

def eliminateTargets (selected : OriginalResult root visit recognition successor transition) :
    TargetsOutputAt root visit recognition successor transition U7' calculus' selected :=
  match selected with
  | .inl tree => ⟨tree.map (nodeTargets root visit recognition successor transition U7' calculus')⟩
  | .inr residual => ⟨residual⟩

abbrev actualTargets (count : Nat) := eliminateTargets root visit recognition successor transition U7' calculus'
  (actualEffect root visit recognition successor transition alignment U7' calculus' count)

theorem targets_tree_preserved (generatedTree : RootedAccountedUnfolding
    (GeneratedNodeAt (step root visit recognition) successor transition.history)) :
    (eliminateTargets root visit recognition successor transition U7' calculus' (.inl generatedTree)).down.map Sigma.fst = generatedTree := by
  change (generatedTree.map (nodeTargets root visit recognition successor transition U7' calculus')).map Sigma.fst = _
  rw [RootedAccountedUnfolding.map_map]
  exact RootedAccountedUnfolding.map_id _

theorem targets_residual_preserved (coordinate : ExactResidualAt (step root visit recognition) successor transition.history) :
    (eliminateTargets root visit recognition successor transition U7' calculus' (.inr coordinate)).down = coordinate := rfl
end SourceOperationNative.Tree.Fold.Dependent.Joint
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
