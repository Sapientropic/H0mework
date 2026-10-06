import H0mework.Versions.AD.Realization.Operations.Tree.Fold.Dependent.Joint.Effect
import H0mework.Versions.AD.Realization.Operations.Tree.Fold.Dependent.Joint.Fibre
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
namespace Tr
export SourceOperationNative.Tree.Fold.Dependent.Joint.Transport (sourceDifferential targetDifferential residualMorphism residualFibreMap residualLift)
end Tr
abbrev NodeFibre := Σ node : GeneratedNodeAt (step root visit recognition) successor transition.history,
  SourceGeneratedScalarDifferentialResidual.Morphism
    (Tr.sourceDifferential root visit recognition successor transition node)
    (Tr.targetDifferential root visit recognition successor transition node)
def nodeFibre (node : GeneratedNodeAt (step root visit recognition) successor transition.history) :
    NodeFibre root visit recognition successor transition :=
  ⟨node,Tr.residualMorphism root visit recognition successor transition node⟩

def FibreOutputAt (selected : OriginalResult root visit recognition successor transition) : Type u :=
  match selected with
  | .inl _tree => RootedAccountedUnfolding (NodeFibre root visit recognition successor transition)
  | .inr _residual => ExactResidualAt (step root visit recognition) successor transition.history

def eliminateFibres (selected : OriginalResult root visit recognition successor transition) :
    FibreOutputAt root visit recognition successor transition selected :=
  match selected with
  | .inl tree => tree.map (nodeFibre root visit recognition successor transition)
  | .inr residual => residual

abbrev actualFibres (count : Nat) := eliminateFibres root visit recognition successor transition
  (actualEffect root visit recognition successor transition alignment U7' calculus' count)

theorem fibre_tree_preserved (generatedTree : RootedAccountedUnfolding
    (GeneratedNodeAt (step root visit recognition) successor transition.history)) :
    (eliminateFibres root visit recognition successor transition (.inl generatedTree)).map Sigma.fst = generatedTree := by
  change (generatedTree.map (nodeFibre root visit recognition successor transition)).map Sigma.fst = _
  rw [RootedAccountedUnfolding.map_map]
  exact RootedAccountedUnfolding.map_id _

theorem fibre_residual_preserved (coordinate : ExactResidualAt (step root visit recognition) successor transition.history) :
    eliminateFibres root visit recognition successor transition (.inr coordinate) = coordinate := rfl
end SourceOperationNative.Tree.Fold.Dependent.Joint
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
