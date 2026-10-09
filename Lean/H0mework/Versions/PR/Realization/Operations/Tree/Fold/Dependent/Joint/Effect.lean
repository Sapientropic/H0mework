import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Joint.CalculationConsumer
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
export SourceOperationNative.Tree.Fold.Dependent.Joint.Transport (sourceResidual targetResidual GeneratedUpdate generateUpdate sourceCouplingTrace targetCouplingTrace source_cost target_cost coupling_square)
end Tr
abbrev actualEffect (count : Nat) :=
  ((face root visit recognition successor transition alignment U7' calculus' count).rootRead.1.fold
    (constructor root visit recognition successor transition)).1

theorem actual_effect_original (count : Nat) : actualEffect root visit recognition successor transition alignment U7' calculus' count =
    (D.nativeTree (step root visit recognition) successor transition alignment).fold
      (effectFoldAt (step root visit recognition) successor transition.history) :=
  original_effect root visit recognition successor transition alignment

abbrev NodeEffect := Σ node : GeneratedNodeAt (step root visit recognition) successor transition.history,
  (value : (StepSourceHistory (step root visit recognition)).CompletionCarrier) →
    (Tr.GeneratedUpdate root visit recognition successor transition node value ×
      (type_of% (Tr.sourceCouplingTrace root visit recognition successor transition node value)) ×
      (type_of% (Tr.targetCouplingTrace root visit recognition successor transition node value)))

def nodeEffect (node : GeneratedNodeAt (step root visit recognition) successor transition.history) :
    NodeEffect root visit recognition successor transition :=
  ⟨node, fun value => ⟨Tr.generateUpdate root visit recognition successor transition node value,
    Tr.sourceCouplingTrace root visit recognition successor transition node value,
    Tr.targetCouplingTrace root visit recognition successor transition node value⟩⟩

def EffectOutputAt (selected : OriginalResult root visit recognition successor transition) : Type u :=
  match selected with
  | .inl _tree => RootedAccountedUnfolding (NodeEffect root visit recognition successor transition)
  | .inr _residual => ExactResidualAt (step root visit recognition) successor transition.history

def eliminateEffect (selected : OriginalResult root visit recognition successor transition) :
    EffectOutputAt root visit recognition successor transition selected :=
  match selected with
  | .inl tree => tree.map (nodeEffect root visit recognition successor transition)
  | .inr residual => residual

abbrev effectOutput (count : Nat) := eliminateEffect root visit recognition successor transition
  (actualEffect root visit recognition successor transition alignment U7' calculus' count)

theorem effect_tree_preserved (generatedTree : RootedAccountedUnfolding
    (GeneratedNodeAt (step root visit recognition) successor transition.history)) :
    (eliminateEffect root visit recognition successor transition (.inl generatedTree)).map Sigma.fst = generatedTree := by
  change (generatedTree.map (nodeEffect root visit recognition successor transition)).map Sigma.fst = _
  rw [RootedAccountedUnfolding.map_map]
  exact RootedAccountedUnfolding.map_id _

theorem effect_residual_preserved (coordinate : ExactResidualAt (step root visit recognition) successor transition.history) :
    eliminateEffect root visit recognition successor transition (.inr coordinate) = coordinate := rfl

abbrev NodeRuntime := Σ node : GeneratedNodeAt (step root visit recognition) successor transition.history,
  (value : (StepSourceHistory (step root visit recognition)).CompletionCarrier) →
    type_of% (Transport.pairedRuntime root visit recognition successor transition node value U7' calculus')

def nodeRuntime (node : GeneratedNodeAt (step root visit recognition) successor transition.history) :
    NodeRuntime root visit recognition successor transition U7' calculus' :=
  ⟨node, fun value => Transport.pairedRuntime root visit recognition successor transition node value U7' calculus'⟩

def RuntimeOutputAt (selected : OriginalResult root visit recognition successor transition) : Type (u+15) :=
  match selected with
  | .inl _tree => ULift.{u+15} (RootedAccountedUnfolding (NodeRuntime root visit recognition successor transition U7' calculus'))
  | .inr _residual => ULift.{u+15} (ExactResidualAt (step root visit recognition) successor transition.history)

def eliminateRuntime (selected : OriginalResult root visit recognition successor transition) :
    RuntimeOutputAt root visit recognition successor transition U7' calculus' selected :=
  match selected with
  | .inl tree => ⟨tree.map (nodeRuntime root visit recognition successor transition U7' calculus')⟩
  | .inr residual => ⟨residual⟩

abbrev actualEffectRuntime (count : Nat) := eliminateRuntime root visit recognition successor transition U7' calculus'
  (actualEffect root visit recognition successor transition alignment U7' calculus' count)

end SourceOperationNative.Tree.Fold.Dependent.Joint
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
