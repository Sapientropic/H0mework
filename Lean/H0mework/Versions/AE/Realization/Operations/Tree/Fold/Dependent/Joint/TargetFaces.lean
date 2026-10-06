import H0mework.Versions.AE.Realization.Operations.Tree.Fold.Dependent.Joint.TargetConsumer
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.Transport
open RootLawDependentJointStateController RootLawDependentJointTransition RootLawDependentJointPassiveEffect
open SourceOperationEffects SourceOperationExecution
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (recognition : RecognitionAt H root)
variable (successor : StepLedgerSuccessorAt (recognition.generateStepAt visit))
variable (transition : GeneratedStepJointTransitionAt (recognition.generateStepAt visit) successor)
variable (node : GeneratedNodeAt (recognition.generateStepAt visit) successor transition.history)
variable (sourceWord : SourceWord root visit recognition) (targetWord : TargetWord root visit recognition successor)
open RootInquiryCompletion
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7)
def targetMaterialFace (count : Nat) : SourceNativeRootSemanticFaceAt
    (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.root
      (targetCalculationRoot root visit recognition successor transition node sourceWord targetWord) visit U7 calculus
      (targetCalculationReader root visit recognition successor transition node sourceWord targetWord) count)
    (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.visit
      (targetCalculationRoot root visit recognition successor transition node sourceWord targetWord) visit
      (targetCalculationReader root visit recognition successor transition node sourceWord targetWord) count) where
  projection := .inherited (.inherited (.inherited
    ((RootGeneratedDebtActivationJointSource.OwnerFree.baseInstallation
      (targetCalculationRoot root visit recognition successor transition node sourceWord targetWord).toAuthoritativeRoot
      visit.current (targetCalculationReader root visit recognition successor transition node sourceWord targetWord)).embed
      (.inl (.inherited (.component PUnit.unit))))))
  active := PUnit.unit
  classifier_eq := rfl

theorem target_node_read (count : Nat) : (targetMaterialFace root visit recognition successor transition node sourceWord targetWord U7 calculus count).rootRead.1 = node := rfl

theorem target_source_word_read (count : Nat) : (targetMaterialFace root visit recognition successor transition node sourceWord targetWord U7 calculus count).rootRead.2.1 = sourceWord := rfl

theorem target_target_word_read (count : Nat) : (targetMaterialFace root visit recognition successor transition node sourceWord targetWord U7 calculus count).rootRead.2.2.1 = targetWord := rfl

theorem target_parent_next (count : Nat) : type_of%
    (SourceTemporalMaterial.Calculation.parent_next_preserved
      (targetSourceRoot root visit recognition successor transition node sourceWord targetWord) visit U7 calculus
      (targetCalculationReader root visit recognition successor transition node sourceWord targetWord) count) :=
  SourceTemporalMaterial.Calculation.parent_next_preserved
    (targetSourceRoot root visit recognition successor transition node sourceWord targetWord) visit U7 calculus
    (targetCalculationReader root visit recognition successor transition node sourceWord targetWord) count
end SourceOperationNative.Tree.Fold.Dependent.Joint.Transport
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
