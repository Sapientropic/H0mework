import H0mework.Versions.V2.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert
open RootInquiryCompletion RootLawDependentJointStateController RootLawDependentJointTransition RootLawDependentJointPassiveEffect
open SourceOperationEffects SourceOperationExecution
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V) (recognition : RecognitionAt H root)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (successor : StepLedgerSuccessorAt (recognition.generateStepAt visit))
variable (transition : GeneratedStepJointTransitionAt (recognition.generateStepAt visit) successor)
variable (alignment : RootedAccountedUnfoldingZip.GeneratedZipAt
  (stepSourcePairingOccurrence (recognition.generateStepAt visit))
  (stepTargetPairingOccurrence (recognition.generateStepAt visit) successor))
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7) (count : Nat)

abbrev complexFeature := SourceGeneratedIntegralCoherentCompletion.complexifiedFeature
  (measurement root recognition visit successor transition alignment U7 calculus count)
abbrev gram := SourceGeneratedComplexFeaturePerfectification.gramEvaluation
  (complexFeature root recognition visit successor transition alignment U7 calculus count)
abbrev perfectification := SourceGeneratedComplexFeaturePerfectification.generate
  (complexFeature root recognition visit successor transition alignment U7 calculus count)
theorem original_gram (left right : Model root recognition visit successor transition alignment U7 calculus count) :
    gram root recognition visit successor transition alignment U7 calculus count
      (1 ⊗ₜ[ℤ] left) (1 ⊗ₜ[ℤ] right) =
      ∑ index : Index root recognition visit successor,
        inner ℂ (Covariance.feature root recognition visit successor transition alignment U7 calculus count
          (actor root recognition visit successor index) left)
          (Covariance.feature root recognition visit successor transition alignment U7 calculus count
            (actor root recognition visit successor index) right) := by
  rw [SourceGeneratedComplexFeaturePerfectification.gramEvaluation_apply]
  simp only [complexFeature,SourceGeneratedIntegralCoherentCompletion.complexifiedFeature_one_tmul,PiLp.inner_apply]
  rfl

end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
