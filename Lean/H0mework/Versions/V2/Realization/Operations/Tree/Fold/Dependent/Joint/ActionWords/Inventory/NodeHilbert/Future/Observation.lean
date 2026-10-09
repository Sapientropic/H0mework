import H0mework.Versions.V2.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future
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

abbrev Cells (bound : Nat) := Code root recognition visit successor bound × Index root recognition visit successor
abbrev Space (bound : Nat) := PiLp 2 (fun _ : Cells root recognition visit successor bound => H)
def observation (bound : Nat) : Model root recognition visit successor transition alignment U7 calculus count →ₗ[ℤ] Space root recognition visit successor bound :=
  (WithLp.linearEquiv 2 ℤ (Cells root recognition visit successor bound → H)).symm.toLinearMap.comp
    (LinearMap.pi (fun cell => (Covariance.feature root recognition visit successor transition alignment U7 calculus count
      (actor root recognition visit successor cell.2)).comp
      (SourceGeneratedActionWords.run (advance root recognition visit successor transition alignment U7 calculus count)
        (word root recognition visit successor cell.1))))
theorem cell_read (bound : Nat) (cell : Cells root recognition visit successor bound)
    (value : Model root recognition visit successor transition alignment U7 calculus count) :
    observation root recognition visit successor transition alignment U7 calculus count bound value cell =
      Covariance.feature root recognition visit successor transition alignment U7 calculus count (actor root recognition visit successor cell.2)
        (SourceGeneratedActionWords.run (advance root recognition visit successor transition alignment U7 calculus count)
          (word root recognition visit successor cell.1) value) := rfl
def restriction (bound : Nat) : Space root recognition visit successor (bound+1) →ₗ[ℤ] Space root recognition visit successor bound :=
  (WithLp.linearEquiv 2 ℤ (Cells root recognition visit successor bound → H)).symm.toLinearMap.comp
    ((LinearMap.pi (fun cell => LinearMap.proj (lengthRestriction root recognition visit successor bound cell.1,cell.2))).comp
      (WithLp.linearEquiv 2 ℤ (Cells root recognition visit successor (bound+1) → H)).toLinearMap)
theorem observation_restriction (bound : Nat) :
    (restriction root recognition visit successor bound).comp
      (observation root recognition visit successor transition alignment U7 calculus count (bound+1))=
    observation root recognition visit successor transition alignment U7 calculus count bound := rfl

abbrev data : SourceGeneratedScalarCofinalKernelCompletion.Data (R:=ℤ)
    (Generator:=Model root recognition visit successor transition alignment U7 calculus count)
    (Carrier:=Space root recognition visit successor) where
  evaluator := observation root recognition visit successor transition alignment U7 calculus count
  transition := restriction root recognition visit successor

theorem compatible : (data root recognition visit successor transition alignment U7 calculus count).Compatible :=
  observation_restriction root recognition visit successor transition alignment U7 calculus count
abbrev whole := (data root recognition visit successor transition alignment U7 calculus count).Completion
  (compatible root recognition visit successor transition alignment U7 calculus count)
abbrev sourceMap := ((data root recognition visit successor transition alignment U7 calculus count).completionMap
  (compatible root recognition visit successor transition alignment U7 calculus count)).hom

abbrev complexFeature (bound : Nat) := SourceGeneratedIntegralCoherentCompletion.complexifiedFeature
  (observation root recognition visit successor transition alignment U7 calculus count bound)
abbrev gram (bound : Nat) := SourceGeneratedComplexFeaturePerfectification.gramEvaluation
  (complexFeature root recognition visit successor transition alignment U7 calculus count bound)
abbrev perfectification (bound : Nat) := SourceGeneratedComplexFeaturePerfectification.generate
  (complexFeature root recognition visit successor transition alignment U7 calculus count bound)

end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
