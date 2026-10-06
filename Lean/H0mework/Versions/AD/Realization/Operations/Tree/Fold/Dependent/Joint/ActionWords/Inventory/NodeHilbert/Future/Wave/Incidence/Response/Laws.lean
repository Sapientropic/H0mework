import H0mework.Versions.AD.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.Incidence.Response.Source
import H0mework.Versions.AD.Realization.Operations.Inquiry.Context.Native.Orbit.Installation.Activation.Observation.Consumer
import Lean.LibrarySuggestions.Basic
-- Exclude only complete next-inventory runtime signatures from suggestion export.
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PaidSourceMacroResponse"
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceMacroResponse
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


variable (point : Carrier root recognition visit successor) (seedWord : List (Letter root recognition visit successor))
variable (bound : Nat) (queryWord : List (Letter root recognition visit successor)) (letter : Letter root recognition visit successor)
theorem whole_recover (word : Word) : (decomposition root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter).symm
 (retained root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word)=word :=
 (decomposition root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter).symm_apply_apply word

theorem projection_fibre (left right : Word) : projection root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter left=projection root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter right ↔
    ∀ (following : List PUnit.{u+1}) (cut : Nat),
      observe root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter (SourceGeneratedActionWords.run actions following left) cut=
        observe root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter (SourceGeneratedActionWords.run actions following right) cut := by
 rw [SourceGeneratedActionWords.projection_fibre]
 constructor
 · intro same following cut; exact congrFun (same following) cut
 · intro same following; funext cut; exact same following cut
end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceMacroResponse
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
