import H0mework.Realization.JointState.ActionOrbit
import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.Consumer
import Lean.LibrarySuggestions.Basic
-- Runtime mouths unfold complete root-indexed carriers in automatic suggestion indexing.
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PaidSourceOrbit"
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceOrbit
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

variable (bound : Nat) (letters : List (Letter root recognition visit successor))
def input : SourceGeneratedIntegralCoherentJointAction.Input
    (Model root recognition visit successor transition alignment U7 calculus count) (Space root recognition visit successor bound)
    (CoarseModel root recognition visit successor transition alignment U7 calculus count) where
  integralAction := SourceGeneratedActionWords.run (advance root recognition visit successor transition alignment U7 calculus count) letters
  coherentAction := (wordEvolution root recognition visit successor bound letters).toLinearMap.restrictScalars ℤ
  measurementAction := SourceGeneratedActionWords.run
    (SourceGeneratedActionWords.advance (actions root recognition visit successor transition alignment U7 calculus count) (coarseRead root recognition visit successor transition alignment U7 calculus count)
      (.simultaneous : Letter root recognition visit successor)) letters
  coherentRead := Future.observation root recognition visit successor transition alignment U7 calculus count bound
  measurementRead := coarseRestriction root recognition visit successor transition alignment U7 calculus count
theorem exact_future (value : Model root recognition visit successor transition alignment U7 calculus count) :
    (input root recognition visit successor transition alignment U7 calculus count bound letters).coherentFace ((input root recognition visit successor transition alignment U7 calculus count bound letters).incidenceResidual value)=
      effect root recognition visit successor transition alignment U7 calculus count bound letters value :=
  (input root recognition visit successor transition alignment U7 calculus count bound letters).incidenceResidual_coherentFace value

theorem coarse_word (value : Model root recognition visit successor transition alignment U7 calculus count) :
    coarseRestriction root recognition visit successor transition alignment U7 calculus count (SourceGeneratedActionWords.run (advance root recognition visit successor transition alignment U7 calculus count) letters value)=
      SourceGeneratedActionWords.run
        (SourceGeneratedActionWords.advance (actions root recognition visit successor transition alignment U7 calculus count) (coarseRead root recognition visit successor transition alignment U7 calculus count)
          (.simultaneous : Letter root recognition visit successor)) letters (coarseRestriction root recognition visit successor transition alignment U7 calculus count value) := by
  induction letters generalizing value with
  | nil => rfl
  | cons first rest previous =>
    have single : coarseRestriction root recognition visit successor transition alignment U7 calculus count (advance root recognition visit successor transition alignment U7 calculus count first value)=
      SourceGeneratedActionWords.advance (actions root recognition visit successor transition alignment U7 calculus count) (coarseRead root recognition visit successor transition alignment U7 calculus count)
        (.simultaneous : Letter root recognition visit successor) first (coarseRestriction root recognition visit successor transition alignment U7 calculus count value) := by
      refine Submodule.Quotient.induction_on _ value (fun point => ?_)
      change coarseRestriction root recognition visit successor transition alignment U7 calculus count (advance root recognition visit successor transition alignment U7 calculus count first (projection root recognition visit successor transition alignment U7 calculus count point))=
        SourceGeneratedActionWords.advance (actions root recognition visit successor transition alignment U7 calculus count) (coarseRead root recognition visit successor transition alignment U7 calculus count)
          (.simultaneous : Letter root recognition visit successor) first (coarseRestriction root recognition visit successor transition alignment U7 calculus count (projection root recognition visit successor transition alignment U7 calculus count point))
      rw [SourceGeneratedActionWords.advance_source,coarse_source,coarse_source]
      exact (SourceGeneratedActionWords.advance_source _ _ _ _ point).symm
    exact (previous (advance root recognition visit successor transition alignment U7 calculus count first value)).trans
      (congrArg (SourceGeneratedActionWords.run
        (SourceGeneratedActionWords.advance (actions root recognition visit successor transition alignment U7 calculus count) (coarseRead root recognition visit successor transition alignment U7 calculus count)
          (.simultaneous : Letter root recognition visit successor)) rest) single)

theorem exact_coarse (value : Model root recognition visit successor transition alignment U7 calculus count) :
    (input root recognition visit successor transition alignment U7 calculus count bound letters).measurementFace ((input root recognition visit successor transition alignment U7 calculus count bound letters).incidenceResidual value)=0 :=
  (input root recognition visit successor transition alignment U7 calculus count bound letters).incidenceResidual_measurementFace value |>.trans
    (sub_eq_zero.mpr (coarse_word root recognition visit successor transition alignment U7 calculus count letters value).symm)
end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceOrbit
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
