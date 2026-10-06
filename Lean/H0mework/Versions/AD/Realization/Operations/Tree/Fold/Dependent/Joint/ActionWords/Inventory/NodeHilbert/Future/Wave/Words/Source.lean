import H0mework.Versions.AD.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.Words.Kernel
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceWordOrbit
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

variable (bound : Nat)
def input : SourceGeneratedJointActionWords.Input
    (Letter root recognition visit successor)
    (Model root recognition visit successor transition alignment U7 calculus count)
    (Space root recognition visit successor bound)
    (CoarseModel root recognition visit successor transition alignment U7 calculus count) where
  integralAction := Inventory.advance root recognition visit successor transition alignment U7 calculus count
  coherentAction := fun letter => (evolution root recognition visit successor bound letter).toLinearMap.restrictScalars ℤ
  measurementAction := Recovery.coarseAdvance root recognition visit successor transition alignment U7 calculus count
  coherentRead := Future.observation root recognition visit successor transition alignment U7 calculus count bound
  measurementRead := coarseRestriction root recognition visit successor transition alignment U7 calculus count
abbrev WordCarrier := (input root recognition visit successor transition alignment U7 calculus count bound).Carrier
abbrev advance := (input root recognition visit successor transition alignment U7 calculus count bound).advance
abbrev seed := (input root recognition visit successor transition alignment U7 calculus count bound).seedLift
abbrev integralFace := (input root recognition visit successor transition alignment U7 calculus count bound).integralFace
abbrev coherentFace := (input root recognition visit successor transition alignment U7 calculus count bound).coherentFace
abbrev measurementFace := (input root recognition visit successor transition alignment U7 calculus count bound).measurementFace

theorem single_source (letter : Letter root recognition visit successor) :
    (input root recognition visit successor transition alignment U7 calculus count bound).single letter=
      PaidSourceOrbit.operation root recognition visit successor transition alignment U7 calculus count bound letter := rfl

theorem wave_word (letters : List (Letter root recognition visit successor))
    (value : Space root recognition visit successor bound) :
    SourceGeneratedActionWords.run (input root recognition visit successor transition alignment U7 calculus count bound).coherentAction letters value=
      wordEvolution root recognition visit successor bound letters value := by
  induction letters generalizing value with
  | nil => rfl
  | cons first rest previous => exact previous (evolution root recognition visit successor bound first value)

theorem exact_future (letters : List (Letter root recognition visit successor))
    (value : Model root recognition visit successor transition alignment U7 calculus count) :
    coherentFace root recognition visit successor transition alignment U7 calculus count bound
      ((input root recognition visit successor transition alignment U7 calculus count bound).incidence letters value)=
      Wave.effect root recognition visit successor transition alignment U7 calculus count bound letters value :=
  ((input root recognition visit successor transition alignment U7 calculus count bound).incidence_coherent letters value).trans
    (congrArg (fun measured => measured-Future.observation root recognition visit successor transition alignment U7 calculus count bound
      (SourceGeneratedActionWords.run (Inventory.advance root recognition visit successor transition alignment U7 calculus count) letters value))
      (wave_word root recognition visit successor transition alignment U7 calculus count bound letters
        (Future.observation root recognition visit successor transition alignment U7 calculus count bound value)))
theorem exact_coarse (letters : List (Letter root recognition visit successor))
    (value : Model root recognition visit successor transition alignment U7 calculus count) :
    measurementFace root recognition visit successor transition alignment U7 calculus count bound
      ((input root recognition visit successor transition alignment U7 calculus count bound).incidence letters value)=0 :=
  ((input root recognition visit successor transition alignment U7 calculus count bound).incidence_measurement letters value).trans
    (sub_eq_zero.mpr (PaidSourceOrbit.coarse_word root recognition visit successor transition alignment U7 calculus count letters value).symm)
end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceWordOrbit
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
