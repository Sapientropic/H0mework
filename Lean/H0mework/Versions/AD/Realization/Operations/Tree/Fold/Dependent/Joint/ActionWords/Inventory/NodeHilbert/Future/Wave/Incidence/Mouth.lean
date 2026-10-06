import H0mework.Versions.AD.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.Incidence.Consumer
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceIncidence
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


variable (letter : Letter root recognition visit successor) (historyWord : List (Letter root recognition visit successor))
variable (point : Carrier root recognition visit successor) (seedWord : List (Letter root recognition visit successor))
theorem original_future (bound : Nat) :
    (PaidSourceFullOrbit.input root recognition visit successor transition alignment U7 calculus count).coherentFace (current root recognition visit successor transition alignment U7 calculus count historyWord point seedWord) bound=
      Wave.effect root recognition visit successor transition alignment U7 calculus count bound historyWord (currentModel root recognition visit successor transition alignment U7 calculus count point seedWord) :=
  (congrArg (fun value => (PaidSourceFullOrbit.input root recognition visit successor transition alignment U7 calculus count).coherentFace value bound)
    (source_value root recognition visit successor transition alignment U7 calculus count historyWord point seedWord)).trans
    (PaidSourceFullOrbit.exact_future root recognition visit successor transition alignment U7 calculus count bound historyWord (currentModel root recognition visit successor transition alignment U7 calculus count point seedWord))
theorem joint_recovery : PaidSourceFullRecovery.recover root recognition visit successor transition alignment U7 calculus count
    (PaidSourceFullRecovery.emit root recognition visit successor transition alignment U7 calculus count (current root recognition visit successor transition alignment U7 calculus count historyWord point seedWord))=
      (PaidSourceFullOrbit.input root recognition visit successor transition alignment U7 calculus count).incidence historyWord (currentModel root recognition visit successor transition alignment U7 calculus count point seedWord) :=
  (PaidSourceFullRecovery.recover_emit root recognition visit successor transition alignment U7 calculus count (current root recognition visit successor transition alignment U7 calculus count historyWord point seedWord)).trans
    (source_value root recognition visit successor transition alignment U7 calculus count historyWord point seedWord)
end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceIncidence
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
