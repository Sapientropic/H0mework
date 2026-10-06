import H0mework.Versions.AE.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.Incidence.Branch.Consumer
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceIncidenceBranch
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
abbrev jointValue := PaidSourceFullRecovery.emit root recognition visit successor transition alignment U7 calculus count (current root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord)
theorem full_recovery : PaidSourceFullRecovery.recover root recognition visit successor transition alignment U7 calculus count (jointValue root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord)=
    current root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord := PaidSourceFullRecovery.recover_emit _ _ _ _ _ _ _ _ _ _
theorem recovered_next : PaidSourceFullRecovery.recover root recognition visit successor transition alignment U7 calculus count
    (PaidSourceFullRecovery.rangeAdvance root recognition visit successor transition alignment U7 calculus count letter (jointValue root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord))=
      normal root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter :=
  (PaidSourceFullRecovery.recover_action root recognition visit successor transition alignment U7 calculus count letter (jointValue root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord)).trans
    ((congrArg (PaidSourceFullOrbit.advance root recognition visit successor transition alignment U7 calculus count letter)
      (full_recovery root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord)).trans
      (normal_value root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter).symm)
end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceIncidenceBranch
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
