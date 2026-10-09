import H0mework.Versions.V2.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.Words.Installation
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

variable (bound : Nat) (letter : Letter root recognition visit successor) (historyWord : List (Letter root recognition visit successor))
variable (point : Carrier root recognition visit successor) (seedWord : List (Letter root recognition visit successor))
abbrev normal := RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.value
  (sourceRoot root recognition visit successor transition alignment U7 calculus count bound letter historyWord point seedWord).toAuthoritativeRoot visit.current
  (reader root recognition visit successor transition alignment U7 calculus count bound letter historyWord point seedWord)
theorem normal_value : normal root recognition visit successor transition alignment U7 calculus count bound letter historyWord point seedWord=
    nextValue root recognition visit successor transition alignment U7 calculus count bound letter historyWord point seedWord :=
  (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.value_source _ _ _).trans
    (orbit_eval root recognition visit successor transition alignment U7 calculus count bound letter (current root recognition visit successor transition alignment U7 calculus count bound historyWord point seedWord))
theorem cost : (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.trace
    (sourceRoot root recognition visit successor transition alignment U7 calculus count bound letter historyWord point seedWord).toAuthoritativeRoot visit.current
    (reader root recognition visit successor transition alignment U7 calculus count bound letter historyWord point seedWord)).length=2 :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.paid_history _ _ _
theorem source_value : current root recognition visit successor transition alignment U7 calculus count bound historyWord point seedWord=
    SourceGeneratedActionWords.run (advance root recognition visit successor transition alignment U7 calculus count bound) historyWord
      (seed root recognition visit successor transition alignment U7 calculus count bound (currentModel root recognition visit successor transition alignment U7 calculus count point seedWord)) :=
  (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.value_source _ _ _).trans
    (programme_value root recognition visit successor transition alignment U7 calculus count bound historyWord (currentModel root recognition visit successor transition alignment U7 calculus count point seedWord))
theorem source_cost : (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.trace root.toAuthoritativeRoot visit.current
    (seedReader root recognition visit successor transition alignment U7 calculus count bound historyWord point seedWord)).length=historyWord.length+2 :=
  (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.paid_history _ _ _).trans
    (programme_budget root recognition visit successor transition alignment U7 calculus count bound historyWord)
end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceWordOrbit
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
