import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.Incidence.Installation
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
abbrev normal := RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.value
  (sourceRoot root recognition visit successor transition alignment U7 calculus count letter historyWord point seedWord).toAuthoritativeRoot visit.current
  (reader root recognition visit successor transition alignment U7 calculus count letter historyWord point seedWord)
theorem normal_value : normal root recognition visit successor transition alignment U7 calculus count letter historyWord point seedWord=
    nextValue root recognition visit successor transition alignment U7 calculus count letter historyWord point seedWord :=
  (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.value_source _ _ _).trans
    (orbit_eval root recognition visit successor transition alignment U7 calculus count letter (current root recognition visit successor transition alignment U7 calculus count historyWord point seedWord))
theorem cost : (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.trace
    (sourceRoot root recognition visit successor transition alignment U7 calculus count letter historyWord point seedWord).toAuthoritativeRoot visit.current
    (reader root recognition visit successor transition alignment U7 calculus count letter historyWord point seedWord)).length=2 :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.paid_history _ _ _
theorem source_value : current root recognition visit successor transition alignment U7 calculus count historyWord point seedWord=
    (PaidSourceFullOrbit.input root recognition visit successor transition alignment U7 calculus count).incidence historyWord (currentModel root recognition visit successor transition alignment U7 calculus count point seedWord) :=
  (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.value_source _ _ _).trans
    (programme_value root recognition visit successor transition alignment U7 calculus count historyWord (currentModel root recognition visit successor transition alignment U7 calculus count point seedWord))
theorem source_cost : (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.trace root.toAuthoritativeRoot visit.current
    (seedReader root recognition visit successor transition alignment U7 calculus count historyWord point seedWord)).length=2*historyWord.length+6 :=
  (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.paid_history _ _ _).trans
    (programme_budget root recognition visit successor transition alignment U7 calculus count historyWord)
end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceIncidence
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
