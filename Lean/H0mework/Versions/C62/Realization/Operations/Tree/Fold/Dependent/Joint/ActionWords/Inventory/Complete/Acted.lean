import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.Complete.Programme
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.Complete
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


variable (point : Carrier root recognition visit successor)
variable (word : List (Letter root recognition visit successor))
abbrev original := (EffectHistory.sourceRoot root recognition visit successor transition alignment U7 calculus count point word).toAuthoritativeRoot
abbrev originalReader := fun (_ : root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt visit.current) =>
  raw root recognition visit successor transition alignment U7 calculus count point word
def actualTrace : Trace (environment root recognition visit successor transition alignment U7 calculus count point)
    (programme root recognition visit successor transition alignment U7 calculus count word)
    (.const (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.value
      (original root recognition visit successor transition alignment U7 calculus count point word) visit.current
      (originalReader root recognition visit successor transition alignment U7 calculus count point word))) :=
  (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.target_expression
    (original root recognition visit successor transition alignment U7 calculus count point word) visit.current
    (originalReader root recognition visit successor transition alignment U7 calculus count point word)) ▸
    RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.trace
      (original root recognition visit successor transition alignment U7 calculus count point word) visit.current
      (originalReader root recognition visit successor transition alignment U7 calculus count point word)
def acted := originalInput (actualTrace root recognition visit successor transition alignment U7 calculus count point word)
theorem acted_value : (acted root recognition visit successor transition alignment U7 calculus count point word).1 =
    actedComplete root recognition visit successor transition alignment U7 calculus count
      (sourceMap root recognition visit successor transition alignment U7 calculus count point) word :=
  (completed_trace_value _ (acted root recognition visit successor transition alignment U7 calculus count point word).2.1).trans
    (whole_eval root recognition visit successor transition alignment U7 calculus count point word
      (.linear (s:=Slot.source) (sourceMap root recognition visit successor transition alignment U7 calculus count).toAddMonoidHom (.var PUnit.unit)))
end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.Complete
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
