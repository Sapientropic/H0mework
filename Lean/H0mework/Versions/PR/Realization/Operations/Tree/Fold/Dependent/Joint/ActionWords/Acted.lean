import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Programme
import H0mework.Realization.Operations.Execution.LinearInput
import H0mework.Versions.AD.Foundation.Responsibility.JointSource.OwnerFree.Installation.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords
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
variable (point : Carrier root recognition visit successor) (word : List Letter)
def sourceRaw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
    (Value:=Value root recognition visit successor transition alignment U7 calculus count) (Var:=Var) (sort:=.model) :=
  ⟨environment root recognition visit successor transition alignment U7 calculus count point,
    programme root recognition visit successor transition alignment U7 calculus count word⟩
abbrev original := (Joint.actualRoot root visit recognition successor transition alignment).toAuthoritativeRoot
abbrev originalReader := fun (_ : root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt visit.current) =>
  sourceRaw root recognition visit successor transition alignment U7 calculus count point word
namespace O
export RootGeneratedDebtActivationJointSource.OwnerFree.Consumer (value trace target_expression)
end O

def actualTrace : Trace
    (environment root recognition visit successor transition alignment U7 calculus count point)
    (programme root recognition visit successor transition alignment U7 calculus count word)
    (.const (O.value (original root recognition visit successor transition alignment) visit.current
      (originalReader root recognition visit successor transition alignment U7 calculus count point word))) :=
  (O.target_expression (original root recognition visit successor transition alignment) visit.current
    (originalReader root recognition visit successor transition alignment U7 calculus count point word)) ▸
      O.trace (original root recognition visit successor transition alignment) visit.current
        (originalReader root recognition visit successor transition alignment U7 calculus count point word)

def acted := originalInput (actualTrace root recognition visit successor transition alignment U7 calculus count point word)

theorem acted_value : (acted root recognition visit successor transition alignment U7 calculus count point word).1 =
    SourceGeneratedActionWords.run (actions root recognition visit successor transition alignment U7 calculus count) word point :=
  (completed_trace_value _ (acted root recognition visit successor transition alignment U7 calculus count point word).2.1).trans
    (source_eval root recognition visit successor transition alignment U7 calculus count point word (.var PUnit.unit))

theorem acted_history : (acted root recognition visit successor transition alignment U7 calculus count point word).2.1.length = word.length+1 :=
  (acted root recognition visit successor transition alignment U7 calculus count point word).2.1.length_to_const.trans
    ((source_budget root recognition visit successor transition alignment U7 calculus count word (.var PUnit.unit)).trans (Nat.add_comm 1 word.length))
theorem acted_model : projection root recognition visit successor transition alignment U7 calculus count
    (acted root recognition visit successor transition alignment U7 calculus count point word).1 =
      O.value (original root recognition visit successor transition alignment) visit.current
        (originalReader root recognition visit successor transition alignment U7 calculus count point word) :=
  (acted root recognition visit successor transition alignment U7 calculus count point word).2.2.down

end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
