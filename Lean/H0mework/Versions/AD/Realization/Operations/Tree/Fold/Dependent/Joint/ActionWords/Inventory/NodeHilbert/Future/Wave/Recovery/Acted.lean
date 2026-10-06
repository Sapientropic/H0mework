import H0mework.Versions.AD.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.Recovery.Programme
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceFullRecovery
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

local instance : Module ℤ (JointCarrier root recognition visit successor transition alignment U7 calculus count) :=
  AddCommGroup.toIntModule _
variable (point : Carrier root recognition visit successor)
variable (seedWord : List (Letter root recognition visit successor))
variable (historyWord : List (Letter root recognition visit successor))
variable (queryWord : List (Letter root recognition visit successor))
abbrev inputModel := PaidSourceFullOrbit.current root recognition visit successor transition alignment U7 calculus count historyWord point seedWord
def sourceRaw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
    (Value:=Value root recognition visit successor transition alignment U7 calculus count) (Var:=Var) (sort:=Slot.model) :=
  ⟨environmentAt root recognition visit successor transition alignment U7 calculus count (inputModel root recognition visit successor transition alignment U7 calculus count point seedWord historyWord),programme root recognition visit successor transition alignment U7 calculus count queryWord⟩
def sourceReader {current : V.Current} (_ : root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) :=
  sourceRaw root recognition visit successor transition alignment U7 calculus count point seedWord historyWord queryWord
def actualTrace : Trace (environmentAt root recognition visit successor transition alignment U7 calculus count (inputModel root recognition visit successor transition alignment U7 calculus count point seedWord historyWord))
    (programme root recognition visit successor transition alignment U7 calculus count queryWord)
    (.const (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.value root.toAuthoritativeRoot visit.current
      (sourceReader root recognition visit successor transition alignment U7 calculus count point seedWord historyWord queryWord))) :=
  (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.target_expression root.toAuthoritativeRoot visit.current
    (sourceReader root recognition visit successor transition alignment U7 calculus count point seedWord historyWord queryWord)) ▸
  RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.trace root.toAuthoritativeRoot visit.current
    (sourceReader root recognition visit successor transition alignment U7 calculus count point seedWord historyWord queryWord)
def acted := originalInput (actualTrace root recognition visit successor transition alignment U7 calculus count point seedWord historyWord queryWord)
theorem acted_value : (acted root recognition visit successor transition alignment U7 calculus count point seedWord historyWord queryWord).1=
    SourceGeneratedActionWords.run (rangeAdvance root recognition visit successor transition alignment U7 calculus count) queryWord
      (emit root recognition visit successor transition alignment U7 calculus count (inputModel root recognition visit successor transition alignment U7 calculus count point seedWord historyWord)) :=
  (completed_trace_value _ (acted root recognition visit successor transition alignment U7 calculus count point seedWord historyWord queryWord).2.1).trans
    (range_eval root recognition visit successor transition alignment U7 calculus count queryWord (inputModel root recognition visit successor transition alignment U7 calculus count point seedWord historyWord)
      (.linear (s:=Slot.model) (emit root recognition visit successor transition alignment U7 calculus count).toAddMonoidHom (.var PUnit.unit)))
theorem acted_budget : (acted root recognition visit successor transition alignment U7 calculus count point seedWord historyWord queryWord).2.1.length=queryWord.length+2 := by
  rw [(acted root recognition visit successor transition alignment U7 calculus count point seedWord historyWord queryWord).2.1.length_to_const]
  rw [range_budget]
  change 2+queryWord.length=queryWord.length+2
  omega
end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceFullRecovery
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
