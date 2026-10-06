import H0mework.Versions.AC.Realization.Operations.Tree.Fold.Dependent.Next.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Next
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution
open RootLawDependentJointStateController RootLawDependentJointTransition RootLawDependentJointPassiveEffect
namespace D
export SourceOperationNative.Tree.Fold.Dependent (FeedAt sourceFeed nativeReader nativeTree)
end D
namespace M
export RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source
  (runtime activated_query activated_answer activated_next)
end M
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (recognition : RecognitionAt H root)
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7)
variable (successor : StepLedgerSuccessorAt (step root visit recognition))
variable (transition : GeneratedStepJointTransitionAt (step root visit recognition) successor)
variable (alignment : RootedAccountedUnfoldingZip.GeneratedZipAt
  (stepSourcePairingOccurrence (step root visit recognition)) (stepTargetPairingOccurrence (step root visit recognition) successor))
theorem actual_next_material : HEq
    (recognition.material.parent.commonLaw.historyAt successor.targetOccurrence)
    (recognition.material.parent.commonLaw.historyAt (root.emitted (nextVisit root visit recognition successor).current)) := by
  rw [successor_targetOccurrence_eq_emitted (step root visit recognition) successor]
  rfl


theorem current_whole_next : HEq (step root visit recognition).wholeLedgerWriteBack
    (root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt visit.current) ∧
    (step root visit recognition).nextCurrent = root.generatedNextCurrentAt visit :=
  ⟨(step root visit recognition).wholeLedgerWriteBack_eq_root,
    (step root visit recognition).nextCurrent_eq_root⟩

theorem next_whole_next :
    let nextStep := recognition.generateStepAt (nextVisit root visit recognition successor)
    HEq nextStep.wholeLedgerWriteBack
      (root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
        (nextVisit root visit recognition successor).current) ∧
      nextStep.nextCurrent = root.generatedNextCurrentAt (nextVisit root visit recognition successor) :=
  ⟨(recognition.generateStepAt (nextVisit root visit recognition successor)).wholeLedgerWriteBack_eq_root,
    (recognition.generateStepAt (nextVisit root visit recognition successor)).nextCurrent_eq_root⟩

theorem query_answer_next (offset : Nat) :
    type_of% (M.activated_query root visit U7 calculus (reader root visit recognition successor transition alignment) offset) ∧
    type_of% (M.activated_answer root visit U7 calculus (reader root visit recognition successor transition alignment) offset) ∧
    type_of% (M.activated_next root visit U7 calculus (reader root visit recognition successor transition alignment) offset) :=
  ⟨M.activated_query root visit U7 calculus (reader root visit recognition successor transition alignment) offset,
    M.activated_answer root visit U7 calculus (reader root visit recognition successor transition alignment) offset,
    M.activated_next root visit U7 calculus (reader root visit recognition successor transition alignment) offset⟩
end SourceOperationNative.Tree.Fold.Dependent.Next
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
