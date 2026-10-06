import H0mework.Versions.AD.Realization.Operations.Tree.Fold.Dependent.Next.Source
import H0mework.Versions.AD.Realization.Operations.Tree.Fold.Dependent.Next.PursuitConsumer
import H0mework.Versions.AD.Realization.Operations.Tree.Fold.Dependent.Joint.Effect
import H0mework.Versions.AD.Realization.Operations.Tree.Fold.Dependent.Branch.RichConsumer
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

namespace J
export SourceOperationNative.Tree.Fold.Dependent.Joint
  (query_answer_next normal_inventory original_parent_next sourceRoot sourceVisit installedReader)
end J

theorem query_answer_next (offset : Nat) : type_of%
    (J.query_answer_next root visit recognition successor transition alignment U7 calculus offset) :=
  J.query_answer_next root visit recognition successor transition alignment U7 calculus offset

theorem parent_visit_readback (count : Nat) : type_of%
    (C.readback (J.sourceRoot root visit recognition successor transition alignment)
      (J.sourceVisit root visit recognition successor transition alignment) U7 calculus
      (J.installedReader root visit recognition successor transition alignment) count) :=
  C.readback (J.sourceRoot root visit recognition successor transition alignment)
    (J.sourceVisit root visit recognition successor transition alignment) U7 calculus
    (J.installedReader root visit recognition successor transition alignment) count

theorem temporal_normal_inverse : type_of%
    (J.normal_inventory root visit recognition successor transition alignment) :=
  J.normal_inventory root visit recognition successor transition alignment

theorem temporal_parent_next (count : Nat) : type_of%
    (J.original_parent_next root visit recognition successor transition alignment U7 calculus count) :=
  J.original_parent_next root visit recognition successor transition alignment U7 calculus count

theorem branch_query_answer_next (offset : Nat) : type_of%
    (SourceOperationNative.Tree.Fold.Dependent.Branch.query_answer_next root visit recognition U7 calculus offset) :=
  SourceOperationNative.Tree.Fold.Dependent.Branch.query_answer_next root visit recognition U7 calculus offset

theorem branch_parent_next (count : Nat) : type_of%
    (SourceOperationNative.Tree.Fold.Dependent.Branch.parent_next root visit recognition U7 calculus count) :=
  SourceOperationNative.Tree.Fold.Dependent.Branch.parent_next root visit recognition U7 calculus count

theorem branch_exact_payload (count : Nat) : type_of%
    (SourceOperationNative.Tree.Fold.Dependent.Branch.recovered_payload root visit recognition U7 calculus count) :=
  SourceOperationNative.Tree.Fold.Dependent.Branch.recovered_payload root visit recognition U7 calculus count
end SourceOperationNative.Tree.Fold.Dependent.Next
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
