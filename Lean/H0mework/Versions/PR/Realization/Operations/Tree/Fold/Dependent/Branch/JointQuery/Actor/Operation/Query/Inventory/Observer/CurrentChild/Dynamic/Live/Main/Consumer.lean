import H0mework.Versions.AD.Foundation.Responsibility.JointSource.OwnerFree.RawState
import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Consumer
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Main
open RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) (recognition : RecognitionAt H root)
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7) (anchor : Nat)
variable (frame : Dynamic.Frame root visit recognition)
variable (seed : RootedAccountedUnfolding (PresentedRelationEventAt
 (Expr (CurrentChild.Value root visit recognition) (CurrentChild.Variable root visit recognition) (CurrentChild.resultSlot root recognition))))
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
variable (supplied : Dynamic.C.Occurrence frame (current:=current))
abbrev actualResult := SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.resultAt frame
 (configuration root visit recognition U7 calculus anchor seed) supplied
theorem result_value : (actualResult root visit recognition U7 calculus anchor frame seed supplied).2.2.1=
 (paidAt root visit recognition U7 calculus anchor (E.epoch frame) seed supplied).2.2.1 := by
 have actualValue := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value
  (E.Shared.baseRoot frame (configuration root visit recognition U7 calculus anchor seed)).toAuthoritativeRoot
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.datum frame
   (configuration root visit recognition U7 calculus anchor seed)).reader supplied
 have helperValue := paid_value root visit recognition U7 calculus anchor (E.epoch frame) seed supplied
 exact actualValue.trans helperValue.symm
theorem result_trace : HEq
 (actualResult root visit recognition U7 calculus anchor frame seed supplied).2.1.2
 (paidAt root visit recognition U7 calculus anchor (E.epoch frame) seed supplied).2.1.2 := by
 change HEq
  (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.trace
   (E.Shared.baseRoot frame (configuration root visit recognition U7 calculus anchor seed)).toAuthoritativeRoot current
   (fun _ => rawAt root visit recognition U7 calculus anchor (E.epoch frame) seed supplied))
  (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.trace
   (E.Shared.base (E.epoch frame)).root.toAuthoritativeRoot current
   (fun _ => rawAt root visit recognition U7 calculus anchor (E.epoch frame) seed supplied))
 exact RootGeneratedDebtActivationJointSource.OwnerFree.common_raw_trace _ _ _ _ _
theorem result_exposure : SourceOperationPaidRelations.exposure
 (actualResult root visit recognition U7 calculus anchor frame seed supplied).2.1.2=
 SourceOperationPaidRelations.exposure
 (paidAt root visit recognition U7 calculus anchor (E.epoch frame) seed supplied).2.1.2 := by
 change SourceOperationPaidRelations.exposure
   (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.trace
    (E.Shared.baseRoot frame (configuration root visit recognition U7 calculus anchor seed)).toAuthoritativeRoot current
    (fun _ => rawAt root visit recognition U7 calculus anchor (E.epoch frame) seed supplied)) =
  SourceOperationPaidRelations.exposure
   (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.trace
    (E.Shared.base (E.epoch frame)).root.toAuthoritativeRoot current
    (fun _ => rawAt root visit recognition U7 calculus anchor (E.epoch frame) seed supplied))
 exact RootGeneratedDebtActivationJointSource.OwnerFree.common_raw_exposure _ _ _ _ _
theorem face_result : (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.resultFace frame
 (configuration root visit recognition U7 calculus anchor seed)).rootRead.2.2.1=
 (actualResult root visit recognition U7 calculus anchor frame seed (E.Shared.actualOccurrence frame)).2.2.1 := rfl
local instance : AddCommGroup (CurrentChild.Value root visit recognition (CurrentChild.resultSlot root recognition)) :=
 CurrentChild.instAddCommGroupValue root visit recognition (CurrentChild.resultSlot root recognition)
def recoveredAt := Sub.sub (α:=PairValue (CurrentChild.Value root visit recognition) (CurrentChild.resultSlot root recognition))
 (actualResult root visit recognition U7 calculus anchor frame seed supplied).2.2.1
 ((originalRawAt root visit recognition (E.epoch frame) seed supplied).expression.eval
  (originalRawAt root visit recognition (E.epoch frame) seed supplied).environment)
theorem recovered_current : (recoveredAt root visit recognition U7 calculus anchor frame seed supplied).1=
 (Dynamic.paidAt root visit recognition U7 calculus anchor (E.epoch frame) supplied).2.2.1 := by
 have same := congrArg (fun value : PairValue (CurrentChild.Value root visit recognition) (CurrentChild.resultSlot root recognition) =>
  (value - (originalRawAt root visit recognition (E.epoch frame) seed supplied).expression.eval
   (originalRawAt root visit recognition (E.epoch frame) seed supplied).environment).1)
  (result_value root visit recognition U7 calculus anchor frame seed supplied)
 exact same.trans (recover_current root visit recognition U7 calculus anchor (E.epoch frame) seed supplied)
end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Main
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
