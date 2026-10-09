import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Forecast.Source
import H0mework.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Forecast.Charge
import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Phase.Source

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift SourceOperationScalarRelations
open CofinalHistorySettlement CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt
namespace Lower.SourceFamily.Foresight.Contextual.Forecast.Payments
namespace D
export Lower.SourceFamily.Foresight.Contextual.Forecast.Dispatch
  (face queryRaw free_evaluation kernelWord pointWord point_word)
end D
namespace J
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint (history)
end J
namespace F
export Lower.SourceFamily.Foresight.Contextual.Forecast
  (query nativeFrame nativeIndex sourceRaw source disposition)
end F
namespace Charge
export Coefficients.SourceCharge (expression_charge)
end Charge
namespace P
export Lower.SourceFamily.Foresight.Paid (expression paidTrace complete_fee)
end P
namespace Phase
export Lower.SourceFamily.Foresight.Contextual.Phase (single_fee)
end Phase
namespace Fee
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.DebtReplay.Math (lift_fee)
end Fee

section Small
variable {S : Type u} {V X : S → Type u} [∀ t,AddCommGroup (V t)] {s : S}
variable {Target : Type u} [AddCommGroup Target] [Module ℤ Target]
variable (seed : RootedAccountedUnfolding (PresentedRelationEventAt (Expr V X s)))
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame (Value:=V) (Var:=X) (sort:=s))
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
variable (occurrence : SourceOperationInquiry.Context.Installation.Occurrence frame (current:=current))
variable (source : RootGeneratedDebtActivationJointSource.OwnerFree.Raw (Value:=PairValue V) (Var:=X) (sort:=s))
variable (e : Formal ℤ (PairValue V) X s →ₗ[ℤ] Target)

private theorem generated_query_charge
    (sourceCharge : 2≤remaining source.expression)
    (outcome : ResidualDispositionOutcome (D.face seed frame occurrence e)) :
    2≤remaining (D.queryRaw seed frame occurrence source e outcome).expression := by
  cases outcome with
  | faithful _ _ _ => exact sourceCharge
  | unsound _ point =>
    apply Charge.expression_charge
    intro zero
    apply point.coordinate_ne_zero
    exact point.coordinate_eq.trans ((D.free_evaluation seed frame occurrence e point.relation).trans
      ((congrArg (SourceOperationLogic.q e) zero).trans (map_zero _)))
  | kernelResidual sound _ point =>
    apply Charge.expression_charge
    intro zero
    let selected := D.kernelWord seed frame occurrence e sound point
    have selectedZero : selected=0 := Subtype.ext zero
    have selectedCoordinate :
        (J.history seed frame occurrence).relationInGeneratorClosure.mkQ selected = point.coordinate.val :=
      Classical.choose_spec (Submodule.Quotient.mk_surjective
        (J.history seed frame occurrence).relationInGeneratorClosure point.coordinate.val)
    exact point.coordinate_ne_zero (selectedCoordinate.symm.trans
      ((congrArg (J.history seed frame occurrence).relationInGeneratorClosure.mkQ selectedZero).trans (map_zero _)))
  | coverageResidual sound _ point =>
    apply Charge.expression_charge
    intro zero
    have representativeZero : point.representative=0 :=
      (D.point_word e point.representative).symm.trans
        ((congrArg (SourceOperationLogic.q e) zero).trans (map_zero _))
    apply point.coordinate_ne_zero
    exact point.representative_class.symm.trans
      ((congrArg (LinearMap.range ((D.face seed frame occurrence e).completionEvaluation sound)).mkQ representativeZero).trans (map_zero _))
end Small

variable {S : Type u} {W X : S → Type u} [∀ t,AddCommGroup (W t)] {s : S}
attribute [local instance] Lower.SourceFamily.Foresight.Contextual.groups
variable (binding : ∀ t,X t → Expr W X t) (n : Nat)
variable (data : Lower.SourceFamily.Packet (W:=W) (X:=X) (s:=s) n)
local instance modelModule : Module ℤ (Lower.SourceFamily.Foresight.Model binding
    (Lower.SourceFamily.Foresight.Contextual.Forecast.state n data) s 0) :=
  (SourceGeneratedScalarCharacterExact.Carrier ℤ (Lower.SourceFamily.Foresight.completion binding
    (Lower.SourceFamily.Foresight.Contextual.Forecast.state n data) s 0)).module

theorem query_charge : 2≤remaining (F.query binding n data).expression := by
  have sourceFee := Lower.SourceFamily.Foresight.Contextual.Reader.Core.source_fee binding n data.2
    (F.nativeFrame n data) (F.nativeIndex n data)
  exact generated_query_charge data.2 (F.nativeFrame n data) (F.nativeIndex n data).2
    (F.sourceRaw binding n data) (F.source binding n data)
    ((by omega : 2≤3).trans sourceFee) (F.disposition binding n data)

def queryWord : Formal ℤ (PairValue (Lower.Value W n)) X s :=
  Finsupp.single (F.query binding n data).expression 1

theorem writer_charge : 4≤remaining (P.expression (W:=W) (X:=X) n s (queryWord binding n data)) := by
  have lifted : liftMap (R:=ℤ) (queryWord binding n data)=
      Finsupp.single (liftExpr (F.query binding n data).expression) 1 := by
    simp only [queryWord,liftMap,Finsupp.lmapDomain_apply,Finsupp.mapDomain_single]
  rw [P.expression,lifted,Phase.single_fee,Fee.lift_fee]
  have paid := query_charge binding n data
  omega

theorem writer_trace_charge :
    4≤(P.paidTrace binding n data s (queryWord binding n data)).length :=
  (writer_charge binding n data).trans_eq (P.complete_fee binding n data s (queryWord binding n data)).symm

end Lower.SourceFamily.Foresight.Contextual.Forecast.Payments
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
