import H0mework.Versions.MF.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Phase.Source
import H0mework.Versions.MF.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Phase.Written
import H0mework.Versions.MF.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Mixed.Effect
import H0mework.Versions.MF.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Effect
import H0mework.Versions.MF.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Whole.Equation
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation SourceGeneratedScalarDifferentialResidual CofinalHistorySettlement
namespace Lower.SourceFamily.Foresight.Contextual.Phase
namespace R
export Lower.SourceFamily.Foresight.Contextual.Reader (residualExpression completed residual_fee)
end R
namespace E
export Lower.SourceFamily.Foresight.Contextual.Effect (actualEnvironment actualDecoder actualIncrement actual_word actual_paid_value actual_new_kernel)
end E
namespace P
export Lower.SourceFamily.Foresight.Paid (result expression paidTrace complete_fee all_paid_relations)
end P
namespace L
export Lower.SourceFamily.Foresight.Paid.Ledger (SourceEvent eventWord writeEvent)
end L
namespace Fee
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.DebtReplay.Math (lift_fee)
end Fee
variable {S : Type u} {W X : S → Type u} [∀ t, AddCommGroup (W t)] {s : S}
attribute [local instance] Lower.SourceFamily.Foresight.Contextual.groups
variable (binding : ∀ t,X t → Expr W X t) (n : Nat)
variable (data : Lower.SourceFamily.Packet (W:=W) (X:=X) (s:=s) n)
abbrev index := Lower.SourceFamily.Foresight.Contextual.actualIndex n data.1
abbrev currentr := R.residualExpression binding n data.2
 (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch data.1) (index n data)
abbrev currentTrace := (R.completed binding n data.2
 (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch data.1) (index n data)).2.1.2
def currentB : Env (Lower.Value W (n+1)) X := Lower.SourceFamily.Foresight.Contextual.Mixed.ownEnv binding n data.2
 (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch data.1) (index n data)
abbrev currentBeta := Lower.SourceFamily.Foresight.Contextual.Mixed.sourceBoundary binding n data.2
 (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch data.1) (index n data)
abbrev phaseEffect := effectEvaluator (R:=ℤ) (currentB binding n data)
 (E.actualDecoder binding n data-currentB binding n data) (currentBeta binding n data)
abbrev bindingEffect := effectEvaluator (R:=ℤ) (E.actualDecoder binding n data)
 (E.actualIncrement binding n data) (currentBeta binding n data)

theorem actual_pair : type_of%
 ((E.actual_word binding n data s (requestWord binding n data)).trans
  (single_pair (currentB binding n data) (currentTrace binding n data)
   (E.actualDecoder binding n data) (E.actualIncrement binding n data))) :=
 (E.actual_word binding n data s (requestWord binding n data)).trans
 (single_pair (currentB binding n data) (currentTrace binding n data)
  (E.actualDecoder binding n data) (E.actualIncrement binding n data))

theorem paid_pair : type_of%
 ((E.actual_paid_value binding n data s (requestWord binding n data)).trans (actual_pair binding n data)) :=
 (E.actual_paid_value binding n data s (requestWord binding n data)).trans (actual_pair binding n data)

theorem expression_pair : type_of%
 ((Coefficients.expression_eval (liftMap (R:=ℤ) (requestWord binding n data)) (E.actualEnvironment binding n data)).trans
  (actual_pair binding n data)) :=
 (Coefficients.expression_eval (liftMap (R:=ℤ) (requestWord binding n data)) (E.actualEnvironment binding n data)).trans
 (actual_pair binding n data)

theorem expression_fee : remaining (P.expression (W:=W) (X:=X) n s (requestWord binding n data))=
 remaining (currentr binding n data)+2 := by
 have lifted : liftMap (R:=ℤ) (requestWord binding n data)=Finsupp.single (liftExpr (currentr binding n data)) 1 :=by
  simp only [requestWord,Paid.Ledger.eventWord,phaseEvent,liftMap,Finsupp.lmapDomain_apply,Finsupp.mapDomain_single]
 rw [P.expression,lifted,single_fee,Fee.lift_fee]

theorem source_charge : 4≤remaining (P.expression (W:=W) (X:=X) n s (requestWord binding n data)) := by
 have paid := R.residual_fee binding n data.2 (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch data.1) (index n data)
 rw [expression_fee]
 change 2≤remaining (currentr binding n data) at paid
 omega

theorem full_history : (P.paidTrace binding n data s (requestWord binding n data)).length=remaining (currentr binding n data)+2 :=
 (P.complete_fee binding n data s (requestWord binding n data)).trans (expression_fee binding n data)

theorem paid_relations : type_of% (P.all_paid_relations binding n data s (requestWord binding n data)) :=P.all_paid_relations _ _ _ _ _
theorem actual_kernel : type_of% (E.actual_new_kernel binding n data s (requestWord binding n data)) :=E.actual_new_kernel _ _ _ _ _
theorem event_word : L.eventWord n (phaseEvent binding n data)=requestWord binding n data :=rfl
theorem actual_write : L.writeEvent binding n data (phaseEvent binding n data)=
 SourceOperationPaidRelations.exposure (P.paidTrace binding n data s (requestWord binding n data)) :=rfl

theorem complete_next_high : type_of% (Lower.SourceFamily.Foresight.Whole.actual_high_head binding n data s (requestWord binding n data)) :=
 Lower.SourceFamily.Foresight.Whole.actual_high_head _ _ _ _ _
theorem beta_next_high : type_of% (Lower.SourceFamily.Foresight.Whole.actual_high_head binding n data s (currentBeta binding n data)) :=
 Lower.SourceFamily.Foresight.Whole.actual_high_head _ _ _ _ _
end Lower.SourceFamily.Foresight.Contextual.Phase
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
