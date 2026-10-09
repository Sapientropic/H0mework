import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Calculation.Source
import H0mework.Versions.AD.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Inquiry.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
namespace Lower.SourceFamily.Evaluated.Answer
namespace E
export RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source
 (endpointState endpointInput endpointCount endpoint_source_state compiled actual_next original_material answerFace)
end E
variable {S : Type u} {W X : S → Type u} [∀ t,AddCommGroup (W t)] {s : S}
variable (binding : ∀ t,X t → Expr W X t)
variable (seed : RootedAccountedUnfolding (PresentedRelationEventAt (Expr W X s)))
variable (frame : M.Frame (Value:=W) (Var:=X) (sort:=s))
abbrev sourceRoot := (Q.base frame).root
abbrev sourceVisit : SourceNativeTemporalVisitAt (sourceRoot frame).toAuthoritativeRoot.toLedgerRoot :=
 SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualVisit frame
abbrev sourceU7 := (Q.base frame).U7
abbrev sourceCalculus := (Q.base frame).calculus
abbrev endpointCount := E.endpointCount (sourceRoot frame) (sourceVisit frame) (reader binding seed frame)
abbrev state := E.endpointState (sourceRoot frame) (sourceVisit frame) (sourceU7 frame) (sourceCalculus frame) (reader binding seed frame)
abbrev input := E.endpointInput (sourceRoot frame) (sourceVisit frame) (sourceU7 frame) (sourceCalculus frame) (reader binding seed frame)
abbrev face := E.answerFace (sourceRoot frame) (sourceVisit frame) (sourceU7 frame) (sourceCalculus frame) (reader binding seed frame) (endpointCount binding seed frame)

theorem same_result : (face binding seed frame).rootRead=(result binding seed frame).2.1 := rfl

def completed : SourceOperationExecutionDebt.Settlement (face binding seed frame).rootRead :=
 Lower.SourceFamily.Evaluated.completed binding seed frame

theorem terminal_value : (completed binding seed frame).1=(raw binding seed frame).expression.eval (raw binding seed frame).environment :=
 SourceOperationExecutionDebt.completed_value _ (completed binding seed frame)

theorem actual_compilation : type_of% (E.compiled (sourceRoot frame) (sourceVisit frame) (sourceU7 frame) (sourceCalculus frame)
 (reader binding seed frame) (endpointCount binding seed frame)) := E.compiled _ _ _ _ _ _

theorem actual_next : type_of% (E.actual_next (sourceRoot frame) (sourceVisit frame) (sourceU7 frame) (sourceCalculus frame)
 (reader binding seed frame) (endpointCount binding seed frame)) := E.actual_next _ _ _ _ _ _

theorem original_material : type_of% (E.original_material (sourceRoot frame) (sourceVisit frame) (sourceU7 frame) (sourceCalculus frame)
 (reader binding seed frame) (endpointCount binding seed frame)) := E.original_material _ _ _ _ _ _
end Lower.SourceFamily.Evaluated.Answer

end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
