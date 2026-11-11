import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Inventory.ActualQuery.Next.Consumer
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
universe u
namespace FullSourceLinearAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
namespace Q
export SourceGeneratedInquiryReceiptAction.Inventory.ActualQuery (programme commonInstalled)
end Q
namespace Next
export SourceGeneratedInquiryReceiptAction.Inventory.ActualQuery.Next (fullRaw actionRaw lowProgramme receiver action_value)
end Next
namespace Intake
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Intake.Lower (generatedAction)
end Intake
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (query resultFace actualOccurrence)
end S
namespace R
export SourceGeneratedInquiryReceiptAction (actionReader)
end R
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ t, AddCommGroup (Value t)] {sort : Sorts}
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value := Value) (Var := Var) (sort := sort))
variable (cfg : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
 (PhysicalValue := Value) (PhysicalVar := Var) (sort := sort))
variable (action : PairValue (PairValue Value) sort →+ PairValue (PairValue Value) sort)

def raw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
 (Value := PairValue (PairValue Value)) (Var := cfg.LowVar) (sort := sort) :=
 ⟨(Next.actionRaw frame cfg).environment,
  .linear action (Next.actionRaw frame cfg).expression⟩
def lowProgramme := { Next.lowProgramme frame cfg with
 datum := fun current => { (Next.lowProgramme frame cfg).datum current with
  calculationReader := some (fun {_current} _supplied => raw frame cfg action) } }
def programme := Q.programme (lowProgramme frame cfg action)
abbrev admitted := Intake.generatedAction frame (Q.programme cfg) (programme frame cfg action)
def admittedCommon := (admitted frame cfg action).target.targetRoot.source.base.projectionLaw.project
 ((admitted frame cfg action).target.oldProjection ((Q.commonInstalled frame cfg).embed PUnit.unit))
 ((admitted frame cfg action).target.targetRoot.emitted (admitted frame cfg action).target.targetVisit.current) PUnit.unit

theorem admitted_full_raw : (admittedCommon frame cfg action).2.1 = Next.fullRaw frame cfg := rfl
theorem reader_actual_source :
 (S.query (Next.receiver frame cfg) (programme frame cfg action)).raw =
 (⟨pairEnvironment (admittedCommon frame cfg action).2.1.environment 0,
   .linear action (liftExpr (admittedCommon frame cfg action).2.1.expression)⟩ :
  RootGeneratedDebtActivationJointSource.OwnerFree.Raw
   (Value := PairValue (PairValue Value)) (Var := cfg.LowVar) (sort := sort)) := rfl

theorem action_value : (raw frame cfg action).expression.eval (raw frame cfg action).environment =
 action ((Next.fullRaw frame cfg).expression.eval (Next.fullRaw frame cfg).environment, 0) :=
 congrArg action (Next.action_value frame cfg)
theorem action_budget : remaining (raw frame cfg action).expression =
 remaining (Next.actionRaw frame cfg).expression + 1 := rfl

theorem actual_value : (S.resultFace (Next.receiver frame cfg) (programme frame cfg action)).rootRead.2.2.1 =
 action ((Next.fullRaw frame cfg).expression.eval (Next.fullRaw frame cfg).environment, 0) :=
 (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.baseRoot
   (Next.receiver frame cfg) (programme frame cfg action)).toAuthoritativeRoot
  (R.actionReader (Next.receiver frame cfg) (programme frame cfg action))
  (S.actualOccurrence (Next.receiver frame cfg))).trans (action_value frame cfg action)
end FullSourceLinearAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
