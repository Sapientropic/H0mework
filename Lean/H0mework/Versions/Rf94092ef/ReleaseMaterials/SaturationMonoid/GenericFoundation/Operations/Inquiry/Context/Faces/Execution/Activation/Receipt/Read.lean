import H0mework.Versions.Rdf421ff6.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Source

set_option autoImplicit false
set_option Elab.async false
noncomputable section

universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedInquiryReceiptAction.Read
open SourceOperationEffects SourceOperationScalarInventoryLift SourceOperationExecution
namespace R
export SourceGeneratedInquiryReceiptAction (actualMaterial actionReader occurrence afterEnvironment)
end R
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ target, AddCommGroup (Value target)] {sort : Sorts}
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
  (Value := Value) (Var := Var) (sort := sort))
variable (cfg : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
  (PhysicalValue := Value) (PhysicalVar := Var) (sort := sort))

theorem raw_source :
    (R.actualMaterial frame cfg).raw = (R.actionReader frame cfg (R.occurrence frame cfg)).expression := rfl

theorem environment_source :
    (R.actualMaterial frame cfg).environment = (R.actionReader frame cfg (R.occurrence frame cfg)).environment := rfl

theorem increment_source :
    (R.actualMaterial frame cfg).increment =
      R.afterEnvironment frame cfg - (R.actionReader frame cfg (R.occurrence frame cfg)).environment := rfl

theorem updated_environment_source :
    (RootGeneratedDebtActivationJointSource.Native.ResidualRequest.input (R.actualMaterial frame cfg)).environment =
      R.afterEnvironment frame cfg := by
  change (R.actionReader frame cfg (R.occurrence frame cfg)).environment +
    (R.afterEnvironment frame cfg - (R.actionReader frame cfg (R.occurrence frame cfg)).environment) = _
  exact add_sub_cancel _ _

theorem state_source :
    (R.actualMaterial frame cfg).state =
      (SourceGeneratedInquiryReceiptAction.actionResultAt frame cfg (R.occurrence frame cfg)).2.1 := rfl


theorem occurrence_source :
    R.occurrence frame cfg =
      SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualOccurrence frame := rfl

theorem value_source :
    (SourceGeneratedInquiryReceiptAction.actionResultAt frame cfg (R.occurrence frame cfg)).2.2.1 =
      (R.actualMaterial frame cfg).raw.eval (R.actualMaterial frame cfg).environment :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.baseRoot frame cfg).toAuthoritativeRoot
    (R.actionReader frame cfg) (R.occurrence frame cfg)

theorem paid_source :
    (R.actualMaterial frame cfg).state.2.length = remaining (R.actualMaterial frame cfg).raw :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_history
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.baseRoot frame cfg).toAuthoritativeRoot
    (R.actionReader frame cfg) (R.occurrence frame cfg)

theorem after_environment_source :
    R.afterEnvironment frame cfg =
      (R.actionReader (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.next frame cfg) cfg
        (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualOccurrence
          (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.next frame cfg))).environment := rfl

end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedInquiryReceiptAction.Read
