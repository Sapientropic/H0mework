import H0mework.Versions.AD.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Compiler
import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Successor.Inquiry.Target
import Lean.LibrarySuggestions.Basic
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "SourceGeneratedInquiryReceiptAction"
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedInquiryReceiptAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution
open SourceOperationScalarInventoryLift DebtActivationWorld
variable {S : Type u} {PhysicalValue PhysicalVar : S → Type u}
 [∀ target,AddCommGroup (PhysicalValue target)] {slot : S}
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=slot))
variable (configuration : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
 (PhysicalValue:=PhysicalValue) (PhysicalVar:=PhysicalVar) (sort:=slot))
def sourcePresentation : RootInquiryStatePresentation where
 N := RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.World frame.registered
 V := RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.JointV frame.registered frame.packetAt
 state := .create (state frame configuration)
def targetState := RootGeneratedDebtActivationJointSource.Successor.Inquiry.mathState (old frame configuration)
 (registered frame configuration) (packetAt frame configuration) 0
def targetPresentation : RootInquiryStatePresentation where
 N := RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.World (registered frame configuration)
 V := RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.JointV (registered frame configuration) (packetAt frame configuration)
 state := .create (targetState frame configuration)
theorem literal_next : (generatedAction frame configuration).target.targetAnswerAndNext.nextCurrent=
 ⟨RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.JointV (registered frame configuration) (packetAt frame configuration),
 (targetState frame configuration).root.toAuthoritativeRoot,(targetState frame configuration).visit⟩ :=
 (generatedAction frame configuration).target.targetAnswerAndNext_next_eq
theorem successor_valid : (targetPresentation frame configuration).erase=
 (RootInquiryProcessNode.answered (sourcePresentation frame configuration)
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.query frame configuration)).erase ∧
 (RootInquiryProcessNode.active (sourcePresentation frame configuration)).PreservesGeneratedLivingLawAt
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.query frame configuration)
  (.active (targetPresentation frame configuration)) := by
 apply RootInquiryProcessNode.active_debtAdmission_successor_valid (sourcePresentation frame configuration) (targetPresentation frame configuration)
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.query frame configuration)
  (generatedAction frame configuration) (compiles frame configuration)
 · exact (congrArg (fun target => (⟨RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.World (registered frame configuration),target⟩ : AnyAuthoritativeRootCurrent.{u}))
    (literal_next frame configuration)).symm
 · exact HEq.rfl
theorem whole_first : type_of% (generatedAction frame configuration).target.firstDestination_heq :=
 (generatedAction frame configuration).target.firstDestination_heq
theorem all_old_projection (projection : (old frame configuration).root.toAuthoritativeRoot.source.projectionLaw.Projection) :
 type_of% ((generatedAction frame configuration).target.oldOutcome_heq projection) :=
 (generatedAction frame configuration).target.oldOutcome_heq projection
theorem actual_query_state : (actualMaterial frame configuration).state=
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.resultFace frame configuration).rootRead.2.1 := rfl
theorem actual_updated_environment : (registered frame configuration).input.environment=afterEnvironment frame configuration := add_sub_cancel _ _
theorem source_effect : type_of% (RootGeneratedDebtActivationJointSource.Native.ResidualRequest.updated_value (R:=ℤ) (actualMaterial frame configuration)) :=
 RootGeneratedDebtActivationJointSource.Native.ResidualRequest.updated_value (R:=ℤ) (actualMaterial frame configuration)
theorem source_inverse : type_of% (RootGeneratedDebtActivationJointSource.Native.ResidualRequest.residual_value (R:=ℤ) (actualMaterial frame configuration)) :=
 RootGeneratedDebtActivationJointSource.Native.ResidualRequest.residual_value (R:=ℤ) (actualMaterial frame configuration)
abbrev generated := (sourcePresentation frame configuration,targetPresentation frame configuration,generatedAction frame configuration)
end SourceGeneratedInquiryReceiptAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
