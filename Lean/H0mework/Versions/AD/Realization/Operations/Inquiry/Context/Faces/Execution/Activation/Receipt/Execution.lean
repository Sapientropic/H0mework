import H0mework.Versions.AD.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Source
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
private theorem not_settled (settled : SourceOperationExecutionDebt.Settlement
 (RootGeneratedDebtActivationJointSource.initialEvent (registered frame configuration)).state) : False := by
 have zero := (RootGeneratedDebtActivationJointSource.Idle.law (registered frame configuration).input.environment
  (registered frame configuration).input.expression).settlement_budget_zero settled
 have sourceBudget := RootGeneratedDebtActivationJointSource.Native.ResidualRequest.budget (actualMaterial frame configuration)
 change remaining (RootGeneratedDebtActivationJointSource.Native.ResidualRequest.expression (actualMaterial frame configuration))=0 at zero
 omega
def firstStep := match _selected : RootGeneratedDebtActivationJointSource.mathAction
 (RootGeneratedDebtActivationJointSource.initialEvent (registered frame configuration)) with
 | .inl settled => False.elim (not_settled frame configuration settled)
 | .inr paid => paid
theorem first_action : RootGeneratedDebtActivationJointSource.Successor.Inquiry.sourceAction
 (old frame configuration) (registered frame configuration) (packetAt frame configuration)=.inr (firstStep frame configuration) := by
 apply (RootGeneratedDebtActivationJointSource.Successor.Inquiry.sourceAction_eq (old frame configuration) (registered frame configuration) (packetAt frame configuration)).trans
 unfold firstStep
 cases selected : RootGeneratedDebtActivationJointSource.mathAction (RootGeneratedDebtActivationJointSource.initialEvent (registered frame configuration)) with
 | inl settled => exact False.elim (not_settled frame configuration settled)
 | inr paid => rfl
def birthProgram := RootGeneratedDebtActivationJointSource.Successor.Inquiry.birthProgram
 (old frame configuration) (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.query frame configuration) (registered frame configuration) (packetAt frame configuration)
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.authority frame configuration)
 (firstStep frame configuration) (first_action frame configuration)
def sourceEvent := (old frame configuration).root.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt (old frame configuration).visit
def generatedAction := (birthProgram frame configuration).generate (sourceEvent frame configuration)
end SourceGeneratedInquiryReceiptAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
