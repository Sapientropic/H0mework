import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Consumer
import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Successor.Inquiry.Target
import H0mework.Versions.AD.Foundation.Responsibility.JointSource.Successor.Inquiry.Continuation.Payment
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
def bornFrame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=PairValue PhysicalValue) (Var:=configuration.LowVar) (sort:=slot) where
 N := RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.World frame.registered
 V := RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.JointV frame.registered frame.packetAt
 old := old frame configuration
 registered := registered frame configuration
 packetAt := packetAt frame configuration
 environment := fun {_current} supplied => ((SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.datum frame configuration).reader supplied).environment
 depth := 0
 inventory := some (SourceOperationPaidRelations.exposure (actualMaterial frame configuration).state.2)
abbrev runtime := RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.runtime (bornFrame frame configuration)
theorem born_current : (bornFrame frame configuration).currentState=targetState frame configuration := rfl
theorem born_inventory : (bornFrame frame configuration).inventory=
 some (SourceOperationPaidRelations.exposure (actualMaterial frame configuration).state.2) := rfl
theorem runtime_current : (runtime frame configuration).initialState.engine.node.erase=(targetPresentation frame configuration).erase :=
 RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.actual_current (bornFrame frame configuration) 0
theorem runtime_next (stage : Nat) : type_of%
 (RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.macro_next (bornFrame frame configuration) stage) :=
 RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.macro_next (bornFrame frame configuration) stage
theorem runtime_preserves (stage : Nat) : type_of%
 (RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.macro_next_preserves (bornFrame frame configuration) stage) :=
 RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.macro_next_preserves (bornFrame frame configuration) stage
theorem no_refill : type_of%
 (RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Payment.no_refill (bornFrame frame configuration)) :=
 RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Payment.no_refill (bornFrame frame configuration)
theorem noetherian : type_of%
 (RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Payment.continuation_wellFounded (bornFrame frame configuration)) :=
 RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Payment.continuation_wellFounded (bornFrame frame configuration)
abbrev actualGenerated := (generated frame configuration,runtime frame configuration)
end SourceGeneratedInquiryReceiptAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
