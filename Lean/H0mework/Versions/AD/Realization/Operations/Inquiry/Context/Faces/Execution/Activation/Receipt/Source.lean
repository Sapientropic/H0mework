import H0mework.Versions.AD.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Runtime
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
abbrev old := SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.answeredState frame configuration
abbrev current := (old frame configuration).visit.current
abbrev occurrence := (old frame configuration).root.emitted (current frame configuration)
def afterEnvironment : Env (PairValue PhysicalValue) configuration.LowVar := (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.query
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.next frame configuration) configuration).raw.environment
def material (supplied : (old frame configuration).root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt (current frame configuration)) :
 RootGeneratedDebtActivationJointSource.Native.ResidualRequest.MaterialAt
 (Value:=PairValue PhysicalValue) (Var:=configuration.LowVar) (sort:=slot) supplied :=
 let sourceRaw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
  (Value:=PairValue PhysicalValue) (Var:=configuration.LowVar) (sort:=slot) := (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.datum frame configuration).reader supplied
 { environment:=sourceRaw.environment
   increment:=afterEnvironment frame configuration-sourceRaw.environment
   raw:=sourceRaw.expression
   state:=(SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.resultAt frame configuration supplied).2.1
   owner:=SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.entryAt frame supplied }
def registered := RootGeneratedDebtActivationJointSource.register (fun supplied => RootGeneratedDebtActivationJointSource.Native.ResidualRequest.input (material frame configuration supplied))
abbrev actualMaterial := material frame configuration (occurrence frame configuration)
def packetAt (candidate : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered) :=
 (RootGeneratedDebtActivationJointSource.Successor.read? (old frame configuration).root.toAuthoritativeRoot.toLedgerRoot candidate).get (by rfl)
end SourceGeneratedInquiryReceiptAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
