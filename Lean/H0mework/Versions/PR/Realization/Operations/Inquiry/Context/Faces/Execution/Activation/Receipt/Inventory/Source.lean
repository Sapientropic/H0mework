import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Runtime
import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Inventory.Pair.Residual.Joint.Consumer
import H0mework.Realization.Operations.Execution.Substitution.Source
import Lean.LibrarySuggestions.Basic
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "SourceGeneratedInquiryReceiptAction"
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedInquiryReceiptAction.Inventory
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open CofinalHistorySettlement SourceOperationScalarRelations SourceOperationScalarPresentation
variable {S : Type u} {PhysicalValue PhysicalVar : S → Type u}
 [∀ target,AddCommGroup (PhysicalValue target)] {slot : S}
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=slot))
variable (configuration : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
 (PhysicalValue:=PhysicalValue) (PhysicalVar:=PhysicalVar) (sort:=slot))
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
variable (occurrence : SourceOperationInquiry.Context.Installation.Occurrence frame (current:=current))
namespace J
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint
 (material queryReader queryResult completeWrittenInventory disposition)
end J
abbrev seed := RootedAccountedUnfolding.zero (PresentedRelationEventAt.generator frame.registered.input.expression)
abbrev original := J.material (seed frame) frame occurrence
abbrev physicalRaw := J.queryReader (seed frame) frame occurrence
abbrev physicalResult := J.queryResult (seed frame) frame occurrence
abbrev lowRaw := (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.datum frame configuration).reader occurrence
abbrev lowResult := SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.resultAt frame configuration occurrence
def binding (sort : S) (name : PhysicalVar sort) : Expr (PairValue PhysicalValue) configuration.LowVar sort :=
 .const ((physicalRaw frame occurrence).environment sort name)
def raw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
 (Value:=PairValue PhysicalValue) (Var:=configuration.LowVar) (sort:=slot) :=
 ⟨(lowRaw frame configuration occurrence).environment,(physicalRaw frame occurrence).expression.subst (binding frame configuration occurrence)⟩
def reader {sourceCurrent : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
 (supplied : SourceOperationInquiry.Context.Installation.Occurrence frame (current:=sourceCurrent)) := raw frame configuration supplied
abbrev physicalWritten := J.completeWrittenInventory (seed frame) frame occurrence
def result {sourceCurrent : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
 (supplied : SourceOperationInquiry.Context.Installation.Occurrence frame (current:=sourceCurrent)) :=
 RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultAt
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.base frame).root.toAuthoritativeRoot (reader frame configuration) supplied
def written := SourceHistoryCommon.seed (SourceOperationPaidRelations.exposure (lowResult frame configuration occurrence).2.1.2)
 (SourceOperationPaidRelations.exposure (result frame configuration occurrence).2.1.2)
def material := (original frame occurrence,physicalWritten frame occurrence,physicalRaw frame occurrence,physicalResult frame occurrence,
 lowRaw frame configuration occurrence,lowResult frame configuration occurrence,binding frame configuration occurrence,
 raw frame configuration occurrence,result frame configuration occurrence,written frame configuration occurrence)
end SourceGeneratedInquiryReceiptAction.Inventory
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
