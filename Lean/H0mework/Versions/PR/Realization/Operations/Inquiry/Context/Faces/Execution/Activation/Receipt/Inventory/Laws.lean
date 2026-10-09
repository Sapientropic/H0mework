import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Inventory.Source
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
theorem bound_environment : (fun sort name => (binding frame configuration occurrence sort name).eval
 (lowRaw frame configuration occurrence).environment)=(physicalRaw frame occurrence).environment := rfl
theorem binding_value : (raw frame configuration occurrence).expression.eval (raw frame configuration occurrence).environment=
 (physicalRaw frame occurrence).expression.eval (physicalRaw frame occurrence).environment :=
 (physicalRaw frame occurrence).expression.eval_subst (binding frame configuration occurrence) (lowRaw frame configuration occurrence).environment
abbrev migratedTrace := (physicalResult frame occurrence).2.1.2.substitutedTrace
 (binding frame configuration occurrence) (lowRaw frame configuration occurrence).environment
theorem query_value : (result frame configuration occurrence).2.2.1=(physicalResult frame occurrence).2.2.1 :=
 (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value _ _ _).trans
  ((binding_value frame configuration occurrence).trans
   (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.base frame).root.toAuthoritativeRoot
    (J.queryReader (seed frame) frame) occurrence).symm)
theorem migrated_boundary : type_of% ((migratedTrace frame configuration occurrence).relation_boundary (R:=ℤ)) :=
 (migratedTrace frame configuration occurrence).relation_boundary (R:=ℤ)
private theorem trace_charge {T : Type u} {A X : T → Type u} [∀ t,AddCommGroup (A t)]
 {t : T} {env : Env A X} {before after : Expr A X t} {value : A t}
 (trace : Trace env before after) (endpoint : after=.const value) : trace.length=remaining before := by
 cases endpoint
 exact trace.length_to_const
theorem migrated_charge : (migratedTrace frame configuration occurrence).length=remaining (raw frame configuration occurrence).expression := by
 have completed : (physicalResult frame occurrence).2.1.1=
  Expr.const (physicalResult frame occurrence).2.2.1 :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.target_expression
   (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.base frame).root.toAuthoritativeRoot current
   (fun _ => physicalRaw frame occurrence)
 exact trace_charge (migratedTrace frame configuration occurrence)
  (congrArg (fun term : Expr (PairValue PhysicalValue) PhysicalVar slot =>
   term.subst (binding frame configuration occurrence)) completed)
def completeWritten := SourceHistoryCommon.seed (written frame configuration occurrence)
 (SourceOperationPaidRelations.exposure (migratedTrace frame configuration occurrence))
def completeMaterial := (material frame configuration occurrence,migratedTrace frame configuration occurrence,
 completeWritten frame configuration occurrence)
end SourceGeneratedInquiryReceiptAction.Inventory
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
