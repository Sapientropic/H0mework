import H0mework.Versions.AE.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Inventory.Born.Coordinates.Actual.Cofinal.Native.Reverse.Action.Cochain.Consumer
import H0mework.Realization.Operations.Execution.Cochain.Inventory
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedInquiryReceiptAction.Inventory.Born.Coordinates.Actual.Cofinal.Native.Reverse.Action.Cochain.Terms
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation CofinalHistorySettlement
attribute [local instance] Reverse.valueGroup
variable {S : Type u} {PhysicalValue PhysicalVar : S → Type u}
 [∀ target,AddCommGroup (PhysicalValue target)] {slot : S}
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=slot))
variable (configuration : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
 (PhysicalValue:=PhysicalValue) (PhysicalVar:=PhysicalVar) (sort:=slot))
variable (sourceStage stage : Nat)
namespace C
export SaturationMonoid.SourceOperationExecution.Cochain.Inventory (Index terms term query environment trace written)
end C
abbrev expression := Action.expression frame configuration sourceStage stage
abbrev Index := C.Index (expression frame configuration sourceStage stage)
def raw := (⟨C.environment (expression frame configuration sourceStage stage)
 (Action.environment frame configuration sourceStage stage) (Action.increment frame configuration sourceStage stage),
 C.query (expression frame configuration sourceStage stage)⟩ : RootGeneratedDebtActivationJointSource.OwnerFree.Raw)
abbrev trace := C.trace (expression frame configuration sourceStage stage)
 (Action.environment frame configuration sourceStage stage) (Action.increment frame configuration sourceStage stage)
def material := (Cochain.material frame configuration sourceStage stage,
 C.terms (expression frame configuration sourceStage stage),trace frame configuration sourceStage stage,
 raw frame configuration sourceStage stage)
def component : SourceNativeProjectionLaw
 (Cochain.queryRoot frame configuration sourceStage stage).source.base.restructuringSource.toLedgerSource where
 Projection := PUnit.{u+1}
 ActiveAt := fun _ {_current} _ => PUnit.{u+1}
 InactiveAt := fun _ {_current} _ => PEmpty.{u+1}
 classify := fun _ {_current} _ => .inl PUnit.unit
 PayloadAt := fun _ {_current} _ _ => type_of% (material frame configuration sourceStage stage)
 project := fun _ {_current} _ _ => material frame configuration sourceStage stage
def baseRoot := (Cochain.queryRoot frame configuration sourceStage stage).withProjectionCoface (component frame configuration sourceStage stage)
def reader {current : type_of% (Reverse.original frame configuration sourceStage stage).visit.current}
 (_supplied : (Reverse.original frame configuration sourceStage stage).root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) :=
 ((component frame configuration sourceStage stage).project PUnit.unit (Reverse.occurrence frame configuration sourceStage stage) PUnit.unit).2.2.2
def sourceInstallation := SourceNativeProjectionLaw.InstallationAt.componentCoface
 (Cochain.queryRoot frame configuration sourceStage stage).source.base (component frame configuration sourceStage stage)
def sourceFace : SourceNativeRootSemanticFaceAt (baseRoot frame configuration sourceStage stage)
 (Reverse.original frame configuration sourceStage stage).visit where
 projection := (sourceInstallation frame configuration sourceStage stage).embed PUnit.unit
 active := PUnit.unit
 classifier_eq := rfl
def result := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultAt
 (baseRoot frame configuration sourceStage stage).toAuthoritativeRoot (reader frame configuration sourceStage stage)
 (Reverse.occurrence frame configuration sourceStage stage)
def queryLaw := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultLaw
 (baseRoot frame configuration sourceStage stage).toAuthoritativeRoot (reader frame configuration sourceStage stage)
def queryRoot := (baseRoot frame configuration sourceStage stage).withProjectionCoface (queryLaw frame configuration sourceStage stage)
def installed := SourceNativeProjectionLaw.InstallationAt.componentCoface
 (baseRoot frame configuration sourceStage stage).source.base (queryLaw frame configuration sourceStage stage)
def queryFace : SourceNativeRootSemanticFaceAt (queryRoot frame configuration sourceStage stage)
 (Reverse.original frame configuration sourceStage stage).visit where
 projection := (installed frame configuration sourceStage stage).embed PUnit.unit
 active := PUnit.unit
 classifier_eq := rfl
def expressionFrame := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.frame
 (queryRoot frame configuration sourceStage stage) (Reverse.original frame configuration sourceStage stage).visit
 (Reverse.original frame configuration sourceStage stage).U7 (Reverse.original frame configuration sourceStage stage).calculus
 (reader frame configuration sourceStage stage)
def queryFrame := {expressionFrame frame configuration sourceStage stage with
 inventory:=some (C.written (expression frame configuration sourceStage stage)
  (Action.environment frame configuration sourceStage stage) (Action.increment frame configuration sourceStage stage))}
abbrev generated := (Cochain.generated frame configuration sourceStage stage,sourceFace frame configuration sourceStage stage,
 queryFace frame configuration sourceStage stage,Inventory.Born.generated (queryFrame frame configuration sourceStage stage)
 SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme)
end SourceGeneratedInquiryReceiptAction.Inventory.Born.Coordinates.Actual.Cofinal.Native.Reverse.Action.Cochain.Terms
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
