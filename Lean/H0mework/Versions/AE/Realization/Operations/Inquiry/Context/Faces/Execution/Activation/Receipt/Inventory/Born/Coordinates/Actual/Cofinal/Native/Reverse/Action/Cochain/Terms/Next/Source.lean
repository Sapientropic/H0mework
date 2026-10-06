import H0mework.Versions.AE.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Inventory.Born.Coordinates.Actual.Cofinal.Native.Reverse.Action.Cochain.Terms.Consumer
import H0mework.Versions.AE.Realization.Operations.Inquiry.Context.Native.Orbit.Pair.Mixed
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedInquiryReceiptAction.Inventory.Born.Coordinates.Actual.Cofinal.Native.Reverse.Action.Cochain.Terms.Next
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
namespace M
export SourceOperationInquiry.Context.Native.Orbit.Pair.Mixed (environment vectorBinding vector_next)
end M
abbrev Index := Terms.Index frame configuration sourceStage stage
abbrev nextState := (Action.state frame configuration sourceStage stage).tick.nextState
def environment := SourceOperationExecution.InventoryVector.environment (Index frame configuration sourceStage stage)
 (M.environment (Reverse.runtime frame configuration sourceStage) (Reverse.source frame configuration sourceStage)
  (Action.state frame configuration sourceStage stage))
def nextEnvironment := SourceOperationExecution.InventoryVector.environment (Index frame configuration sourceStage stage)
 (M.environment (Reverse.runtime frame configuration sourceStage) (Reverse.source frame configuration sourceStage)
  (nextState frame configuration sourceStage stage))
def binding : ∀ target,ChangedVar (SourceOperationInquiry.Context.Native.Orbit.Var (SourceOperationInquiry.Context.Native.Orbit.Var
   (SourceOperationInquiry.Context.Native.Orbit.Var configuration.LowVar))) target →
 Expr (InventoryVector.VectorValue (Index frame configuration sourceStage stage) (Value:=Reverse.Value frame configuration))
  (ChangedVar (SourceOperationInquiry.Context.Native.Orbit.Var (SourceOperationInquiry.Context.Native.Orbit.Var
   (SourceOperationInquiry.Context.Native.Orbit.Var configuration.LowVar)))) target :=
 fun _ name => .var ((name.1.1+1,name.1.2),name.2)
def raw := (⟨environment frame configuration sourceStage stage,
 (Terms.raw frame configuration sourceStage stage).expression.subst (binding frame configuration sourceStage stage)⟩ :
 RootGeneratedDebtActivationJointSource.OwnerFree.Raw)
def inverse := SourceGeneratedScalarDifferentialResidual.canonicalResidual
 (evaluation (R:=ℤ) (s:=slot) (nextEnvironment frame configuration sourceStage stage))
 (Finsupp.single (Terms.raw frame configuration sourceStage stage).expression 1)
def material := (Terms.material frame configuration sourceStage stage,
 binding frame configuration sourceStage stage,inverse frame configuration sourceStage stage,raw frame configuration sourceStage stage)
def component : SourceNativeProjectionLaw
 (Terms.queryRoot frame configuration sourceStage stage).source.base.restructuringSource.toLedgerSource where
 Projection := PUnit.{u+1}
 ActiveAt := fun _ {_current} _ => PUnit.{u+1}
 InactiveAt := fun _ {_current} _ => PEmpty.{u+1}
 classify := fun _ {_current} _ => .inl PUnit.unit
 PayloadAt := fun _ {_current} _ _ => type_of% (material frame configuration sourceStage stage)
 project := fun _ {_current} _ _ => material frame configuration sourceStage stage
def baseRoot := (Terms.queryRoot frame configuration sourceStage stage).withProjectionCoface (component frame configuration sourceStage stage)
def reader {current : type_of% (Reverse.original frame configuration sourceStage stage).visit.current}
 (_supplied : (Reverse.original frame configuration sourceStage stage).root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) :=
 ((component frame configuration sourceStage stage).project PUnit.unit (Reverse.occurrence frame configuration sourceStage stage) PUnit.unit).2.2.2
def sourceInstallation := SourceNativeProjectionLaw.InstallationAt.componentCoface
 (Terms.queryRoot frame configuration sourceStage stage).source.base (component frame configuration sourceStage stage)
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
 inventory:=some (SourceOperationPaidRelations.exposure (result frame configuration sourceStage stage).2.1.2)}
abbrev generated := (Terms.generated frame configuration sourceStage stage,sourceFace frame configuration sourceStage stage,
 queryFace frame configuration sourceStage stage,Inventory.Born.generated (queryFrame frame configuration sourceStage stage)
 SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme)
end SourceGeneratedInquiryReceiptAction.Inventory.Born.Coordinates.Actual.Cofinal.Native.Reverse.Action.Cochain.Terms.Next
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
