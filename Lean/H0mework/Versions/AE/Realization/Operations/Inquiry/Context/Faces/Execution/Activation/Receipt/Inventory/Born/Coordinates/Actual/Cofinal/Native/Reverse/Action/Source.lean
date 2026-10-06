import H0mework.Versions.AE.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Inventory.Born.Coordinates.Actual.Cofinal.Native.Reverse.Consumer
import H0mework.Versions.AE.Realization.Operations.Inquiry.Context.Native.Orbit.Pair.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedInquiryReceiptAction.Inventory.Born.Coordinates.Actual.Cofinal.Native.Reverse.Action
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation SourceGeneratedScalarDifferentialResidual
attribute [local instance] Reverse.valueGroup
variable {S : Type u} {PhysicalValue PhysicalVar : S → Type u}
 [∀ target,AddCommGroup (PhysicalValue target)] {slot : S}
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=slot))
variable (configuration : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
 (PhysicalValue:=PhysicalValue) (PhysicalVar:=PhysicalVar) (sort:=slot))
variable (sourceStage stage : Nat)
namespace P
export SourceOperationInquiry.Context.Native.Orbit.Pair (environment embedding embeddedTrace binding_point binding_difference)
end P
namespace O
export SourceOperationInquiry.Context.Native.Orbit (binding)
end O
abbrev state := Reverse.stateAt frame configuration sourceStage stage
def environment := P.environment (Reverse.runtime frame configuration sourceStage)
 (Reverse.source frame configuration sourceStage) (SourceOperationInquiry.point _ (state frame configuration sourceStage stage))
def increment := P.environment (Reverse.runtime frame configuration sourceStage)
 (Reverse.source frame configuration sourceStage) (SourceOperationInquiry.point _ (state frame configuration sourceStage stage).tick.nextState-
 SourceOperationInquiry.point _ (state frame configuration sourceStage stage))
def expression := (Reverse.raw frame configuration sourceStage stage).expression.subst P.embedding
abbrev trace := P.embeddedTrace (Reverse.runtime frame configuration sourceStage)
 (Reverse.source frame configuration sourceStage) (state frame configuration sourceStage stage)
 (Reverse.result frame configuration sourceStage stage).2.1.2
def relations := (trace frame configuration sourceStage stage).relationWords (R:=ℤ)
def boundary := relationMap (R:=ℤ) (environment frame configuration sourceStage stage)
 (relations frame configuration sourceStage stage)
def nextEvaluation := evaluation (R:=ℤ) (s:=slot) (P.environment (Reverse.runtime frame configuration sourceStage)
 (Reverse.source frame configuration sourceStage)
 (SourceOperationInquiry.point _ (state frame configuration sourceStage stage).tick.nextState))
def inverse := canonicalResidual (nextEvaluation frame configuration sourceStage stage)
 (boundary frame configuration sourceStage stage)
def sourceExpression := SourceOperationExecution.Coefficients.expression (boundary frame configuration sourceStage stage)
def nextExpression := (sourceExpression frame configuration sourceStage stage).subst O.binding
def raw := (⟨pairEnvironment (environment frame configuration sourceStage stage) (increment frame configuration sourceStage stage),
 liftExpr (nextExpression frame configuration sourceStage stage)⟩ : RootGeneratedDebtActivationJointSource.OwnerFree.Raw)
def material := (Reverse.material frame configuration sourceStage stage,trace frame configuration sourceStage stage,
 relations frame configuration sourceStage stage,boundary frame configuration sourceStage stage,
 inverse frame configuration sourceStage stage,raw frame configuration sourceStage stage)
def component : SourceNativeProjectionLaw
 (Reverse.original frame configuration sourceStage stage).root.source.base.restructuringSource.toLedgerSource where
 Projection := PUnit.{u+1}
 ActiveAt := fun _ {_current} _ => PUnit.{u+1}
 InactiveAt := fun _ {_current} _ => PEmpty.{u+1}
 classify := fun _ {_current} _ => .inl PUnit.unit
 PayloadAt := fun _ {_current} _ _ => type_of% (material frame configuration sourceStage stage)
 project := fun _ {_current} _ _ => material frame configuration sourceStage stage
def baseRoot := (Reverse.original frame configuration sourceStage stage).root.withProjectionCoface
 (component frame configuration sourceStage stage)
def reader {current : type_of% (Reverse.original frame configuration sourceStage stage).visit.current}
 (_supplied : (Reverse.original frame configuration sourceStage stage).root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) :=
 ((component frame configuration sourceStage stage).project PUnit.unit (Reverse.occurrence frame configuration sourceStage stage) PUnit.unit).2.2.2.2.2
def sourceInstallation := SourceNativeProjectionLaw.InstallationAt.componentCoface
 (Reverse.original frame configuration sourceStage stage).root.source.base (component frame configuration sourceStage stage)
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
def queryFrame := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.frame
 (queryRoot frame configuration sourceStage stage) (Reverse.original frame configuration sourceStage stage).visit
 (Reverse.original frame configuration sourceStage stage).U7 (Reverse.original frame configuration sourceStage stage).calculus
 (reader frame configuration sourceStage stage)
abbrev generated := (Reverse.generated frame configuration sourceStage stage,sourceFace frame configuration sourceStage stage,
 queryFace frame configuration sourceStage stage,SourceGeneratedInquiryReceiptAction.actualGenerated
 (queryFrame frame configuration sourceStage stage) SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme)
end SourceGeneratedInquiryReceiptAction.Inventory.Born.Coordinates.Actual.Cofinal.Native.Reverse.Action
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
