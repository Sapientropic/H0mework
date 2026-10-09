import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Inventory.Born.Coordinates.Actual.Cofinal.Native.Reverse.Action.Cochain.Terms.Next.Future.Consumer
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedInquiryReceiptAction.Inventory.Born.Coordinates.Actual.Cofinal.Native.Reverse.Action.Cochain.Terms.Next.Future.Query
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation
attribute [local instance] Reverse.valueGroup
variable {S : Type u} {PhysicalValue PhysicalVar : S → Type u}
 [∀ target,AddCommGroup (PhysicalValue target)] {slot : S}
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=slot))
variable (configuration : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
 (PhysicalValue:=PhysicalValue) (PhysicalVar:=PhysicalVar) (sort:=slot))
variable (sourceStage stage count : Nat)
namespace O
export SourceOperationInquiry.Context.Native.Orbit (Var embed binding environment)
end O
abbrev state := (Future.runtime frame configuration sourceStage stage).stateAt count
abbrev original := SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.state
 (Future.frameAt frame configuration sourceStage stage count) (Future.consumer frame configuration sourceStage stage)
abbrev occurrence := original frame configuration sourceStage stage count |>.root.emitted
 (original frame configuration sourceStage stage count).visit.current
def expression := (O.embed (Coefficients.expression (Future.word frame configuration sourceStage stage count))).subst O.binding
def environment := O.environment (Future.runtime frame configuration sourceStage stage) (Future.source frame configuration sourceStage stage)
 (SourceOperationInquiry.point _ (state frame configuration sourceStage stage count))
def increment := O.environment (Future.runtime frame configuration sourceStage stage) (Future.source frame configuration sourceStage stage)
 (SourceOperationInquiry.point _ (state frame configuration sourceStage stage count).tick.nextState-
 SourceOperationInquiry.point _ (state frame configuration sourceStage stage count))
def raw := (⟨pairEnvironment (environment frame configuration sourceStage stage count) (increment frame configuration sourceStage stage count),
 liftExpr (expression frame configuration sourceStage stage count)⟩ : RootGeneratedDebtActivationJointSource.OwnerFree.Raw)
def material := (Future.word frame configuration sourceStage stage count,Future.relationField frame configuration sourceStage stage count,
 Future.witness frame configuration sourceStage stage count,raw frame configuration sourceStage stage count)
def component : SourceNativeProjectionLaw
 (original frame configuration sourceStage stage count).root.source.base.restructuringSource.toLedgerSource where
 Projection := PUnit.{u+1}
 ActiveAt := fun _ {_current} _ => PUnit.{u+1}
 InactiveAt := fun _ {_current} _ => PEmpty.{u+1}
 classify := fun _ {_current} _ => .inl PUnit.unit
 PayloadAt := fun _ {_current} _ _ => type_of% (material frame configuration sourceStage stage count)
 project := fun _ {_current} _ _ => material frame configuration sourceStage stage count
def baseRoot := (original frame configuration sourceStage stage count).root.withProjectionCoface
 (component frame configuration sourceStage stage count)
def reader {current : type_of% (original frame configuration sourceStage stage count).visit.current}
 (_supplied : (original frame configuration sourceStage stage count).root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) :=
 ((component frame configuration sourceStage stage count).project PUnit.unit (occurrence frame configuration sourceStage stage count) PUnit.unit).2.2.2
def sourceInstallation := SourceNativeProjectionLaw.InstallationAt.componentCoface
 (original frame configuration sourceStage stage count).root.source.base (component frame configuration sourceStage stage count)
def sourceFace : SourceNativeRootSemanticFaceAt (baseRoot frame configuration sourceStage stage count)
 (original frame configuration sourceStage stage count).visit where
 projection := (sourceInstallation frame configuration sourceStage stage count).embed PUnit.unit
 active := PUnit.unit
 classifier_eq := rfl
def result := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultAt
 (baseRoot frame configuration sourceStage stage count).toAuthoritativeRoot (reader frame configuration sourceStage stage count)
 (occurrence frame configuration sourceStage stage count)
def queryLaw := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultLaw
 (baseRoot frame configuration sourceStage stage count).toAuthoritativeRoot (reader frame configuration sourceStage stage count)
def queryRoot := (baseRoot frame configuration sourceStage stage count).withProjectionCoface (queryLaw frame configuration sourceStage stage count)
def installed := SourceNativeProjectionLaw.InstallationAt.componentCoface
 (baseRoot frame configuration sourceStage stage count).source.base (queryLaw frame configuration sourceStage stage count)
def queryFace : SourceNativeRootSemanticFaceAt (queryRoot frame configuration sourceStage stage count)
 (original frame configuration sourceStage stage count).visit where
 projection := (installed frame configuration sourceStage stage count).embed PUnit.unit
 active := PUnit.unit
 classifier_eq := rfl
def queryFrame := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.frame
 (queryRoot frame configuration sourceStage stage count) (original frame configuration sourceStage stage count).visit
 (original frame configuration sourceStage stage count).U7 (original frame configuration sourceStage stage count).calculus
 (reader frame configuration sourceStage stage count)
abbrev generated := (Future.generated frame configuration sourceStage stage,sourceFace frame configuration sourceStage stage count,
 queryFace frame configuration sourceStage stage count,SourceGeneratedInquiryReceiptAction.actualGenerated
 (queryFrame frame configuration sourceStage stage count) SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme)
end SourceGeneratedInquiryReceiptAction.Inventory.Born.Coordinates.Actual.Cofinal.Native.Reverse.Action.Cochain.Terms.Next.Future.Query
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
