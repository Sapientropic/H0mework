import H0mework.Versions.AE.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Inventory.Born.Coordinates.Actual.Cofinal.Native.Reverse.Action.Cochain.Terms.Next.Future.Query.Pair.Consumer
import H0mework.Versions.AE.Realization.Operations.Inquiry.Context.Native.Pairing.Orbit.Action
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedInquiryReceiptAction.Inventory.Born.Coordinates.Actual.Cofinal.Native.Reverse.Action.Cochain.Terms.Next.Future.Query.Pair.Coimage
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
attribute [local instance] Reverse.valueGroup
variable {S : Type u} {PhysicalValue PhysicalVar : S → Type u}
 [∀ target,AddCommGroup (PhysicalValue target)] {slot : S}
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=slot))
variable (configuration : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
 (PhysicalValue:=PhysicalValue) (PhysicalVar:=PhysicalVar) (sort:=slot))
variable (sourceStage stage count : Nat)
namespace O
export SourceOperationInquiry.Context.Native.Pairing.Orbit (canonical action read wordAction)
end O
def word := Finsupp.single (Query.expression frame configuration sourceStage stage count) (1:ℤ)
def oldClass := O.canonical (Future.runtime frame configuration sourceStage stage) (Future.source frame configuration sourceStage stage)
 (word frame configuration sourceStage stage count)
def nextClass := O.action (Future.runtime frame configuration sourceStage stage) (Future.source frame configuration sourceStage stage)
 (oldClass frame configuration sourceStage stage count)
def expression := (Query.expression frame configuration sourceStage stage count).subst Query.O.binding
def raw := (⟨pairEnvironment (Query.environment frame configuration sourceStage stage count)
 (Query.increment frame configuration sourceStage stage count),liftExpr (expression frame configuration sourceStage stage count)⟩ :
 RootGeneratedDebtActivationJointSource.OwnerFree.Raw)
def material := (Pair.material frame configuration sourceStage stage count,word frame configuration sourceStage stage count,
 oldClass frame configuration sourceStage stage count,nextClass frame configuration sourceStage stage count,raw frame configuration sourceStage stage count)
def component : SourceNativeProjectionLaw (Pair.root frame configuration sourceStage stage count).source.base.restructuringSource.toLedgerSource where
 Projection := PUnit.{u+1}
 ActiveAt := fun _ {_current} _ => PUnit.{u+1}
 InactiveAt := fun _ {_current} _ => PEmpty.{u+1}
 classify := fun _ {_current} _ => .inl PUnit.unit
 PayloadAt := fun _ {_current} _ _ => type_of% (material frame configuration sourceStage stage count)
 project := fun _ {_current} _ _ => material frame configuration sourceStage stage count
def baseRoot := (Pair.root frame configuration sourceStage stage count).withProjectionCoface (component frame configuration sourceStage stage count)
def reader {current : type_of% (Query.original frame configuration sourceStage stage count).visit.current}
 (_supplied : (Query.original frame configuration sourceStage stage count).root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) :=
 ((component frame configuration sourceStage stage count).project PUnit.unit (Query.occurrence frame configuration sourceStage stage count) PUnit.unit).2.2.2.2
def sourceInstallation := SourceNativeProjectionLaw.InstallationAt.componentCoface
 (Pair.root frame configuration sourceStage stage count).source.base (component frame configuration sourceStage stage count)
def sourceFace : SourceNativeRootSemanticFaceAt (baseRoot frame configuration sourceStage stage count)
 (Query.original frame configuration sourceStage stage count).visit where
 projection := (sourceInstallation frame configuration sourceStage stage count).embed PUnit.unit
 active := PUnit.unit
 classifier_eq := rfl
def result := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultAt
 (baseRoot frame configuration sourceStage stage count).toAuthoritativeRoot (reader frame configuration sourceStage stage count)
 (Query.occurrence frame configuration sourceStage stage count)
def queryLaw := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultLaw
 (baseRoot frame configuration sourceStage stage count).toAuthoritativeRoot (reader frame configuration sourceStage stage count)
def root := (baseRoot frame configuration sourceStage stage count).withProjectionCoface (queryLaw frame configuration sourceStage stage count)
def installed := SourceNativeProjectionLaw.InstallationAt.componentCoface
 (baseRoot frame configuration sourceStage stage count).source.base (queryLaw frame configuration sourceStage stage count)
def face : SourceNativeRootSemanticFaceAt (root frame configuration sourceStage stage count)
 (Query.original frame configuration sourceStage stage count).visit where
 projection := (installed frame configuration sourceStage stage count).embed PUnit.unit
 active := PUnit.unit
 classifier_eq := rfl
def queryFrame := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.frame
 (root frame configuration sourceStage stage count) (Query.original frame configuration sourceStage stage count).visit
 (Query.original frame configuration sourceStage stage count).U7 (Query.original frame configuration sourceStage stage count).calculus
 (reader frame configuration sourceStage stage count)
abbrev generated := (Pair.generated frame configuration sourceStage stage count,sourceFace frame configuration sourceStage stage count,
 face frame configuration sourceStage stage count,SourceGeneratedInquiryReceiptAction.actualGenerated
 (queryFrame frame configuration sourceStage stage count) SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme)
end SourceGeneratedInquiryReceiptAction.Inventory.Born.Coordinates.Actual.Cofinal.Native.Reverse.Action.Cochain.Terms.Next.Future.Query.Pair.Coimage
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
