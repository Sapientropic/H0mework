import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Inventory.Born.Coordinates.Actual.Consumer
import H0mework.Versions.AD.Realization.Operations.Inquiry.Context.Faces.Cofinal.Consumer
import H0mework.Versions.R2.Realization.Operations.Inquiry.Context.Native.Orbit.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedInquiryReceiptAction.Inventory.Born.Coordinates.Actual.Cofinal
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation
variable {S : Type u} {PhysicalValue PhysicalVar : S → Type u}
 [∀ target,AddCommGroup (PhysicalValue target)] {slot : S}
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=slot))
variable (configuration : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
 (PhysicalValue:=PhysicalValue) (PhysicalVar:=PhysicalVar) (sort:=slot))
abbrev initial := SourceGeneratedInquiryReceiptAction.bornFrame (Actual.queryFrame frame configuration)
 SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme
abbrev runtime := SourceGeneratedInquiryReceiptAction.runtime (Actual.queryFrame frame configuration)
 SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme
abbrev source := SourceOperationInquiry.Context.Installation.rawSource (initial frame configuration)
abbrev frameAt (stage : Nat) := RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.frames (initial frame configuration) stage
abbrev stateAt (stage : Nat) := (runtime frame configuration).stateAt stage
abbrev original (stage : Nat) := (frameAt frame configuration stage).currentState
abbrev occurrence (stage : Nat) := (original frame configuration stage).root.emitted (original frame configuration stage).visit.current
namespace C
export SourceOperationInquiry.Context.Faces.Cofinal (relationAt relationField relationWitness sourceMap next)
end C
namespace O
export SourceOperationInquiry.Context.Native.Orbit (Var embed binding environment)
end O
abbrev relationWord (stage : Nat) := C.relationAt (runtime frame configuration) (source frame configuration) stage
abbrev field (stage : Nat) := C.relationField (runtime frame configuration) (source frame configuration) stage
abbrev witness (stage : Nat) := C.relationWitness (runtime frame configuration) (source frame configuration) stage
def expression (stage : Nat) :=
 (O.embed (SourceOperationExecution.Coefficients.expression (relationWord frame configuration stage))).subst O.binding
abbrev environment (stage : Nat) := O.environment (runtime frame configuration) (source frame configuration)
 (SourceOperationInquiry.point (runtime frame configuration) (stateAt frame configuration stage))
abbrev increment (stage : Nat) := O.environment (runtime frame configuration) (source frame configuration)
 (SourceOperationInquiry.point (runtime frame configuration) (stateAt frame configuration stage).tick.nextState-
  SourceOperationInquiry.point (runtime frame configuration) (stateAt frame configuration stage))
def raw (stage : Nat) : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
 (Value:=PairValue (PairValue (SaturationMonoid.SourceOperationExecution.InventoryVector.VectorValue
   (Actual.ActualIndex frame configuration) (Value:=PairValue (PairValue PhysicalValue)))))
 (Var:=O.Var configuration.LowVar) (sort:=slot) :=
 ⟨pairEnvironment (environment frame configuration stage) (increment frame configuration stage),
  liftExpr (expression frame configuration stage)⟩
def material (stage : Nat) := (relationWord frame configuration stage,field frame configuration stage,
 witness frame configuration stage,raw frame configuration stage)
def component (stage : Nat) : SourceNativeProjectionLaw
 (original frame configuration stage).root.source.base.restructuringSource.toLedgerSource where
 Projection := PUnit.{u+1}
 ActiveAt := fun _ {_current} _ => PUnit.{u+1}
 InactiveAt := fun _ {_current} _ => PEmpty.{u+1}
 classify := fun _ {_current} _ => .inl PUnit.unit
 PayloadAt := fun _ {_current} _ _ => type_of% (material frame configuration stage)
 project := fun _ {_current} _ _ => material frame configuration stage
def baseRoot (stage : Nat) := (original frame configuration stage).root.withProjectionCoface (component frame configuration stage)
def reader (stage : Nat) {current : type_of% (original frame configuration stage).visit.current}
 (_supplied : (original frame configuration stage).root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) :=
 ((component frame configuration stage).project PUnit.unit (occurrence frame configuration stage) PUnit.unit).2.2.2
def sourceInstallation (stage : Nat) := SourceNativeProjectionLaw.InstallationAt.componentCoface
 (original frame configuration stage).root.source.base (component frame configuration stage)
def sourceFace (stage : Nat) : SourceNativeRootSemanticFaceAt (baseRoot frame configuration stage) (original frame configuration stage).visit where
 projection := (sourceInstallation frame configuration stage).embed PUnit.unit
 active := PUnit.unit
 classifier_eq := rfl
def result (stage : Nat) := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultAt
 (baseRoot frame configuration stage).toAuthoritativeRoot (reader frame configuration stage) (occurrence frame configuration stage)
def queryLaw (stage : Nat) := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultLaw
 (baseRoot frame configuration stage).toAuthoritativeRoot (reader frame configuration stage)
def queryRoot (stage : Nat) := (baseRoot frame configuration stage).withProjectionCoface (queryLaw frame configuration stage)
def installed (stage : Nat) := SourceNativeProjectionLaw.InstallationAt.componentCoface
 (baseRoot frame configuration stage).source.base (queryLaw frame configuration stage)
def queryFace (stage : Nat) : SourceNativeRootSemanticFaceAt (queryRoot frame configuration stage) (original frame configuration stage).visit where
 projection := (installed frame configuration stage).embed PUnit.unit
 active := PUnit.unit
 classifier_eq := rfl
def queryFrame (stage : Nat) := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.frame
 (queryRoot frame configuration stage) (original frame configuration stage).visit
 (original frame configuration stage).U7 (original frame configuration stage).calculus (reader frame configuration stage)
abbrev generated (stage : Nat) := (Actual.generated frame configuration,sourceFace frame configuration stage,queryFace frame configuration stage,
 SourceGeneratedInquiryReceiptAction.actualGenerated (queryFrame frame configuration stage)
  SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme)
end SourceGeneratedInquiryReceiptAction.Inventory.Born.Coordinates.Actual.Cofinal
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
