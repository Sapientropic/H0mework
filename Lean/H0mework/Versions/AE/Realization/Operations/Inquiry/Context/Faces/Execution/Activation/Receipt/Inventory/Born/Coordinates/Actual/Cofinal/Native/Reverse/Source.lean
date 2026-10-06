import H0mework.Versions.AE.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Inventory.Born.Coordinates.Actual.Cofinal.Native.Consumer
import H0mework.Versions.AD.Realization.Operations.Inquiry.Context.Faces.Reverse.Consumer
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedInquiryReceiptAction.Inventory.Born.Coordinates.Actual.Cofinal.Native.Reverse
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation
variable {S : Type u} {PhysicalValue PhysicalVar : S → Type u}
 [∀ target,AddCommGroup (PhysicalValue target)] {slot : S}
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=slot))
variable (configuration : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
 (PhysicalValue:=PhysicalValue) (PhysicalVar:=PhysicalVar) (sort:=slot))
variable (sourceStage : Nat)
abbrev Value := PairValue (PairValue (PairValue (PairValue
 (SaturationMonoid.SourceOperationExecution.InventoryVector.VectorValue (Actual.ActualIndex frame configuration)
  (Value:=PairValue (PairValue PhysicalValue))))))
local instance valueGroup : ∀ sort,AddCommGroup (Value frame configuration sort) := fun target => by
 letI : AddCommGroup (PhysicalValue target) := (inferInstance : ∀ sort,AddCommGroup (PhysicalValue sort)) target
 letI : AddCommGroup (PairValue PhysicalValue target) := Prod.instAddCommGroup
 letI : AddCommGroup (PairValue (PairValue PhysicalValue) target) := Prod.instAddCommGroup
 letI : AddCommGroup (SaturationMonoid.SourceOperationExecution.InventoryVector.VectorValue
   (Actual.ActualIndex frame configuration) (Value:=PairValue (PairValue PhysicalValue)) target) := inferInstance
 letI : AddCommGroup (PairValue (SaturationMonoid.SourceOperationExecution.InventoryVector.VectorValue
   (Actual.ActualIndex frame configuration) (Value:=PairValue (PairValue PhysicalValue))) target) := Prod.instAddCommGroup
 letI : AddCommGroup (PairValue (PairValue (SaturationMonoid.SourceOperationExecution.InventoryVector.VectorValue
   (Actual.ActualIndex frame configuration) (Value:=PairValue (PairValue PhysicalValue)))) target) := Prod.instAddCommGroup
 letI : AddCommGroup (PairValue (PairValue (PairValue (SaturationMonoid.SourceOperationExecution.InventoryVector.VectorValue
   (Actual.ActualIndex frame configuration) (Value:=PairValue (PairValue PhysicalValue))))) target) := Prod.instAddCommGroup
 exact Prod.instAddCommGroup
abbrev initial := SourceGeneratedInquiryReceiptAction.bornFrame (Native.nativeFrame frame configuration sourceStage) R.programme
abbrev runtime := SourceGeneratedInquiryReceiptAction.runtime (Native.nativeFrame frame configuration sourceStage) R.programme
abbrev source := SourceOperationInquiry.Context.Installation.rawSource (initial frame configuration sourceStage)
abbrev frameAt (stage : Nat) := RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.frames
 (initial frame configuration sourceStage) stage
abbrev stateAt (stage : Nat) := (runtime frame configuration sourceStage).stateAt stage
abbrev original (stage : Nat) := (frameAt frame configuration sourceStage stage).currentState
abbrev occurrence (stage : Nat) := (original frame configuration sourceStage stage).root.emitted
 (original frame configuration sourceStage stage).visit.current
namespace F
export SourceOperationInquiry.Context.Faces (recover pairInventory)
end F
namespace B
export SourceOperationInquiry.Context.Faces.Reverse (oldWord nextWord target reverse retainedTarget)
end B
def word (stage : Nat) := B.nextWord (runtime frame configuration sourceStage) (source frame configuration sourceStage)
 (stateAt frame configuration sourceStage stage)
def raw (stage : Nat) := {SourceOperationInquiry.Context.Faces.Execution.pairRaw
 (runtime frame configuration sourceStage) (source frame configuration sourceStage)
 (stateAt frame configuration sourceStage stage) (word frame configuration sourceStage stage) with
 expression:=liftExpr (SourceOperationExecution.Coefficients.expression (word frame configuration sourceStage stage))}
def material (stage : Nat) := (B.target (runtime frame configuration sourceStage) (source frame configuration sourceStage)
 (stateAt frame configuration sourceStage stage),B.reverse (runtime frame configuration sourceStage) (source frame configuration sourceStage)
 (stateAt frame configuration sourceStage stage),B.retainedTarget (runtime frame configuration sourceStage) (source frame configuration sourceStage)
 (stateAt frame configuration sourceStage stage),word frame configuration sourceStage stage,raw frame configuration sourceStage stage)
def component (stage : Nat) : SourceNativeProjectionLaw
 (original frame configuration sourceStage stage).root.source.base.restructuringSource.toLedgerSource where
 Projection := PUnit.{u+1}
 ActiveAt := fun _ {_current} _ => PUnit.{u+1}
 InactiveAt := fun _ {_current} _ => PEmpty.{u+1}
 classify := fun _ {_current} _ => .inl PUnit.unit
 PayloadAt := fun _ {_current} _ _ => type_of% (material frame configuration sourceStage stage)
 project := fun _ {_current} _ _ => material frame configuration sourceStage stage
def baseRoot (stage : Nat) := (original frame configuration sourceStage stage).root.withProjectionCoface
 (component frame configuration sourceStage stage)
def reader (stage : Nat) {current : type_of% (original frame configuration sourceStage stage).visit.current}
 (_supplied : (original frame configuration sourceStage stage).root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) :=
 ((component frame configuration sourceStage stage).project PUnit.unit (occurrence frame configuration sourceStage stage) PUnit.unit).2.2.2.2
def sourceInstallation (stage : Nat) := SourceNativeProjectionLaw.InstallationAt.componentCoface
 (original frame configuration sourceStage stage).root.source.base (component frame configuration sourceStage stage)
def sourceFace (stage : Nat) : SourceNativeRootSemanticFaceAt (baseRoot frame configuration sourceStage stage)
 (original frame configuration sourceStage stage).visit where
 projection := (sourceInstallation frame configuration sourceStage stage).embed PUnit.unit
 active := PUnit.unit
 classifier_eq := rfl
def result (stage : Nat) := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultAt
 (baseRoot frame configuration sourceStage stage).toAuthoritativeRoot (reader frame configuration sourceStage stage)
 (occurrence frame configuration sourceStage stage)
def queryLaw (stage : Nat) := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultLaw
 (baseRoot frame configuration sourceStage stage).toAuthoritativeRoot (reader frame configuration sourceStage stage)
def queryRoot (stage : Nat) := (baseRoot frame configuration sourceStage stage).withProjectionCoface
 (queryLaw frame configuration sourceStage stage)
def installed (stage : Nat) := SourceNativeProjectionLaw.InstallationAt.componentCoface
 (baseRoot frame configuration sourceStage stage).source.base (queryLaw frame configuration sourceStage stage)
def queryFace (stage : Nat) : SourceNativeRootSemanticFaceAt (queryRoot frame configuration sourceStage stage)
 (original frame configuration sourceStage stage).visit where
 projection := (installed frame configuration sourceStage stage).embed PUnit.unit
 active := PUnit.unit
 classifier_eq := rfl
def queryFrame (stage : Nat) := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.frame
 (queryRoot frame configuration sourceStage stage) (original frame configuration sourceStage stage).visit
 (original frame configuration sourceStage stage).U7 (original frame configuration sourceStage stage).calculus
 (reader frame configuration sourceStage stage)
abbrev generated (stage : Nat) := (Native.generated frame configuration sourceStage,sourceFace frame configuration sourceStage stage,
 queryFace frame configuration sourceStage stage,SourceGeneratedInquiryReceiptAction.actualGenerated
 (queryFrame frame configuration sourceStage stage) SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme)
end SourceGeneratedInquiryReceiptAction.Inventory.Born.Coordinates.Actual.Cofinal.Native.Reverse
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
