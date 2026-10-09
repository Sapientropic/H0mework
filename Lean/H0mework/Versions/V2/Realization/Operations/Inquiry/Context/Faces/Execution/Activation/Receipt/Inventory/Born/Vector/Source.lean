import H0mework.Versions.V2.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Inventory.Born.Consumer
import H0mework.Realization.Operations.Execution.InventoryVector.Source
import H0mework.Versions.PR.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Frame.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedInquiryReceiptAction.Inventory.Born.Vector
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open CofinalHistorySettlement SourceOperationScalarRelations SourceOperationScalarPresentation
variable {S : Type u} {PhysicalValue PhysicalVar : S → Type u}
 [∀ target,AddCommGroup (PhysicalValue target)] {slot : S}
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=slot))
variable (configuration : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
 (PhysicalValue:=PhysicalValue) (PhysicalVar:=PhysicalVar) (sort:=slot))
namespace V
export SaturationMonoid.SourceOperationExecution.InventoryVector (VectorValue query environment query_read query_charge)
end V
namespace C
export SourceOperationInquiry.Context.Installation (Occurrence materialAt)
end C
abbrev Index := Fin (inventory frame configuration).trace.length
abbrev Value := V.VectorValue (Index frame configuration) (Value:=PairValue (PairValue PhysicalValue))
def event (index : Index frame configuration) := (inventory frame configuration).trace.get index
def word (index : Index frame configuration) : Formal ℤ (PairValue PhysicalValue) configuration.LowVar slot :=
 match event frame configuration index with
 | .generator expression => Finsupp.single expression 1
 | .relation relation => relation
def items := List.ofFn (fun index : Index frame configuration =>
 (index,liftExpr (SourceOperationExecution.Coefficients.expression (word frame configuration index))))
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current (bornFrame frame configuration).registered}
variable (supplied : C.Occurrence (bornFrame frame configuration) (current:=current))
abbrev physical := C.materialAt (bornFrame frame configuration) supplied
abbrev oldEnvironment := (physical frame configuration supplied).raw.environment
abbrev increment := (physical frame configuration supplied).nextRaw.environment-oldEnvironment frame configuration supplied
def raw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw (Value:=Value frame configuration) (Var:=configuration.LowVar) (sort:=slot) :=
 ⟨V.environment (Index frame configuration)
   (pairEnvironment (oldEnvironment frame configuration supplied) (increment frame configuration supplied)),
  V.query (Index frame configuration) (items frame configuration)⟩
def reader {sourceCurrent : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current (bornFrame frame configuration).registered}
 (supplied : C.Occurrence (bornFrame frame configuration) (current:=sourceCurrent)) := raw frame configuration supplied
abbrev sourceRoot := (bornFrame frame configuration).currentState.root
abbrev sourceVisit := (bornFrame frame configuration).currentState.visit
abbrev occurrence := (sourceRoot frame configuration).emitted (sourceVisit frame configuration).current
def result := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultAt
 (sourceRoot frame configuration).toAuthoritativeRoot (reader frame configuration) (occurrence frame configuration)
def queryLaw := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultLaw
 (sourceRoot frame configuration).toAuthoritativeRoot (reader frame configuration)
def queryRoot := (sourceRoot frame configuration).withProjectionCoface (queryLaw frame configuration)
def installed := SourceNativeProjectionLaw.InstallationAt.componentCoface
 (sourceRoot frame configuration).source.base (queryLaw frame configuration)
def queryFace : SourceNativeRootSemanticFaceAt (queryRoot frame configuration) (sourceVisit frame configuration) where
 projection := (installed frame configuration).embed PUnit.unit
 active := PUnit.unit
 classifier_eq := rfl
def queryFrame := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.frame
 (queryRoot frame configuration) (sourceVisit frame configuration)
 (bornFrame frame configuration).currentState.U7 (bornFrame frame configuration).currentState.calculus
 (reader frame configuration)
abbrev generated := (queryFace frame configuration,
 SourceGeneratedInquiryReceiptAction.actualGenerated (queryFrame frame configuration)
  SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme)
end SourceGeneratedInquiryReceiptAction.Inventory.Born.Vector
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
