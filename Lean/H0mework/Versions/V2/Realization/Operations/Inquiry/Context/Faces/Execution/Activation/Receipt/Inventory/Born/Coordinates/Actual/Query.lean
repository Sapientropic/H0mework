import H0mework.Versions.V2.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Inventory.Born.Coordinates.Actual.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedInquiryReceiptAction.Inventory.Born.Coordinates.Actual
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations
variable {S : Type u} {PhysicalValue PhysicalVar : S → Type u}
 [∀ target,AddCommGroup (PhysicalValue target)] {slot : S}
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=slot))
variable (configuration : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
 (PhysicalValue:=PhysicalValue) (PhysicalVar:=PhysicalVar) (sort:=slot))
abbrev ActualIndex := Fin (actualInventory frame configuration).trace.length
def actualWord (index : ActualIndex frame configuration) := inventoryEventWord configuration ((actualInventory frame configuration).trace.get index)
theorem actual_word_read (index : Vector.Index frame configuration) : actualWord frame configuration
 (intoActual frame configuration index)=Vector.word frame configuration index :=
 congrArg (inventoryEventWord configuration) (actual_event_read frame configuration index)
def items := List.ofFn (fun index : ActualIndex frame configuration =>
 (index,liftExpr (SourceOperationExecution.Coefficients.expression (actualWord frame configuration index))))
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current (actualFrame frame configuration).registered}
variable (supplied : SourceOperationInquiry.Context.Installation.Occurrence (actualFrame frame configuration) (current:=current))
abbrev physical := SourceOperationInquiry.Context.Installation.materialAt (actualFrame frame configuration) supplied
abbrev oldEnvironment := (physical frame configuration supplied).raw.environment
abbrev increment := (physical frame configuration supplied).nextRaw.environment-oldEnvironment frame configuration supplied
def raw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
 (Value:=SaturationMonoid.SourceOperationExecution.InventoryVector.VectorValue (ActualIndex frame configuration)
   (Value:=PairValue (PairValue PhysicalValue))) (Var:=configuration.LowVar) (sort:=slot) :=
 ⟨SaturationMonoid.SourceOperationExecution.InventoryVector.environment (ActualIndex frame configuration)
   (pairEnvironment (oldEnvironment frame configuration supplied) (increment frame configuration supplied)),
  SaturationMonoid.SourceOperationExecution.InventoryVector.query (ActualIndex frame configuration) (items frame configuration)⟩
def reader {sourceCurrent : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current (actualFrame frame configuration).registered}
 (supplied : SourceOperationInquiry.Context.Installation.Occurrence (actualFrame frame configuration) (current:=sourceCurrent)) := raw frame configuration supplied
abbrev root := (actualFrame frame configuration).currentState.root
abbrev visit := (actualFrame frame configuration).currentState.visit
abbrev occurrence := (root frame configuration).emitted (visit frame configuration).current
def result := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultAt
 (root frame configuration).toAuthoritativeRoot (reader frame configuration) (occurrence frame configuration)
def queryLaw := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultLaw
 (root frame configuration).toAuthoritativeRoot (reader frame configuration)
def queryRoot := (root frame configuration).withProjectionCoface (queryLaw frame configuration)
def installed := SourceNativeProjectionLaw.InstallationAt.componentCoface (root frame configuration).source.base (queryLaw frame configuration)
def queryFace : SourceNativeRootSemanticFaceAt (queryRoot frame configuration) (visit frame configuration) where
 projection := (installed frame configuration).embed PUnit.unit
 active := PUnit.unit
 classifier_eq := rfl
def queryFrame := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.frame
 (queryRoot frame configuration) (visit frame configuration) (actualFrame frame configuration).currentState.U7
 (actualFrame frame configuration).currentState.calculus (reader frame configuration)
abbrev generated := (Vector.Action.generated frame configuration,queryFace frame configuration,
 SourceGeneratedInquiryReceiptAction.actualGenerated (queryFrame frame configuration)
  SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme)
end SourceGeneratedInquiryReceiptAction.Inventory.Born.Coordinates.Actual
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
