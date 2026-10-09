import H0mework.Versions.V2.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Inventory.Born.Vector.Fibre.Consumer
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedInquiryReceiptAction.Inventory.Born.Vector.Action
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open CofinalHistorySettlement SourceOperationScalarRelations SourceOperationScalarPresentation SourceGeneratedScalarDifferentialResidual
variable {S : Type u} {PhysicalValue PhysicalVar : S → Type u}
 [∀ target,AddCommGroup (PhysicalValue target)] {slot : S}
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=slot))
variable (configuration : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
 (PhysicalValue:=PhysicalValue) (PhysicalVar:=PhysicalVar) (sort:=slot))
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current (bornFrame frame configuration).registered}
variable (supplied : C.Occurrence (bornFrame frame configuration) (current:=current))
abbrev sourceMaterial := (Fibre.component frame configuration).project PUnit.unit supplied PUnit.unit
abbrev sourceWords := (sourceMaterial frame configuration supplied).2.2.2.1
def binding (sort : S) (name : configuration.LowVar sort) : Expr (PairValue PhysicalValue) configuration.LowVar sort :=
 .const ((physical frame configuration supplied).nextRaw.environment sort name)
def actedWords : Fibre.Words frame configuration := fun index =>
 substitution (R:=ℤ) (binding frame configuration supplied) (sourceWords frame configuration supplied index)
def expression (index : Index frame configuration) :=
 (SourceOperationExecution.Coefficients.expression (sourceWords frame configuration supplied index)).subst (binding frame configuration supplied)
def items := List.ofFn (fun index : Index frame configuration => (index,liftExpr (expression frame configuration supplied index)))
def raw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw (Value:=Value frame configuration) (Var:=configuration.LowVar) (sort:=slot) :=
 ⟨V.environment (Index frame configuration)
   (pairEnvironment (oldEnvironment frame configuration supplied) (increment frame configuration supplied)),
  V.query (Index frame configuration) (items frame configuration supplied)⟩
def material := (sourceMaterial frame configuration supplied,binding frame configuration supplied,
 actedWords frame configuration supplied,expression frame configuration supplied,raw frame configuration supplied)
def component : SourceNativeProjectionLaw (Fibre.root frame configuration).source.base.restructuringSource.toLedgerSource where
 Projection := PUnit.{u+1}
 ActiveAt := fun _ {_current} _ => PUnit.{u+1}
 InactiveAt := fun _ {_current} _ => PEmpty.{u+1}
 classify := fun _ {_current} _ => .inl PUnit.unit
 PayloadAt := fun _ {_current} supplied _ => type_of% (material frame configuration supplied)
 project := fun _ {_current} supplied _ => material frame configuration supplied
def reader {sourceCurrent : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current (bornFrame frame configuration).registered}
 (supplied : C.Occurrence (bornFrame frame configuration) (current:=sourceCurrent)) :=
 ((component frame configuration).project PUnit.unit supplied PUnit.unit).2.2.2.2
def root := (Fibre.root frame configuration).withProjectionCoface (component frame configuration)
def actionInstallation := SourceNativeProjectionLaw.InstallationAt.componentCoface
 (Fibre.root frame configuration).source.base (component frame configuration)
def actionFace : SourceNativeRootSemanticFaceAt (root frame configuration) (sourceVisit frame configuration) where
 projection := (actionInstallation frame configuration).embed PUnit.unit
 active := PUnit.unit
 classifier_eq := rfl
def result := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultAt
 (root frame configuration).toAuthoritativeRoot (reader frame configuration) (occurrence frame configuration)
def queryLaw := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultLaw
 (root frame configuration).toAuthoritativeRoot (reader frame configuration)
def queryRoot := (root frame configuration).withProjectionCoface (queryLaw frame configuration)
def installed := SourceNativeProjectionLaw.InstallationAt.componentCoface (root frame configuration).source.base (queryLaw frame configuration)
def queryFace : SourceNativeRootSemanticFaceAt (queryRoot frame configuration) (sourceVisit frame configuration) where
 projection := (installed frame configuration).embed PUnit.unit
 active := PUnit.unit
 classifier_eq := rfl
def queryFrame := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.frame
 (queryRoot frame configuration) (sourceVisit frame configuration)
 (bornFrame frame configuration).currentState.U7 (bornFrame frame configuration).currentState.calculus
 (reader frame configuration)
abbrev generated := (Fibre.face frame configuration,actionFace frame configuration,queryFace frame configuration,
 SourceGeneratedInquiryReceiptAction.actualGenerated (queryFrame frame configuration)
  SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme)
end SourceGeneratedInquiryReceiptAction.Inventory.Born.Vector.Action
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
