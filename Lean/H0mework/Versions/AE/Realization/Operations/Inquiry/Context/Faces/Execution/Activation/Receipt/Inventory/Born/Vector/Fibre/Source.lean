import H0mework.Versions.AE.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Inventory.Born.Vector.Consumer
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedInquiryReceiptAction.Inventory.Born.Vector.Fibre
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open CofinalHistorySettlement SourceOperationScalarRelations SourceOperationScalarPresentation SourceGeneratedScalarDifferentialResidual
variable {S : Type u} {PhysicalValue PhysicalVar : S → Type u}
 [∀ target,AddCommGroup (PhysicalValue target)] {slot : S}
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=slot))
variable (configuration : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
 (PhysicalValue:=PhysicalValue) (PhysicalVar:=PhysicalVar) (sort:=slot))
abbrev Words := Index frame configuration → Formal ℤ (PairValue PhysicalValue) configuration.LowVar slot
abbrev actualWords : Words frame configuration := word frame configuration
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current (bornFrame frame configuration).registered}
variable (supplied : C.Occurrence (bornFrame frame configuration) (current:=current))
def joint : Words frame configuration →ₗ[ℤ] Value frame configuration slot where
 toFun words := fun index => updateInventory (R:=ℤ) (oldEnvironment frame configuration supplied)
  (increment frame configuration supplied) (words index)
 map_add' left right := by funext index; exact (updateInventory (R:=ℤ) _ _).map_add _ _
 map_smul' coefficient words := by funext index; exact (updateInventory (R:=ℤ) _ _).map_smul _ _
def next : Words frame configuration →ₗ[ℤ] (Index frame configuration → PairValue PhysicalValue slot) where
 toFun words := fun index => evaluation (R:=ℤ) (oldEnvironment frame configuration supplied+increment frame configuration supplied) (words index)
 map_add' left right := by funext index; exact (evaluation (R:=ℤ) _).map_add _ _
 map_smul' coefficient words := by funext index; exact (evaluation (R:=ℤ) _).map_smul _ _
def addition : Value frame configuration slot →ₗ[ℤ] (Index frame configuration → PairValue PhysicalValue slot) where
 toFun values := fun index => (values index).1+(values index).2
 map_add' left right := by
  funext index
  change ((left index).1+(right index).1)+((left index).2+(right index).2)=
   ((left index).1+(left index).2)+((right index).1+(right index).2)
  abel
 map_smul' coefficient values := by
  funext index
  change coefficient • (values index).1+coefficient • (values index).2=coefficient • ((values index).1+(values index).2)
  exact (smul_add coefficient (values index).1 (values index).2).symm
def update : Morphism (joint frame configuration supplied) (next frame configuration supplied) where
 sourceMap := LinearMap.id
 targetMap := addition frame configuration
 commutes := by
  apply LinearMap.ext
  intro words
  funext index
  exact (LinearMap.congr_fun (evaluation_update (R:=ℤ)
   (oldEnvironment frame configuration supplied) (increment frame configuration supplied)) (words index)).symm
abbrev JointCarrier := ResidualCarrier (joint frame configuration supplied)
abbrev NextCarrier := ResidualCarrier (next frame configuration supplied)
def inverse := canonicalResidual (joint frame configuration supplied) (actualWords frame configuration)
def nextInverse := inducedResidualMap (update frame configuration supplied) (inverse frame configuration supplied)
def completeMaterial := (joint frame configuration supplied,next frame configuration supplied,update frame configuration supplied,
 actualWords frame configuration,inverse frame configuration supplied,nextInverse frame configuration supplied)
def component : SourceNativeProjectionLaw (queryRoot frame configuration).source.base.restructuringSource.toLedgerSource where
 Projection := PUnit.{u+1}
 ActiveAt := fun _ {_current} _ => PUnit.{u+1}
 InactiveAt := fun _ {_current} _ => PEmpty.{u+1}
 classify := fun _ {_current} _ => .inl PUnit.unit
 PayloadAt := fun _ {_current} supplied _ => type_of% (completeMaterial frame configuration supplied)
 project := fun _ {_current} supplied _ => completeMaterial frame configuration supplied
def root := (queryRoot frame configuration).withProjectionCoface (component frame configuration)
def installed := SourceNativeProjectionLaw.InstallationAt.componentCoface (queryRoot frame configuration).source.base
 (component frame configuration)
def face : SourceNativeRootSemanticFaceAt (root frame configuration) (sourceVisit frame configuration) where
 projection := (installed frame configuration).embed PUnit.unit
 active := PUnit.unit
 classifier_eq := rfl
def queryFrame := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.frame
 (root frame configuration) (sourceVisit frame configuration)
 (bornFrame frame configuration).currentState.U7 (bornFrame frame configuration).currentState.calculus
 (reader frame configuration)
abbrev generated := (Vector.queryFace frame configuration,face frame configuration,
 SourceGeneratedInquiryReceiptAction.actualGenerated (queryFrame frame configuration)
  SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme)
end SourceGeneratedInquiryReceiptAction.Inventory.Born.Vector.Fibre
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
