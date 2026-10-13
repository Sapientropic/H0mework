import H0mework.Versions.R9c73a630.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Inventory.Installation
import H0mework.Versions.C62.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Configured.Consumer

set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedInquiryReceiptAction.Inventory.ActualQuery
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (Programme epoch)
namespace Shared
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared
  (base baseRoot queryRoot resultRoot consumerRoot root queryLaw resultLaw consumerLaw compilationLaw
   actualOccurrence query resultFace)
end Shared
end A
namespace I
export SourceGeneratedInquiryReceiptAction.Inventory (stockLaw component programme stockEmbedding completeMaterial)
end I
variable {S : Type u} {PhysicalValue PhysicalVar : S → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {slot : S}
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
  (Value := PhysicalValue) (Var := PhysicalVar) (sort := slot))
variable (configuration : A.Programme
  (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar) (sort := slot))

def commonMaterial
    {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
    (supplied : SourceOperationInquiry.Context.Installation.Occurrence frame (current := current)) :=
  (I.completeMaterial frame configuration supplied,
   actionReader frame configuration supplied, actionResultAt frame configuration supplied)

-- The full old stock remains an independent installed coordinate.
def commonLaw : SourceNativeProjectionLaw
    (A.Shared.base frame).root.source.base.restructuringSource.toLedgerSource where
  Projection := (I.stockLaw frame configuration).Projection
  ActiveAt := (I.stockLaw frame configuration).ActiveAt
  InactiveAt := (I.stockLaw frame configuration).InactiveAt
  classify := (I.stockLaw frame configuration).classify
  PayloadAt := fun _ {_current} supplied _ => type_of% (commonMaterial frame configuration supplied)
  project := fun _ {_current} supplied _ => commonMaterial frame configuration supplied

def component : SourceNativeProjectionLaw
    (A.Shared.base frame).root.source.base.restructuringSource.toLedgerSource :=
  ({ (A.Shared.base frame).root.source.base with projectionLaw := I.component frame configuration }.withProjectionCoface
    (commonLaw frame configuration)).projectionLaw

def programme : A.Programme
    (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar) (sort := slot) :=
  { I.programme configuration with
    datum := fun sourceFrame =>
      { (I.programme configuration).datum sourceFrame with
        component := some (component sourceFrame configuration)
        reader := fun {_current} supplied => (commonMaterial sourceFrame configuration supplied).2.1
        calculationReader := some (fun {_current} supplied => (commonMaterial sourceFrame configuration supplied).2.1) } }

def stockEmbedding : SourceNativeProjectionLaw.InstallationAt
    (I.stockLaw frame configuration) (component frame configuration) :=
  (I.stockEmbedding frame configuration).trans
    (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
      { (A.Shared.base frame).root.source.base with projectionLaw := I.component frame configuration }
      (commonLaw frame configuration))

def commonEmbedding : SourceNativeProjectionLaw.InstallationAt
    (commonLaw frame configuration) (component frame configuration) :=
  SourceNativeProjectionLaw.InstallationAt.componentCoface
    { (A.Shared.base frame).root.source.base with projectionLaw := I.component frame configuration }
    (commonLaw frame configuration)

def componentInstalled : SourceNativeProjectionLaw.InstallationAt
    (component (A.epoch frame) configuration)
    (A.Shared.root frame (programme configuration)).source.base.projectionLaw :=
  (SourceNativeProjectionLaw.InstallationAt.componentCoface
    (A.Shared.base frame).root.source.base (component (A.epoch frame) configuration)).trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
    (A.Shared.baseRoot frame (programme configuration)).source.base
    (A.Shared.queryLaw (A.epoch frame) (programme configuration))) |>.trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
    (A.Shared.queryRoot frame (programme configuration)).source.base
    (A.Shared.resultLaw (A.epoch frame) (programme configuration))) |>.trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
    (A.Shared.resultRoot frame (programme configuration)).source.base
    (A.Shared.consumerLaw (A.epoch frame) (programme configuration))) |>.trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
    (A.Shared.consumerRoot frame (programme configuration)).source.base
    (A.Shared.compilationLaw (A.epoch frame) (programme configuration)))

def stockInstalled := (stockEmbedding (A.epoch frame) configuration).trans
  (componentInstalled frame configuration)
def commonInstalled := (commonEmbedding (A.epoch frame) configuration).trans
  (componentInstalled frame configuration)
def stockOutcome := (A.Shared.root frame (programme configuration)).source.base.projectionLaw.outcomeAt
  ((stockInstalled frame configuration).embed PUnit.unit) (A.Shared.actualOccurrence frame)
def commonOutcome := (A.Shared.root frame (programme configuration)).source.base.projectionLaw.outcomeAt
  ((commonInstalled frame configuration).embed PUnit.unit) (A.Shared.actualOccurrence frame)

end SourceGeneratedInquiryReceiptAction.Inventory.ActualQuery
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
