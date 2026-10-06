import H0mework.Versions.AE.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Inventory.Transport
import H0mework.Realization.Operations.ScalarExact
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.KernelWrite
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations CofinalHistorySettlement SourceOperationScalarPresentation
open CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (seed : RootedAccountedUnfolding (PresentedRelationEventAt (Expr PhysicalValue PhysicalVar sort)))
variable (frame : M.Frame (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=sort))
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
variable (occurrence : Context.Installation.Occurrence frame (current:=current))
variable (sound : GeneratedRelationSoundnessAt (face seed frame occurrence))
variable (coordinate : GeneratedKernelResidualCoordinateAt (face seed frame occurrence) sound)
abbrev word := (kernelWord seed frame occurrence sound coordinate).val
abbrev environment := (physical frame occurrence).raw.environment
-- The complete source module law already proves kernel exactness; consume its generated relation fibre.
def sourceCertificate : RelationIndex ℤ (environment frame occurrence) sort →₀ ℤ :=
  Classical.choose ((relation_range_eq_kernel (R:=ℤ) (environment frame occurrence)) ▸
    (show word seed frame occurrence sound coordinate ∈ LinearMap.ker (evaluation (R:=ℤ) (environment frame occurrence)) from
      kernel_word_value seed frame occurrence sound coordinate))
theorem sourceCertificate_read : relationMap (R:=ℤ) (environment frame occurrence)
    (sourceCertificate seed frame occurrence sound coordinate) = word seed frame occurrence sound coordinate :=
  Classical.choose_spec ((relation_range_eq_kernel (R:=ℤ) (environment frame occurrence)) ▸
    (show word seed frame occurrence sound coordinate ∈ LinearMap.ker (evaluation (R:=ℤ) (environment frame occurrence)) from
      kernel_word_value seed frame occurrence sound coordinate))


def relationEvent : RootedAccountedUnfolding (PresentedRelationEventAt (Expr PhysicalValue PhysicalVar sort)) :=
  .zero (.relation (word seed frame occurrence sound coordinate))


end SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.KernelWrite
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
