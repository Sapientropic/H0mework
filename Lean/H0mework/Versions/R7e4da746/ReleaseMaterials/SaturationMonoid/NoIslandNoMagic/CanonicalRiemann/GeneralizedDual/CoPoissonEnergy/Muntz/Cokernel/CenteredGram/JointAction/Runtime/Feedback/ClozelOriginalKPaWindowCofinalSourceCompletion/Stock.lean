import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPaWindowCofinalSourceCompletion.Completion
import H0mework.Realization.ScalarCofinal.RootOccurrence
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Configured.Writeback.Successor.FourFace.Native.Source
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPaWindowCofinalSourceCompletion
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution
namespace AN
export ActualNativeRelationTransport (stockMaterial stock_material_source stock_paid_trace stockInstalled stockOutcome stock_payload born_payload)
end AN
namespace CofinalFace
export SourceGeneratedScalarCofinalRootOccurrence (Face)
end CofinalFace

universe u
variable {Sorts : Type u} {Value Var : Sorts → Type u}
 [∀ s, AddCommGroup (Value s)] {sort : Sorts}
variable (frame : ActualNativeRelationTransport.A.M.Frame (Value:=Value) (Var:=Var) (sort:=sort))
variable (base : ActualNativeRelationTransport.A.Programme (PhysicalValue:=Value) (PhysicalVar:=Var) (sort:=sort))

/-- This calculation history is read through the existing installed whole-root stock authority. -/
def installedSourceHistory := (AN.stockMaterial frame base).2.2

def sourceCofinalOccurrence := (installedSourceHistory frame base).map (fun event => (event,sourceData))

def sourceCofinalFace := SourceGeneratedScalarCofinalRootOccurrence.Face.generate (occurrence:=sourceCofinalOccurrence frame base)

theorem source_cofinal_face_data : (sourceCofinalFace frame base).data = sourceData := by
 exact ((sourceCofinalFace frame base).data_root).trans (by
  rw [sourceCofinalOccurrence,RootedAccountedUnfolding.root_map])

theorem sourceCofinalCalculation : SourceGeneratedScalarCofinalRootOccurrence.Face.GeneratedCompatibilityCalculationAt (sourceCofinalFace frame base) :=
 (sourceCofinalFace frame base).generateCompatibility (by
  change (sourceCofinalFace frame base).data.Compatible
  rw [source_cofinal_face_data]
  exact source_data_compatible)

theorem source_cofinal_face_preserves_history :
 (sourceCofinalFace frame base).root = installedSourceHistory frame base := by
 change ((installedSourceHistory frame base).map (fun event => (event,sourceData))).map Prod.fst = _
 rw [RootedAccountedUnfolding.map_map]
 exact RootedAccountedUnfolding.map_id _

theorem source_cofinal_face_injective :
 Function.Injective ((sourceCofinalFace frame base).completionMap (sourceCofinalCalculation frame base)) :=
 (sourceCofinalFace frame base).completionMap_injective (sourceCofinalCalculation frame base) (by
  rw [source_cofinal_face_data]
  exact source_data_kernel_separated)

theorem source_cofinal_face_readback (stage : Nat) : type_of%
 ((sourceCofinalFace frame base).source_to_evaluator (sourceCofinalCalculation frame base) stage) :=
 (sourceCofinalFace frame base).source_to_evaluator (sourceCofinalCalculation frame base) stage

theorem installed_source_history : installedSourceHistory frame base =
 (SourceGeneratedInquiryReceiptAction.Inventory.completeMaterial
  (ActualNativeRelationTransport.A.epoch frame) base
  (ActualNativeRelationTransport.S.actualOccurrence frame)).2.2 := by
 unfold installedSourceHistory
 rw [AN.stock_material_source]

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPaWindowCofinalSourceCompletion
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
