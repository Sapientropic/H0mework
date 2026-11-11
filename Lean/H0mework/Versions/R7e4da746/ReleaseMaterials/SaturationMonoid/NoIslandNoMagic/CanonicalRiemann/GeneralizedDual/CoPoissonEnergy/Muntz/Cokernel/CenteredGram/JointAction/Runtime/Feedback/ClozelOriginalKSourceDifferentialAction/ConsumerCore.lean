import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceDifferentialAction.Price
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceDifferentialAction.Inventory
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceDifferentialAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
namespace Prior
export OriginalKSourceCofinalNativeSuccessor
 (SourceActualWriteAcceptance SourceActualInventoryAcceptance SourceActualWholeAcceptance
  source_actual_write_acceptance source_actual_inventory_acceptance source_actual_whole_acceptance source_actual_whole_root source_actual_whole_current)
end Prior
variable {W X : Unit→Type} [∀ target,AddCommGroup (W target)]
local instance coreGroups (grade : Nat) : ∀ target,AddCommGroup (L.Value W grade target) := L.groups W grade
variable (mother : SF.Factory W X ())
variable (packet : AS.AdmissionPacket (W:=W) (X:=X) (s:=()))
attribute [local irreducible] Prior.SourceActualWriteAcceptance Prior.SourceActualInventoryAcceptance Prior.SourceActualWholeAcceptance

/-- The original actual native source and whole accept this same differential action and full typed inventories. -/
def SourceDifferentialNativeAcceptance : Prop :=
 (type_of% (Prior.source_actual_write_acceptance (sourceCompleteDifferentialFactory mother) (sourceCompleteDifferentialPacket mother packet))) ∧
 (type_of% (Prior.source_actual_inventory_acceptance (sourceCompleteDifferentialFactory mother) (sourceCompleteDifferentialPacket mother packet))) ∧
 (type_of% (Prior.source_actual_whole_acceptance (sourceCompleteDifferentialFactory mother) (sourceCompleteDifferentialPacket mother packet))) ∧
 (type_of% (Prior.source_actual_whole_root (sourceCompleteDifferentialFactory mother) (sourceCompleteDifferentialPacket mother packet))) ∧
 (type_of% (Prior.source_actual_whole_current (sourceCompleteDifferentialFactory mother) (sourceCompleteDifferentialPacket mother packet)))
attribute [local irreducible] SourceDifferentialNativeAcceptance

theorem source_differential_native_acceptance : SourceDifferentialNativeAcceptance mother packet := by
 unfold SourceDifferentialNativeAcceptance
 exact ⟨Prior.source_actual_write_acceptance _ _,Prior.source_actual_inventory_acceptance _ _,
  Prior.source_actual_whole_acceptance _ _,Prior.source_actual_whole_root _ _,Prior.source_actual_whole_current _ _⟩

/-- All source nodes and complete mother quantities are consumed together with their real native inherited fee. -/
def SourceDifferentialQuantityAcceptance : Prop :=
 (type_of% (source_complete_scalar_nodes mother packet)) ∧
 (type_of% (source_complete_pair_nodes mother packet)) ∧
 (type_of% (source_whole_registered_faces mother packet)) ∧
 (type_of% (source_whole_recovers_same_mother mother packet)) ∧
 (∀ {Result : Type} [AddCommGroup Result] (read : PairValue (L.Value W packet.1) ()→+Result),
  read (actualDifferentialWholeTotal mother packet)=read (actualDifferentialRecovered mother packet)+read (actualDifferentialInherited mother packet))
attribute [local irreducible] SourceDifferentialQuantityAcceptance

theorem source_differential_quantity_acceptance : SourceDifferentialQuantityAcceptance mother packet := by
 unfold SourceDifferentialQuantityAcceptance
 exact ⟨source_complete_scalar_nodes _ _,source_complete_pair_nodes _ _,source_whole_registered_faces _ _,
  source_whole_recovers_same_mother _ _,fun read=>source_whole_observer_full_fees _ _ read⟩

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceDifferentialAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
