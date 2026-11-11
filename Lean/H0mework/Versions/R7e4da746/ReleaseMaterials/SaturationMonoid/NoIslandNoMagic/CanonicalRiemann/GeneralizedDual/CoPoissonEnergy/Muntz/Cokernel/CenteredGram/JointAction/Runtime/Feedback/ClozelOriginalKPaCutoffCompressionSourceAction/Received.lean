import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPaCutoffCompressionSourceAction.Price
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKWindowInverseResidualSourceAction.Consumer
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPaCutoffCompressionSourceAction
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual BurnolPhysicalState
open scoped InnerProductSpace



open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
namespace R
export OriginalKWindowInverseResidualSourceAction (actualSourceFactory actualSourcePacket actualReceivedResidual actualResidualWhole)
end R
namespace F
export OriginalKFinitePaWindowOperatorSourceAction (actualPreviousPacket actualReceivedNu previous_nu_origin)
end F
local instance receiptSourceGroups (grade : Nat) (target : Unit) :
 AddCommGroup (OriginalKFinitePaWindowOperatorSourceAction.L.Value (PairValue OriginalKFullSourceRAction.C.Value) grade target) :=
 OriginalKFinitePaWindowOperatorSourceAction.L.groups (PairValue OriginalKFullSourceRAction.C.Value) grade target
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat) (h H N radius : ℝ)

abbrev materialAt := OriginalKMaterialPaWindowSourceAction.actualParentMaterialREffect observation nontrivial half depth ordinal h H N

theorem source_vector_receipt : F.actualReceivedNu observation nontrivial half depth ordinal h H N =
 Native.sourceFields (actualNu (materialAt observation nontrivial half depth ordinal h H N)) := by
 unfold OriginalKFinitePaWindowOperatorSourceAction.actualReceivedNu
 rw [F.previous_nu_origin]
 rfl

theorem received_residual_compression
 (write : type_of% (OriginalKFinitePaWindowOperatorSourceAction.finite_stock_generated_source_delta
  (R.actualSourceFactory observation nontrivial half depth ordinal h)
  (F.actualPreviousPacket observation nontrivial half depth ordinal h H N).1
  (F.actualPreviousPacket observation nontrivial half depth ordinal h H N).2.1
  (F.actualPreviousPacket observation nontrivial half depth ordinal h H N).2.2.1
  (F.actualPreviousPacket observation nontrivial half depth ordinal h H N).2.2.2.down radius
  (F.actualReceivedNu observation nontrivial half depth ordinal h H N)
  ((F.actualPreviousPacket observation nontrivial half depth ordinal h H N).2.2.2.down.symm ▸ ()))) :
 OriginalKFullSourceRAction.originalField (R.actualReceivedResidual observation nontrivial half depth ordinal h H N radius) =
 burnolMobiusSourceL2 (physicalTailAction radius (actualPaField (materialAt observation nontrivial half depth ordinal h H N))) := by
 have origin := OriginalKWindowInverseResidualSourceAction.received_residual_source _ _ _ _ write
 change OriginalKFullSourceRAction.originalField (R.actualReceivedResidual observation nontrivial half depth ordinal h H N radius) = _ at origin
 rw [source_vector_receipt] at origin
 exact origin.trans (actual_inverse_compression_source _ _)

theorem received_residual_source_cost
 (write : type_of% (OriginalKFinitePaWindowOperatorSourceAction.finite_stock_generated_source_delta
  (R.actualSourceFactory observation nontrivial half depth ordinal h)
  (F.actualPreviousPacket observation nontrivial half depth ordinal h H N).1
  (F.actualPreviousPacket observation nontrivial half depth ordinal h H N).2.1
  (F.actualPreviousPacket observation nontrivial half depth ordinal h H N).2.2.1
  (F.actualPreviousPacket observation nontrivial half depth ordinal h H N).2.2.2.down radius
  (F.actualReceivedNu observation nontrivial half depth ordinal h H N)
  ((F.actualPreviousPacket observation nontrivial half depth ordinal h H N).2.2.2.down.symm ▸ ()))) :
 ‖OriginalKFullSourceRAction.originalField (R.actualReceivedResidual observation nontrivial half depth ordinal h H N radius)‖ ≤
 ‖burnolMobiusSourceL2‖ * ‖outsideTailAction radius
  (actualPaField (materialAt observation nontrivial half depth ordinal h H N) : BurnolL2)‖ := by
 rw [received_residual_compression _ _ _ _ _ _ _ _ _ write]
 exact (burnolMobiusSourceL2.le_opNorm _).trans
  (mul_le_mul_of_nonneg_left (physical_tail_norm_le_outside _ _) (ContinuousLinearMap.opNorm_nonneg _))

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPaCutoffCompressionSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
