import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKShiftedPaRSourceWardAction.NextSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKShiftedPaRSourceWardAction.Conservation
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKShiftedPaRSourceWardAction
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
namespace Step
export OriginalKPaUnitOutsideSourceDebtAction
 (received_source_split received_write_source_split writtenSourceSplit actual_born_split_increment actual_material_stock_effect
  consume_split_source_receipt sourceWholeAt source_born_root source_born_current source_packet_all_future sourceBornPacket)
end Step
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat) (h H N radius : ℝ)

def nextWrittenSourceSplit (base step : ℝ) : Split.Branches :=
 Step.writtenSourceSplit (receivedShiftSource observation nontrivial half depth ordinal h H N radius base) step
 (sourceParentFactory observation nontrivial half depth ordinal h)
 (sourceParentPacket observation nontrivial half depth ordinal h H N radius base).1
 (sourceParentPacket observation nontrivial half depth ordinal h H N radius base).2.1
 (sourceParentPacket observation nontrivial half depth ordinal h H N radius base).2.2.1
 (sourceParentPacket observation nontrivial half depth ordinal h H N radius base).2.2.2.down

/-- Received write/effect from the true successor recovers its clean source endpoint after paying the complete inherited fee. -/
theorem received_next_split_source (base step : ℝ)
 (write : type_of% (Step.actual_born_split_increment
  (receivedShiftSource observation nontrivial half depth ordinal h H N radius base) step
  (Previous.splitFactory (sourceParentFactory observation nontrivial half depth ordinal h))
  (sourceParentPacket observation nontrivial half depth ordinal h H N radius base).1
  (sourceParentPacket observation nontrivial half depth ordinal h H N radius base).2.1
  (sourceParentPacket observation nontrivial half depth ordinal h H N radius base).2.2.1
  (sourceParentPacket observation nontrivial half depth ordinal h H N radius base).2.2.2.down
  ((sourceParentPacket observation nontrivial half depth ordinal h H N radius base).2.2.2.down.symm ▸ ())))
 (effect : type_of% (Step.actual_material_stock_effect
  (receivedShiftSource observation nontrivial half depth ordinal h H N radius base) step
  (sourceParentFactory observation nontrivial half depth ordinal h)
  (sourceParentPacket observation nontrivial half depth ordinal h H N radius base).1
  (sourceParentPacket observation nontrivial half depth ordinal h H N radius base).2.1
  (sourceParentPacket observation nontrivial half depth ordinal h H N radius base).2.2.1
  (sourceParentPacket observation nontrivial half depth ordinal h H N radius base).2.2.2.down)) :
 nextWrittenSourceSplit observation nontrivial half depth ordinal h H N radius base step=
 shiftedSplit observation nontrivial half depth ordinal h H N (base+step) := by
 let source := receivedShiftSource observation nontrivial half depth ordinal h H N radius base
 let factory := sourceParentFactory observation nontrivial half depth ordinal h
 let packet := sourceParentPacket observation nontrivial half depth ordinal h H N radius base
 exact ((Step.received_write_source_split source step factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down write effect).trans
  (Step.received_source_split source step factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down effect)).trans
  (received_source_action_group observation nontrivial half depth ordinal h H N radius base step)

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKShiftedPaRSourceWardAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
