import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKShiftedPaRSourceWardAction.FiniteDebt
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPaUnitOutsideSourceDebtAction.Consumer
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
namespace Native
export OriginalKBoundaryNativeSourceAction (sourceFields)
end Native
namespace Previous
export OriginalKPaUnitOutsideSourceDebtAction
 (actualSourceMaterial actualParentFactory actualParentPacket sourceBornPacket splitFactory writtenSourceSplit received_source_split received_write_source_split
  actual_material_stock_effect actual_born_split_increment actual_split_source_read splitAction sourceRRead sourceWholeAt sourceBaseAt sourceSelectedAt)
end Previous
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat) (h H N radius : ℝ)

abbrev originalSource := Previous.actualSourceMaterial observation nontrivial half depth ordinal h H N radius
abbrev originalFactory := Previous.actualParentFactory observation nontrivial half depth ordinal h
abbrev originalPacket := Previous.actualParentPacket observation nontrivial half depth ordinal h H N radius

def receivedOldSplit (base : ℝ) : Split.Branches := Previous.writtenSourceSplit
 (originalSource observation nontrivial half depth ordinal h H N radius) base
 (originalFactory observation nontrivial half depth ordinal h)
 (originalPacket observation nontrivial half depth ordinal h H N radius).1
 (originalPacket observation nontrivial half depth ordinal h H N radius).2.1
 (originalPacket observation nontrivial half depth ordinal h H N radius).2.2.1
 (originalPacket observation nontrivial half depth ordinal h H N radius).2.2.2.down

theorem received_old_split_source (base : ℝ) :
 receivedOldSplit observation nontrivial half depth ordinal h H N radius base=
 shiftedSplit observation nontrivial half depth ordinal h H N base := by
 let source := originalSource observation nontrivial half depth ordinal h H N radius
 let factory := originalFactory observation nontrivial half depth ordinal h
 let packet := originalPacket observation nontrivial half depth ordinal h H N radius
 have write := Previous.actual_born_split_increment source base (Previous.splitFactory factory)
  packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down (packet.2.2.2.down.symm ▸ ())
 have effect := Previous.actual_material_stock_effect source base factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down
 have recovered := (Previous.received_write_source_split source base factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down write effect).trans
  (Previous.received_source_split source base factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down effect)
 exact recovered.trans (Previous.actual_split_source_read observation nontrivial half depth ordinal h H N radius base)

def rawSourceFields : BurnolL2 →L[ℂ] Split.Branches :=
 ((ContinuousLinearMap.id ℂ BurnolL2).prod (0 : BurnolL2 →L[ℂ] BurnolL2)).prod
  ((0 : BurnolL2 →L[ℂ] BurnolL2).prod (0 : BurnolL2 →L[ℂ] BurnolL2))

/-- The new raw-source role is generated from the actual prior write; it is not an original R/DR/Fourier four-stock. -/
def receivedShiftSource (base : ℝ) : Split.Branches :=
 rawSourceFields (receivedOldSplit observation nontrivial half depth ordinal h H N radius base).2.2

theorem received_shift_source_R (base : ℝ) :
 Previous.sourceRRead (receivedShiftSource observation nontrivial half depth ordinal h H N radius base)=
 shiftedR observation nontrivial half depth ordinal h H N base := by
 rw [receivedShiftSource,received_old_split_source]
 change shiftedR observation nontrivial half depth ordinal h H N base+0=_
 exact add_zero _

abbrev sourceParentPacket (base : ℝ) := Previous.sourceBornPacket
 (originalSource observation nontrivial half depth ordinal h H N radius) base
 (originalFactory observation nontrivial half depth ordinal h)
 (originalPacket observation nontrivial half depth ordinal h H N radius)
abbrev sourceParentFactory := Previous.splitFactory (originalFactory observation nontrivial half depth ordinal h)

theorem received_source_action_group (base step : ℝ) :
 Previous.splitAction step (receivedShiftSource observation nontrivial half depth ordinal h H N radius base)=
 shiftedSplit observation nontrivial half depth ordinal h H N (base+step) := by
 change Split.splitProjection (burnolMultiplicativeDilation (-step/2)
  (Previous.sourceRRead (receivedShiftSource observation nontrivial half depth ordinal h H N radius base)))=_
 rw [received_shift_source_R]
 unfold shiftedR
 rw [burnolMultiplicativeDilation_add]
 have parameter : -step/2+ -base/2= -(base+step)/2 := by ring
 rw [parameter]
 rfl

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKShiftedPaRSourceWardAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
