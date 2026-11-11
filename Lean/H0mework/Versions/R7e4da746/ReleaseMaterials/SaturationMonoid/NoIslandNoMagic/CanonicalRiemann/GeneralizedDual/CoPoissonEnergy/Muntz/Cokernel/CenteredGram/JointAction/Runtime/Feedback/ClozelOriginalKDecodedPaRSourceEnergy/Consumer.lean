import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDecodedPaRSourceEnergy.Rank
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDecodedPaRSourceEnergy
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
namespace Actual
export OriginalKDecodedPaRFourFaceSourceAction (actual_material_stock_effect receivedOwnStock received_material_own_stock sourceWholeAt source_born_current source_born_root actualParentFactory actualParentPacket consume_four_stock_receipt actual_born_four_stock_increment fourFaceFactory)
end Actual
namespace C
export OriginalKDecodedPaRFourFaceSourceAction.C (Value Var)
end C
namespace SF
export OriginalKDecodedPaRFourFaceSourceAction.SF (Factory)
end SF
namespace L
export OriginalKDecodedPaRFourFaceSourceAction.L (Value groups)
end L
namespace AP
export OriginalKDecodedPaRFourFaceSourceAction.AP (AdmissionPacket)
end AP
local instance consumerEnergyPhysicalComplete : CompleteSpace BurnolPaAmbientCarrier := by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local instance consumerEnergyGroups (grade : Nat) (target : Unit) :
 AddCommGroup (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade target
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat) (h H N : ℝ)
variable (producer : SF.Factory (PairValue C.Value) C.Var ())
variable (packet : AP.AdmissionPacket (W:=PairValue C.Value) (X:=C.Var) (s:=()))

def receivedSourceR : BurnolL2 :=
 (Actual.receivedOwnStock observation nontrivial half depth ordinal h H N producer packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down).1.1+
 (Actual.receivedOwnStock observation nontrivial half depth ordinal h H N producer packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down).1.2

theorem received_source_R_read
 (effect : type_of% (Actual.actual_material_stock_effect observation nontrivial half depth ordinal h H N producer packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down)) :
 receivedSourceR observation nontrivial half depth ordinal h H N producer packet = sourceR observation nontrivial half depth ordinal h H N := by
 unfold receivedSourceR
 rw [Actual.received_material_own_stock _ _ _ _ _ _ _ _ _ _ _ _ _ effect]
 rfl

theorem received_source_energy
 (effect : type_of% (Actual.actual_material_stock_effect observation nontrivial half depth ordinal h H N producer packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down)) :
 (inner ℂ (receivedSourceR observation nontrivial half depth ordinal h H N producer packet)
  (Four.sourceA observation nontrivial half depth ordinal h H N)).re =
 -((observation.coordinate/2-1/4).re * ‖receivedSourceR observation nontrivial half depth ordinal h H N producer packet‖^2) := by
 rw [received_source_R_read _ _ _ _ _ _ _ _ _ _ effect]
 exact source_R_energy _ _ _ _ _ _ _ _

def receivedPhysicalSourceR
 (effect : type_of% (Actual.actual_material_stock_effect observation nontrivial half depth ordinal h H N producer packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down)) : BurnolPaAmbientCarrier :=
 ⟨receivedSourceR observation nontrivial half depth ordinal h H N producer packet,by
  rw [received_source_R_read _ _ _ _ _ _ _ _ _ _ effect]
  exact source_R_physical _ _ _ _ _ _ _ _⟩

theorem received_physical_R_read
 (effect : type_of% (Actual.actual_material_stock_effect observation nontrivial half depth ordinal h H N producer packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down)) :
 receivedPhysicalSourceR observation nontrivial half depth ordinal h H N producer packet effect =
 physicalSourceR observation nontrivial half depth ordinal h H N := Subtype.ext (received_source_R_read _ _ _ _ _ _ _ _ _ _ effect)

def receivedPaSourceR
 (effect : type_of% (Actual.actual_material_stock_effect observation nontrivial half depth ordinal h H N producer packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down)) :=
 burnolCompactCoPoissonClosedRange.toSubmodule.starProjection
  (receivedPhysicalSourceR observation nontrivial half depth ordinal h H N producer packet effect)

theorem received_Pa_unit_complete_energy
 (effect : type_of% (Actual.actual_material_stock_effect observation nontrivial half depth ordinal h H N producer packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down)) :
 -(inner ℂ (receivedPaSourceR observation nontrivial half depth ordinal h H N producer packet effect)
  (OriginalKDecodedPaRSourceSuccessor.decodedPaSource observation nontrivial half depth ordinal h H N).val).re =
 (observation.coordinate/2-1/4).re *
  (‖receivedPaSourceR observation nontrivial half depth ordinal h H N producer packet effect‖^2+
   ‖sourceRankCoefficient observation nontrivial half depth ordinal h H N • originalUnitRank observation nontrivial half‖^2) := by
 unfold receivedPaSourceR
 rw [received_physical_R_read _ _ _ _ _ _ _ _ _ _ effect]
 exact source_Pa_unit_complete_energy _ _ _ _ _ _ _ _

/-- The existing actual whole/next receives the new source-energy responsibility; no additional tick is asserted. -/
theorem received_whole_source_energy :
 ∃ whole : type_of% (Actual.sourceWholeAt observation nontrivial half depth ordinal h H N producer packet),
 (type_of% whole.actual_step) ∧ (type_of% whole.payment.strictDebit) ∧
 (type_of% whole.same_ledger) ∧ (type_of% whole.entry) ∧ (type_of% whole.whole_destination) ∧
 (type_of% whole.source_environment) ∧ (type_of% whole.source_expression) ∧
 (type_of% (Actual.source_born_root observation nontrivial half depth ordinal h H N producer packet)) ∧
 (type_of% (Actual.source_born_current observation nontrivial half depth ordinal h H N producer packet)) ∧
 (type_of% (Actual.actual_born_four_stock_increment observation nontrivial half depth ordinal h H N
  (Actual.fourFaceFactory producer) packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down (packet.2.2.2.down.symm ▸ ()))) ∧
 (type_of% (received_source_energy observation nontrivial half depth ordinal h H N producer packet (Actual.actual_material_stock_effect _ _ _ _ _ _ _ _ _ _ _ _ _))) ∧
 (type_of% (received_Pa_unit_complete_energy observation nontrivial half depth ordinal h H N producer packet (Actual.actual_material_stock_effect _ _ _ _ _ _ _ _ _ _ _ _ _))) := by
 exact Actual.consume_four_stock_receipt observation nontrivial half depth ordinal h H N producer packet fun whole write effect _trace =>
  ⟨whole,whole.actual_step,whole.payment.strictDebit,whole.same_ledger,whole.entry,whole.whole_destination,
   whole.source_environment,whole.source_expression,Actual.source_born_root _ _ _ _ _ _ _ _ _ _,Actual.source_born_current _ _ _ _ _ _ _ _ _ _,
   write,received_source_energy _ _ _ _ _ _ _ _ _ _ effect,received_Pa_unit_complete_energy _ _ _ _ _ _ _ _ _ _ effect⟩

variable (radius : ℝ)
theorem actual_received_whole_source_energy : type_of% (received_whole_source_energy observation nontrivial half depth ordinal h H N
 (Actual.actualParentFactory observation nontrivial half depth ordinal h)
 (Actual.actualParentPacket observation nontrivial half depth ordinal h H N radius)) := received_whole_source_energy _ _ _ _ _ _ _ _ _ _

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDecodedPaRSourceEnergy
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
