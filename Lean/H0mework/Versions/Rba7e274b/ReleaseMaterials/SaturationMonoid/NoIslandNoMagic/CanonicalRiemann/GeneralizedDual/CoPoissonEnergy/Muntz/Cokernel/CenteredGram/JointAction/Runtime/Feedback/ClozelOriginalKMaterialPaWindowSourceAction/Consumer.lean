import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKMaterialPaWindowSourceAction.Material
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKMaterialPaWindowSourceAction.Root
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKMaterialPaWindowSourceAction.Price
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKMaterialPaWindowSourceAction.Trace
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKMaterialPaWindowSourceAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual BurnolPhysicalState
local instance paFinalComplete : CompleteSpace BurnolPaAmbientCarrier := by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local instance paFinalGroups (grade : Nat) (target : Unit) :
 AddCommGroup (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade target

theorem consume_received_pa_whole_trace (factory : SF.Factory (PairValue C.Value) C.Var ())
 (packet : AP.AdmissionPacket (W:=PairValue C.Value) (X:=C.Var) (s:=())) (source : D.SourceBranches)
 {Target : Prop} (consumer : (whole : type_of% (paWholeAt factory packet source)) →
 (write : type_of% (pa_stock_generated_source_delta factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down source (packet.2.2.2.down.symm ▸ ()))) →
 (trace : type_of% (actual_born_delta_source_trace factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down source (packet.2.2.2.down.symm ▸ ()))) → Target) : Target :=
 consumer (paWholeAt _ _ _)
  (pa_stock_generated_source_delta _ _ _ _ _ _ _)
  (actual_born_delta_source_trace _ _ _ _ _ _ _)

theorem received_pa_trace_window_whole (factory : SF.Factory (PairValue C.Value) C.Var ())
 (packet : AP.AdmissionPacket (W:=PairValue C.Value) (X:=C.Var) (s:=())) (source : D.SourceBranches) (radius t : ℝ) :
 ∃ whole : type_of% (paWholeAt factory packet source),
 (type_of% whole.actual_step) ∧ (type_of% whole.same_ledger) ∧ (type_of% whole.same_visit) ∧
 (type_of% whole.entry) ∧ (type_of% whole.whole_destination) ∧ (type_of% whole.source_environment) ∧ (type_of% whole.source_expression) ∧
 (type_of% (pa_stock_source_window factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down source (packet.2.2.2.down.symm ▸ ()) radius)) ∧
 (type_of% (received_two_mean_prices factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down source (packet.2.2.2.down.symm ▸ ()) (pa_stock_generated_source_delta _ _ _ _ _ _ _))) ∧
 (type_of% (received_moving_mean_price factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down source (packet.2.2.2.down.symm ▸ ()) (pa_stock_generated_source_delta _ _ _ _ _ _ _) t)) := by
 exact consume_received_pa_whole_trace factory packet source fun whole write trace =>
  ⟨whole,whole.actual_step,whole.same_ledger,whole.same_visit,whole.entry,whole.whole_destination,whole.source_environment,whole.source_expression,
   source_window_from_received_trace source _ trace radius,
   received_two_mean_prices _ _ _ _ _ _ _ write,
   received_moving_mean_price _ _ _ _ _ _ _ write t⟩

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat) (h H N : ℝ)

theorem actual_material_Pa_source_whole_next_future (radius t : ℝ) (futureOrdinal : Nat) :
 (type_of% (received_pa_trace_window_whole
  (actualParentRFactory observation nontrivial half depth ordinal h)
  (actualParentBornPacket observation nontrivial half depth ordinal h H N)
  (actualParentMaterialREffect observation nontrivial half depth ordinal h H N) radius t)) ∧
 (type_of% (pa_source_root (actualParentRFactory observation nontrivial half depth ordinal h)
  (actualParentBornPacket observation nontrivial half depth ordinal h H N)
  (actualParentMaterialREffect observation nontrivial half depth ordinal h H N))) ∧
 (type_of% (pa_source_current (actualParentRFactory observation nontrivial half depth ordinal h)
  (actualParentBornPacket observation nontrivial half depth ordinal h H N)
  (actualParentMaterialREffect observation nontrivial half depth ordinal h H N))) ∧
 ((auxiliary : OriginalKBoundaryNextActualSourceDelta.SF.Seed
  (L.Value (PairValue C.Value) (actualPaBornPacket observation nontrivial half depth ordinal h H N).1) C.Var () 0) → type_of%
  (pa_packet_source_history (actualParentRFactory observation nontrivial half depth ordinal h)
   (actualParentBornPacket observation nontrivial half depth ordinal h H N)
   (actualParentMaterialREffect observation nontrivial half depth ordinal h H N) auxiliary)) ∧
 ((history : List PUnit) → (target : Nat) → type_of% (actual_Pa_material_all_future observation nontrivial half depth ordinal h H N futureOrdinal history target)) := by
 exact ⟨received_pa_trace_window_whole _ _ _ radius t,pa_source_root _ _ _,pa_source_current _ _ _,
  pa_packet_source_history _ _ _,actual_Pa_material_all_future _ _ _ _ _ _ _ _ futureOrdinal⟩

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKMaterialPaWindowSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
