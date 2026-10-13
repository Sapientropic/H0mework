import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKBoundaryNextActualSourceDelta.Whole
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKBoundaryNextActualSourceDelta.Future.Source
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKBoundaryNextActualSourceDelta.Material.Consumer
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
universe v
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKBoundaryNextActualSourceDelta
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open Complex MeasureTheory Filter
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
namespace D
export OriginalKWholePaNativeRankSourceUpdate
 (actualMaterialActorBranches actualMaterialPaCoefficient actualMaterialNonPaR actualMaterialSourceDelta
 actualMaterialCrossEffect actualMaterialREffect actualMaterialInheritedREffect
 actual_material_actor_branches actual_material_R_effect_partition actualSourceDeltaBranches
 actual_original_cross_consumes_native_rank_update)
end D
local instance materialReceiverGroups (grade : Nat) (target : Unit) : AddCommGroup (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade target
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
variable (producer : SF.Factory (PairValue C.Value) C.Var ())
variable (packet : AP.AdmissionPacket (W := PairValue C.Value) (X := C.Var) (s := ()))
variable (H N : ℝ)

/-- This readout eliminates the received actual material actor partition before taking prices. -/
theorem cross_from_received_material_actor
 (actor : type_of% (D.actual_material_actor_branches observation nontrivial half producer
  packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down H N))
 (nonnegative : 0 ≤ H) (ordered : H ≤ N) :
 OriginalKPairedResponseGramAction.originalKernelCross observation nontrivial half N -
 OriginalKPairedResponseGramAction.originalKernelCross observation nontrivial half H =
 D.actualMaterialCrossEffect observation nontrivial half producer packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down H N := by
 have price : D.actualMaterialCrossEffect observation nontrivial half producer packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down H N =
  OriginalKWholePaNativeRankSourceUpdate.actualWholePaRankSourceCharacterUpdate observation nontrivial half H N := by
  unfold D.actualMaterialCrossEffect D.actualMaterialPaCoefficient D.actualMaterialNonPaR D.actualMaterialSourceDelta
  rw [actor]
  rfl
 exact (D.actual_original_cross_consumes_native_rank_update observation nontrivial half H N nonnegative ordered).trans price.symm

theorem current_from_received_material_actor
 (actor : type_of% (D.actual_material_actor_branches observation nontrivial half producer
  packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down H N))
 (nonnegative : 0 ≤ H) (ordered : H ≤ N) (bounded : N ≤ Real.log 2) (n : Nat) :
 (OriginalKWaveSourceAction.actualBandSourceFiniteCharacter observation nontrivial half N
    (nonnegative.trans ordered) bounded n +
  OriginalKRealCoordinateSourceUnit.actualUnweightedCharacterResidual observation nontrivial half N
    (nonnegative.trans ordered) bounded n) -
 (OriginalKWaveSourceAction.actualBandSourceFiniteCharacter observation nontrivial half H nonnegative (ordered.trans bounded) n +
  OriginalKRealCoordinateSourceUnit.actualUnweightedCharacterResidual observation nontrivial half H nonnegative (ordered.trans bounded) n) =
 D.actualMaterialCrossEffect observation nontrivial half producer packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down H N := by
 have current := OriginalKWholePaNativeRankSourceUpdate.actual_current_consumes_native_rank_update
  observation nontrivial half H N nonnegative ordered bounded n
 rw [←D.actual_original_cross_consumes_native_rank_update observation nontrivial half H N nonnegative ordered,
  cross_from_received_material_actor observation nontrivial half producer packet H N actor nonnegative ordered] at current
 exact current

/-- All material and whole fields are generated on the same exact source packet. -/
def consume_actual_actor_material {Result : Sort v}
 (consumer : (whole : type_of% (actorWholeAt observation nontrivial half producer packet H N)) →
  type_of% (D.actual_material_R_effect_partition observation nontrivial half producer
   packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down H N) →
  type_of% (D.actual_material_actor_branches observation nontrivial half producer
   packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down H N) → Result) : Result :=
 consumer (actorWholeAt observation nontrivial half producer packet H N)
  (D.actual_material_R_effect_partition observation nontrivial half producer
   packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down H N)
  (D.actual_material_actor_branches observation nontrivial half producer
   packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down H N)

theorem actual_material_whole_consumer (nonnegative : 0 ≤ H) (ordered : H ≤ N) (bounded : N ≤ Real.log 2) :
 ∃ whole : type_of% (actorWholeAt observation nontrivial half producer packet H N),
 (type_of% whole.actual_step) ∧ (type_of% whole.same_ledger) ∧ (type_of% whole.same_visit) ∧
 (type_of% whole.entry) ∧ (type_of% whole.whole_destination) ∧
 (type_of% whole.source_environment) ∧ (type_of% whole.source_expression) ∧
 (type_of% (D.actual_material_R_effect_partition observation nontrivial half producer
  packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down H N)) ∧
 OriginalKPairedResponseGramAction.originalKernelCross observation nontrivial half N -
 OriginalKPairedResponseGramAction.originalKernelCross observation nontrivial half H =
 D.actualMaterialCrossEffect observation nontrivial half producer packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down H N ∧
 ((n : Nat) → type_of% (current_from_received_material_actor observation nontrivial half producer packet H N
  (D.actual_material_actor_branches observation nontrivial half producer packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down H N)
  nonnegative ordered bounded n)) := by
 exact consume_actual_actor_material observation nontrivial half producer packet H N
  fun whole effect actor =>
  ⟨whole,whole.actual_step,whole.same_ledger,whole.same_visit,whole.entry,whole.whole_destination,
   whole.source_environment,whole.source_expression,effect,
   cross_from_received_material_actor _ _ _ _ _ _ _ actor nonnegative ordered,
   current_from_received_material_actor _ _ _ _ _ _ _ actor nonnegative ordered bounded⟩

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKBoundaryNextActualSourceDelta
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
