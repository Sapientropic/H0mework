import H0mework.Versions.X.Fock.PrimeFieldJoint.BornSource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedBornDecoder

open SourceGeneratedAcquisitionMeasure SourceGeneratedAcquisitionContinuation SourceGeneratedAcquisitionJoint
open SourceGeneratedActionWords.Fock.OriginalHilbert SourceGeneratedJointTime SourceGeneratedJointClockGraph
open SourceGeneratedAtomicObservation SourceGeneratedRuntimeHistoryProbability
open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem fresh_decode (runtime : LivingRuntimeState process) (depth : Nat) :
    SourceGeneratedJointFiniteDecoder.decode depth (inventoryBound (next runtime)) (target runtime depth) = newest runtime depth := by
  rw [target, SourceGeneratedJointFiniteDecoder.original_K]
  exact SourceGeneratedRecordFrame.original_time_recovery depth _ _

theorem fresh_residual_zero (runtime : LivingRuntimeState process) (depth : Nat) :
    SourceJointFiniteDecoder.residual (inventoryBound (next runtime)) (target runtime depth) = 0 :=
  SourceGeneratedJointFiniteDecoder.next_residual_zero depth _ _

theorem fresh_samples (runtime : LivingRuntimeState process) (depth : Nat) :
    SourceJointFiniteDecoder.decode (inventoryBound (next runtime)) (target runtime depth) =
      cotest (historyPMF (inventoryBound (next runtime))) (Fin.last (inventoryBound (next runtime))) := by
  rw [← SourceGeneratedJointFiniteDecoder.decode_actor depth, fresh_decode, newest_samples]

theorem fresh_next_actual (runtime : LivingRuntimeState process) (depth : Nat) :
    Actor.nextRead depth (inventoryBound (next runtime)) (Fin.last (inventoryBound (next runtime))) =
      fieldPoint nativeStep (rawWords depth) ((next runtime).tick.next.current.visit.current : Current) := by
  have same : runtimeAt (inventoryBound (next runtime)) = next runtime := by
    rw [inventory_bound]
    exact (runtime_eq (next runtime)).symm
  exact (next_sample_actual depth (inventoryBound (next runtime))
    (Fin.last (inventoryBound (next runtime)))).trans
      (congrArg (fun current : LivingRuntimeState process =>
        fieldPoint nativeStep (rawWords depth) (current.tick.next.current.visit.current : Current)) same)

theorem target_actual_read (runtime : LivingRuntimeState process) (depth : Nat) :
    timeTransfer depth (inventoryBound (next runtime)) (newest runtime depth)
      (fieldPoint nativeStep (rawWords depth) ((next runtime).tick.next.current.visit.current : Current)) = 1 := by
  rw [← fresh_next_actual]
  have square := DFunLike.congr_fun (SourceGeneratedRecordFrame.joint_action_square depth (inventoryBound (next runtime)))
    (newest runtime depth)
  change Actor.nextPullback depth (inventoryBound (next runtime))
    (timeTransfer depth (inventoryBound (next runtime)) (newest runtime depth)) =
      Actor.currentPullback depth (inventoryBound (next runtime)) (newest runtime depth) at square
  rw [newest_samples] at square
  have sample := congrArg (fun value : SourceWeightedRecovery.Space (historyPMF (inventoryBound (next runtime))) =>
    value (Fin.last (inventoryBound (next runtime)))) square
  rw [Actor.nextPullback_at, cotest_at _ _ (SourceUniformFibreVariance.source_positive _ _)] at sample
  exact sample

end
end SourceGeneratedBornDecoder
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
