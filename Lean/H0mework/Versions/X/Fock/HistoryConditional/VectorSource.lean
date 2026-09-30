import H0mework.Versions.X.Fock.HistoryConditional.VectorData
import H0mework.Versions.X.Fock.HistoryConditional.VectorAction

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalVector

open SourceConditionalModel (Actors NextModel nextRead)
open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceCopyCurrentCoordinates (maximumIndex sourceRead realize jointModelEquiv)
open SourceCopyNativeModelStep (sourceValue)
open SourceCopyRecordedRecurrence (cutoff)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def actor (runtime : LivingRuntimeState process) (index : Actors runtime) : SourceJointClockGraph.Carrier :=
  sourceValue (runtimeSeed.advance index.val)

theorem actor_material (runtime : LivingRuntimeState process) (index : Actors runtime) :
    SourceJointClockGraph.action (actor runtime index) =
      sourceValue ((history runtimeSeed (inventoryBound runtime)).stageAt index).next := by
  rw [actor, SourceCopyNativeModelStep.source_value_next]
  rfl

private theorem realize_included (runtime origin : LivingRuntimeState process)
    (included : origin.state ≤ cutoff runtime (maximumIndex runtime) 0) :
    realize runtime (maximumIndex runtime) 0
      (sourceRead runtime (maximumIndex runtime) 0 (sourceValue origin)) = sourceValue origin := by
  apply (SourceCopyCurrentCoordinates.complete_fibre runtime (maximumIndex runtime) 0 _ _).mpr
  refine ⟨SourceCopyCurrentCoordinates.realize_source _ _ _ _, ?_⟩
  intro coordinate beyond
  change SourceCopyCurrentCoordinates.hilbertLift runtime (maximumIndex runtime) 0 _ coordinate = _
  rw [SourceCopyCurrentCoordinates.hilbert_lift_outside _ _ _ _ _ beyond,
    SourceCopyPhaseRecovery.native_hilbert, if_neg (ne_of_gt (lt_of_le_of_lt included beyond))]

theorem realized_next (runtime : LivingRuntimeState process) (index : Actors runtime) :
    realizeModel runtime (nextRead runtime index) = SourceJointClockGraph.action (actor runtime index) := by
  rw [SourceConditionalModel.next_action]
  change realize runtime.tick.next (maximumIndex runtime.tick.next) 0
    (jointModelEquiv runtime.tick.next
      (SourceGeneratedActionObservationHistory.projection SourceJointClockGraph.action.toLinearMap
        (SourceCopyCurrentCoordinates.jointObserver runtime.tick.next)
        (SourceJointClockGraph.action (sourceValue (runtimeSeed.advance index.val))))) = _
  rw [SourceCopyCurrentCoordinates.joint_model_source, SourceCopyNativeModelStep.source_value_next]
  change realize runtime.tick.next (maximumIndex runtime.tick.next) 0
    (sourceRead runtime.tick.next (maximumIndex runtime.tick.next) 0
      (sourceValue (runtimeAt (index.val + 1)))) = SourceJointClockGraph.action (actor runtime index)
  have included : (runtimeAt (index.val + 1)).state ≤ cutoff runtime.tick.next (maximumIndex runtime.tick.next) 0 := by
    rw [runtimeAt_state]
    have bound := SourceCopyCurrentCoordinates.maximum_cutoff runtime.tick.next
    rw [inventory_bound] at bound
    change cutoff runtime.tick.next (maximumIndex runtime.tick.next) 0 + 1 = (runtime.state + 1 + 1) ^ 2 at bound
    have indexBound : index.val < runtime.state + 1 := by
      have := index.isLt
      have := inventory_bound runtime
      omega
    have low := Nat.mul_le_mul_left (runtime.state + 2) (Nat.succ_le_succ (Nat.zero_le (runtime.state + 1)))
    change (runtime.state + 2) * 1 ≤ (runtime.state + 2) * (runtime.state + 2) at low
    rw [Nat.mul_one, ← Nat.pow_two] at low
    change cutoff runtime.tick.next (maximumIndex runtime.tick.next) 0 + 1 = (runtime.state + 2) ^ 2 at bound
    exact Nat.le_of_succ_le_succ ((Nat.succ_le_succ indexBound).trans (low.trans_eq bound.symm))
  rw [realize_included runtime.tick.next _ included, actor, SourceCopyNativeModelStep.source_value_next]
  rfl

theorem actor_mass (runtime : LivingRuntimeState process) (index : Actors runtime) :
    SourceVectorMoment.massMap (actor runtime index) = 1 := by
  change SourceMassCompletion.massRead (SourceJointClockGraph.joint (actor runtime index)) = 1
  rw [actor, sourceValue, SourceJointClockGraph.joint_source, SourceClockComplex.joint_native,
    SourceMassCompletion.massRead_native]
  simp only [SourceOperationNative.point, SourceOperationNative.statePoint, SourceSuccessorBoundary.mass_single, Int.cast_one]

end
end SourceConditionalVector
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
