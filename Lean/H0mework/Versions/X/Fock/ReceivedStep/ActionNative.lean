import H0mework.Versions.X.Fock.ReceivedStep.ActionValue

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceReceivedConditionalStep

open SourceGeneratedAcquisitionContinuation
open SourceCopyProgram (Index)
open SourceCopyCurrentCoordinates (maximumIndex residual)
open SourceCopyRecordedRecurrence (cutoff)
open SourceConditionalModel (Actors nextRead)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem actor_residual_zero (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (nonunit : index.val ≠ 0) (actor : Actors runtime) :
    residual runtime index 0 (SourceConditionalVector.realizeModel runtime (nextRead runtime actor)) = 0 := by
  have included : actor.val + 1 ≤ cutoff runtime index 0 :=
    Nat.le_of_lt_succ ((SourceRationalWindowReadout.weightAddress (inventoryBound runtime) index.val nonunit actor).isLt.trans_eq
      (current_extent runtime index))
  rw [SourceConditionalVector.realized_next, SourceConditionalVector.actor, SourceCopyNativeModelStep.source_value_next]
  change residual runtime index 0 (SourceCopyNativeModelStep.sourceValue (runtimeAt (actor.val + 1))) = 0
  apply (SourceCopyCurrentCoordinates.complete_fibre runtime index 0 _ 0).mpr
  refine ⟨?_, ?_⟩
  · rw [SourceCopyCurrentCoordinates.residual_source, map_zero]
  · intro coordinate beyond
    rw [SourceCopyCurrentCoordinates.residual_outside _ _ _ _ _ beyond, SourceCopyPhaseRecovery.native_hilbert,
      runtimeAt_state, if_neg (ne_of_gt (lt_of_le_of_lt included beyond))]
    rfl

theorem decoder_residual_zero (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (nonunit : index.val ≠ 0) {Key : Type*} [DecidableEq Key] (read : Nat → Key) (key : Key) :
    residual runtime index 0 (SourceConditionalNativePosterior.decoder runtime read key) = 0 := by
  simp only [SourceConditionalNativePosterior.decoder, SourceConditionalNativePosterior.model, map_sum, map_smul,
    actor_residual_zero runtime index nonunit, smul_zero, Finset.sum_const_zero]

theorem received_value_source (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (nonunit : index.val ≠ 0) {Key : Type*} [DecidableEq Key] (read : Nat → Key) (key : Key) :
    completeValue runtime index 0 (SourceRationalWindowReadout.decode (inventoryBound runtime) index.val
      (fun phase => SourceFiniteObserverCalculation.posteriorCalculate (inventoryBound runtime) (index.val + 1) 0 phase.val read key)) =
        SourceConditionalNativePosterior.decoder runtime read key := by
  have actual := SourceRationalWindowReadout.decoded_reconstruction runtime index nonunit read key
  rw [decoder_residual_zero runtime index nonunit, add_zero] at actual
  exact actual

def completeUpdatedValue (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (nonunit : index.val ≠ 0) {Key : Type*} [DecidableEq Key]
    (received : Key → SourceRationalWindowReadout.Samples (inventoryBound runtime) (index.val + 1)) (added key : Key) :
    SourceJointClockGraph.Carrier :=
  completeValue runtime.tick.next (maximumIndex runtime.tick.next) 0
    (nextData runtime index (receiveState (inventoryBound runtime) index.val nonunit received key).1 (decide (key = added))
      (SourceRationalWindowReadout.decode (inventoryBound runtime) index.val (received key)))

theorem updated_value_source (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (nonunit : index.val ≠ 0) {Key : Type*} [DecidableEq Key] (read : Nat → Key) (key : Key) :
    completeUpdatedValue runtime index nonunit
      (fun value phase => SourceFiniteObserverCalculation.posteriorCalculate
        (inventoryBound runtime) (index.val + 1) 0 phase.val read value)
      (read runtime.tick.next.state) key = SourceConditionalNativePosterior.decoder runtime.tick.next read key := by
  have count := congrArg (fun state : SourceConditionalNativeObservers.State Key (inventoryBound runtime) => (state key).1)
    (state_source runtime index nonunit read)
  have receipt := congrArg read ((inventory_bound runtime.tick.next).symm.trans (SourceActualImageStep.next_bound runtime))
  rw [completeUpdatedValue, next_value_source, received_value_source runtime index nonunit read key,
    count, receipt, SourceConditionalNativeBirth.decoder_next]
  simp only [decide_eq_true_eq]

end
end SourceReceivedConditionalStep
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
