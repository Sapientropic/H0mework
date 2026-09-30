import H0mework.Fock.HistoryConditional.Update
import H0mework.Fock.HistoryConditional.NativePosteriorField

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperatorObservationAcquisition

open SourceCopyProgram (Index)
open SourceCopyTemporalBoundary (recordedPrefix)
open SourceCopyRecordedRecurrence (windowBound)
open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceConditionalModel (Actors nextRead)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem shorter_inventory (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :
    Fintype.card (Fin (index.val + 2)) < Fintype.card (Fin (windowBound runtime index steps + 1)) := by
  have order := SourceCopyRecordedRecurrence.address_mono (inventoryBound runtime) index
    (Nat.zero_le (inventoryBound runtime + steps))
  rw [first_address] at order
  change index.val ≤ SourceCopyRecordedRecurrence.cutoff runtime index steps at order
  rw [Fintype.card_fin, Fintype.card_fin]
  change index.val + 2 < SourceCopyRecordedRecurrence.cutoff runtime index steps + 2 + 1
  omega

theorem native_next (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (nonunit : index.val ≠ 0) (steps : Nat) :
    next runtime index nonunit steps (recordedPrefix runtime index steps (index.val + 1)
      (SourceJointClockGraph.read (SourceClockComplex.ofNative (SourceOperationNative.point runtime)))) =
        recordedPrefix runtime index steps (index.val + 1)
          (SourceJointClockGraph.read (SourceClockComplex.ofNative (SourceOperationNative.point runtime.tick.next))) := by
  rw [next_source, SourceJointClockGraph.native_next]

theorem native_acquired_next (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (nonunit : index.val ≠ 0) (steps : Nat) :
    next runtime index nonunit (steps + 2)
      (acquire runtime index nonunit steps (recordedPrefix runtime index (steps + 1) (index.val + 1)
        (SourceJointClockGraph.read (SourceClockComplex.ofNative (SourceOperationNative.point runtime))))
        (SourceCopyFutureUpdate.samples runtime index steps
          (SourceJointClockGraph.read (SourceClockComplex.ofNative (SourceOperationNative.point runtime))))) =
        recordedPrefix runtime index (steps + 2) (index.val + 1)
          (SourceJointClockGraph.read (SourceClockComplex.ofNative (SourceOperationNative.point runtime.tick.next))) := by
  rw [acquired_next, SourceJointClockGraph.native_next]

theorem field_cost (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (nonunit : index.val ≠ 0) (steps depth : Nat) (key : ZMod 2)
    (supported : key ∈ ((historyPMF (inventoryBound runtime)).map (fun actor : Actors runtime => (actor.val : ZMod 2))).support) :
    let value := SourceConditionalNativeKeys.decoder runtime depth (SourceConditionalNativeKeys.observed depth key)
    (∑ actor : Actors runtime, ((SourceConditionalNativeKeys.generate (inventoryBound runtime) key).2 actor : ℝ) *
      ‖SourceConditionalVector.realizeModel runtime (nextRead runtime actor) -
        SourceCopyCurrentCoordinates.realize runtime index steps
          (decode runtime index nonunit steps (recordedPrefix runtime index steps (index.val + 1) value))‖ ^ 2) =
    (∑ actor : Actors runtime, ((SourceConditionalNativeKeys.generate (inventoryBound runtime) key).2 actor : ℝ) *
      ‖SourceConditionalVector.realizeModel runtime (nextRead runtime actor) - value‖ ^ 2) +
        ‖SourceCopyCurrentCoordinates.residual runtime index steps value‖ ^ 2 := by
  dsimp only
  rw [SourceConditionalNativePosterior.field_error runtime depth key supported, decode_source]
  rfl

theorem model_feedback {Key : Type*} [DecidableEq Key] (runtime : LivingRuntimeState process)
    (index : Index (inventoryBound runtime)) (nonunit : index.val ≠ 0) (steps : Nat) (read : Nat → Key) (key : Key) :
    let value := SourceConditionalNativePosterior.decoder runtime read key
    SourceCopyNativeSharedUpdate.modelStep runtime.tick.next
      (SourceGeneratedActionObservationHistory.projection SourceJointClockGraph.action.toLinearMap
        (SourceCopyCurrentCoordinates.jointObserver runtime.tick.next)
        (SourceCopyCurrentCoordinates.realize runtime index steps
          (decode runtime index nonunit steps (recordedPrefix runtime index steps (index.val + 1) value)) +
            SourceCopyCurrentCoordinates.residual runtime index steps value)) =
        SourceConditionalNativePosterior.effect runtime read key := by
  dsimp only
  rw [decode_source]
  have rebuilt := SourceCopyCurrentCoordinates.reconstruction runtime index steps (SourceConditionalNativePosterior.decoder runtime read key)
  change SourceCopyCurrentCoordinates.realize runtime index steps
    (SourceCopyCurrentCoordinates.sourceRead runtime index steps (SourceConditionalNativePosterior.decoder runtime read key)) +
    SourceCopyCurrentCoordinates.residual runtime index steps (SourceConditionalNativePosterior.decoder runtime read key) = _ at rebuilt
  rw [rebuilt, SourceConditionalNativePosterior.decoder, SourceConditionalStream.project_realization]
  rfl

end
end SourceOperatorObservationAcquisition
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
