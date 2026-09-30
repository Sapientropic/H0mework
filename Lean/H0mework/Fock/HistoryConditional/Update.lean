import H0mework.Fock.HistoryConditional.OperatorAcquisitionForecast
import H0mework.Fock.CopyGraph.FutureUpdateObservation

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperatorObservationAcquisition

open SourceCopyProgram (Index)
open SourceCopyTemporalBoundary (recordedPrefix)
open SourceGeneratedAcquisitionContinuation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def acquire (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (nonunit : index.val ≠ 0) (steps : Nat) (previous : Window runtime index)
    (observed : SourceCopyFutureUpdate.Samples runtime index) : Window runtime index :=
  recordedPrefix runtime index (steps + 2) (index.val + 1)
    (SourceCopyCurrentCoordinates.realize runtime index (steps + 2)
      (SourceCopyFutureUpdate.update runtime index steps (decode runtime index nonunit (steps + 1) previous) observed))

theorem acquire_source (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (nonunit : index.val ≠ 0) (steps : Nat) (value : SourceJointClockGraph.Carrier) :
    acquire runtime index nonunit steps (recordedPrefix runtime index (steps + 1) (index.val + 1) value)
      (SourceCopyFutureUpdate.samples runtime index steps value) =
        recordedPrefix runtime index (steps + 2) (index.val + 1) value := by
  rw [acquire, decode_source]
  have paid := SourceCopyFutureUpdate.update_source runtime index steps value
  change SourceCopyFutureUpdate.update runtime index steps (SourceCopyCurrentCoordinates.sourceRead runtime index (steps + 1) value)
    (SourceCopyFutureUpdate.samples runtime index steps value) = SourceCopyCurrentCoordinates.sourceRead runtime index (steps + 2) value at paid
  rw [paid]
  exact retained_window runtime index (steps + 2) (index.val + 1) value

theorem acquired_next (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (nonunit : index.val ≠ 0) (steps : Nat) (value : SourceJointClockGraph.Carrier) :
    next runtime index nonunit (steps + 2)
      (acquire runtime index nonunit steps (recordedPrefix runtime index (steps + 1) (index.val + 1) value)
        (SourceCopyFutureUpdate.samples runtime index steps value)) =
      recordedPrefix runtime index (steps + 2) (index.val + 1) (SourceJointClockGraph.action value) := by
  rw [acquire_source, next_source]

theorem residual_budget (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (nonunit : index.val ≠ 0) (steps : Nat) (value : SourceJointClockGraph.Carrier) :
    ‖SourceCopyFutureUpdate.block runtime index steps value‖ ^ 2 +
      ‖value - SourceCopyCurrentCoordinates.realize runtime index (steps + 2)
        (decode runtime index nonunit (steps + 2)
          (acquire runtime index nonunit steps (recordedPrefix runtime index (steps + 1) (index.val + 1) value)
            (SourceCopyFutureUpdate.samples runtime index steps value)))‖ ^ 2 =
      ‖value - SourceCopyCurrentCoordinates.realize runtime index (steps + 1)
        (decode runtime index nonunit (steps + 1) (recordedPrefix runtime index (steps + 1) (index.val + 1) value))‖ ^ 2 := by
  rw [acquire_source, decode_source, decode_source]
  exact SourceCopyFutureUpdate.block_budget runtime index steps value

theorem acquired_strict (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (nonunit : index.val ≠ 0) (steps : Nat) :
    let value := SourceCopyRecordedRecurrence.hidden runtime index (steps + 1)
    ‖value - SourceCopyCurrentCoordinates.realize runtime index (steps + 2)
      (decode runtime index nonunit (steps + 2)
        (acquire runtime index nonunit steps (recordedPrefix runtime index (steps + 1) (index.val + 1) value)
          (SourceCopyFutureUpdate.samples runtime index steps value)))‖ ^ 2 <
      ‖value - SourceCopyCurrentCoordinates.realize runtime index (steps + 1)
        (decode runtime index nonunit (steps + 1) (recordedPrefix runtime index (steps + 1) (index.val + 1) value))‖ ^ 2 := by
  dsimp only
  rw [acquire_source, decode_source, decode_source]
  exact SourceCopyFutureUpdate.tail_strict runtime index steps

end
end SourceOperatorObservationAcquisition
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
