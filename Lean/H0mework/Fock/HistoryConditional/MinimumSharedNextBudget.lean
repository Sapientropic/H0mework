import H0mework.Fock.HistoryConditional.MinimumSharedNextFamily
import H0mework.Fock.CopyGraph.SharedNextGain

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceMinimumSharedNext

open SourceCopyCurrentCoordinates (maximumIndex realize residual)
open SourceCopyTemporalBoundary (recordedPrefix)
open SourceOperatorObservationAcquisition (decode)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem step_realize (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (previous : Window runtime) :
    realize runtime.tick.next (maximumIndex runtime.tick.next) 0
      (decode runtime.tick.next (maximumIndex runtime.tick.next) (next_nonunit runtime) 0 (step runtime nonunit previous)) =
        SourceJointClockGraph.action
          (realize runtime (maximumIndex runtime) 0 (decode runtime (maximumIndex runtime) nonunit 0 previous)) := by
  rw [decode_step]
  exact SourceCopyNativeSharedUpdate.step_realize runtime _

theorem step_reconstruction (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (target : SourceJointClockGraph.Carrier) :
    realize runtime.tick.next (maximumIndex runtime.tick.next) 0
      (decode runtime.tick.next (maximumIndex runtime.tick.next) (next_nonunit runtime) 0
        (step runtime nonunit (recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1) target))) +
      SourceJointClockGraph.action (residual runtime (maximumIndex runtime) 0 target) =
        SourceJointClockGraph.action target := by
  rw [step_realize, SourceOperatorObservationAcquisition.decode_source, ← map_add]
  exact congrArg SourceJointClockGraph.action (SourceCopyCurrentCoordinates.reconstruction runtime (maximumIndex runtime) 0 target)

theorem step_loss (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (target : SourceJointClockGraph.Carrier) :
    ‖SourceJointClockGraph.action target -
      realize runtime.tick.next (maximumIndex runtime.tick.next) 0
        (decode runtime.tick.next (maximumIndex runtime.tick.next) (next_nonunit runtime) 0
          (step runtime nonunit (recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1) target)))‖ ^ 2 =
      ‖residual runtime (maximumIndex runtime) 0 target‖ ^ 2 := by
  have rebuilt := step_reconstruction runtime nonunit target
  calc
    _ = ‖SourceJointClockGraph.action (residual runtime (maximumIndex runtime) 0 target)‖ ^ 2 := by
      rw [← rebuilt, add_sub_cancel_left]
    _ = _ := SourceCopySharedNext.tail_time_energy runtime target

theorem step_energy (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (previous : Window runtime) :
    let coordinates := decode runtime (maximumIndex runtime) nonunit 0 previous
    ‖realize runtime.tick.next (maximumIndex runtime.tick.next) 0
      (decode runtime.tick.next (maximumIndex runtime.tick.next) (next_nonunit runtime) 0 (step runtime nonunit previous))‖ ^ 2 =
      ‖realize runtime (maximumIndex runtime) 0 coordinates‖ ^ 2 + ‖coordinates.2.1‖ ^ 2 +
        2 * (inner ℂ coordinates.2.2 coordinates.2.1).re := by
  dsimp only
  rw [decode_step]
  exact SourceCopyNativeSharedUpdate.step_energy runtime _

end
end SourceMinimumSharedNext
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
