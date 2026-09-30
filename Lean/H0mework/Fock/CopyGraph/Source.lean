import H0mework.Fock.CopyGraph.SharedHistoryEvolution
import H0mework.Fock.CopyGraph.Native

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopySharedHistory

open SourceCopyCurrentCoordinates (Coordinates maximumIndex shared expand)
open SourceCopySharedNext (nativePacket update)
open SourceGeneratedAcquisitionContinuation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def history (runtime : LivingRuntimeState process) : (stage : Nat) →
    Coordinates (runtime.advance stage) (maximumIndex (runtime.advance stage)) 0 :=
  SourceCopyNativeSharedUpdate.trajectory runtime (shared runtime)

theorem history_native_step (runtime : LivingRuntimeState process) (stage : Nat) :
    history runtime (stage + 1) = SourceCopyNativeSharedUpdate.step (runtime.advance stage) (history runtime stage) :=
  SourceCopyNativeSharedUpdate.trajectory_step runtime (shared runtime) stage

theorem history_action (runtime : LivingRuntimeState process) (stage : Nat) :
    SourceCopyCurrentCoordinates.realize (runtime.advance (stage + 1)) (maximumIndex (runtime.advance (stage + 1))) 0
      (history runtime (stage + 1)) =
      SourceJointClockGraph.action (SourceCopyCurrentCoordinates.realize (runtime.advance stage) (maximumIndex (runtime.advance stage)) 0
        (history runtime stage)) := by
  dsimp only [history]
  rw [SourceCopyNativeSharedUpdate.trajectory_realize, SourceCopyNativeSharedUpdate.trajectory_realize,
    SourceCopyTimeModel.time_succ]

theorem history_source (runtime : LivingRuntimeState process) (stage : Nat) : history runtime stage = shared (runtime.advance stage) := by
  induction stage with
  | zero => exact SourceCopyNativeSharedUpdate.trajectory_zero runtime (shared runtime)
  | succ stage previous =>
    rw [history_native_step, previous, SourceCopyCurrentCoordinates.shared_source,
      SourceCopyNativeSharedUpdate.step_source, SourceCopyCurrentCoordinates.shared_source]
    rfl

theorem history_step (runtime : LivingRuntimeState process) (stage : Nat) :
    history runtime (stage + 1) = update (runtime.advance stage) (history runtime stage) (nativePacket (runtime.advance stage)) := by
  rw [history_source, history_source]
  exact (SourceCopySharedNext.update_native (runtime.advance stage)).symm

theorem history_family (runtime : LivingRuntimeState process) (stage : Nat) :
    expand (runtime.advance stage) (history runtime stage) = SourceCopyLiveModelFamily.family (runtime.advance stage) := by
  rw [history_source, SourceCopyCurrentCoordinates.shared_family]

theorem history_at_material (runtime : LivingRuntimeState process) (stage : Nat)
    (material : SourceGeneratedRuntimeMaterialStageAt (runtime.advance stage)) :
    history runtime (stage + 1) = shared material.next := history_source runtime (stage + 1)

end
end SourceCopySharedHistory
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
