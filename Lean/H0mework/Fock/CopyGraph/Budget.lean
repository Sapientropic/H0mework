import H0mework.Fock.CopyGraph.SharedNextSourceStepModel
import H0mework.Fock.CopyGraph.Source

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopySharedHistory

open SourceCopyCurrentCoordinates (maximumIndex jointObserver jointModelEquiv)
open SourceCopySharedNext (nativePacket)
open SourceCopyNativeModelStep (sourceValue)
open SourceGeneratedAcquisitionContinuation SourceGeneratedActionObservationHistory
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def modelHistory (runtime : LivingRuntimeState process) (stage : Nat) :
    Model SourceJointClockGraph.action.toLinearMap (jointObserver (runtime.advance stage)) :=
  (jointModelEquiv (runtime.advance stage)).symm (history runtime stage)

theorem model_history_step (runtime : LivingRuntimeState process) (stage : Nat) :
    SourceCopySharedNext.updateModel (runtime.advance stage) (modelHistory runtime stage) (nativePacket (runtime.advance stage)) =
      modelHistory runtime (stage + 1) := by
  rw [SourceCopySharedNext.updateModel, modelHistory, LinearEquiv.apply_symm_apply]
  exact congrArg (jointModelEquiv (runtime.advance (stage + 1))).symm (history_step runtime stage).symm

theorem model_history_native_step (runtime : LivingRuntimeState process) (stage : Nat) :
    SourceCopyNativeSharedUpdate.modelStep (runtime.advance stage) (modelHistory runtime stage) =
      modelHistory runtime (stage + 1) := by
  rw [SourceCopyNativeSharedUpdate.modelStep, modelHistory, LinearEquiv.apply_symm_apply]
  exact congrArg (jointModelEquiv (runtime.advance (stage + 1))).symm (history_native_step runtime stage).symm

theorem history_native_energy (runtime : LivingRuntimeState process) (stage : Nat) :
    ‖SourceCopyCurrentCoordinates.realize (runtime.advance (stage + 1)) (maximumIndex (runtime.advance (stage + 1))) 0
      (history runtime (stage + 1))‖ ^ 2 =
      ‖SourceCopyCurrentCoordinates.realize (runtime.advance stage) (maximumIndex (runtime.advance stage)) 0 (history runtime stage)‖ ^ 2 +
        ‖(history runtime stage).2.1‖ ^ 2 + 2 * (inner ℂ (history runtime stage).2.2 (history runtime stage).2.1).re := by
  rw [history_action, SourceJointClockGraph.action_energy]
  rfl

def gainAt (runtime : LivingRuntimeState process) (stage : Nat) : SourceJointClockGraph.Carrier :=
  SourceCopySharedNext.gain (runtime.advance stage) (history runtime stage) (nativePacket (runtime.advance stage))

def remainingAt (runtime : LivingRuntimeState process) (stage : Nat) : SourceJointClockGraph.Carrier :=
  SourceCopyCurrentCoordinates.residual (runtime.advance stage) (maximumIndex (runtime.advance stage)) 0 (sourceValue (runtime.advance stage))

theorem gain_step_budget (runtime : LivingRuntimeState process) (stage : Nat) :
    ‖gainAt runtime stage‖ ^ 2 + ‖remainingAt runtime (stage + 1)‖ ^ 2 = ‖remainingAt runtime stage‖ ^ 2 := by
  rw [gainAt, history_source, nativePacket]
  dsimp only [remainingAt]
  rw [show runtime.advance (stage + 1) = (runtime.advance stage).tick.next from rfl]
  with_reducible exact SourceCopySharedNext.native_budget (runtime.advance stage)

theorem history_budget (runtime : LivingRuntimeState process) (stage : Nat) :
    (∑ step ∈ Finset.range stage, ‖gainAt runtime step‖ ^ 2) + ‖remainingAt runtime stage‖ ^ 2 = ‖remainingAt runtime 0‖ ^ 2 := by
  induction stage with
  | zero => simp only [Finset.range_zero, Finset.sum_empty, zero_add]
  | succ stage previous =>
    rw [Finset.sum_range_succ]
    have localBudget := gain_step_budget runtime stage
    linarith only [previous, localBudget]

end
end SourceCopySharedHistory
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
