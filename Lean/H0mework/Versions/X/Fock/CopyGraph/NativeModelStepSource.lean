import H0mework.Versions.X.Fock.CopyGraph.FutureUpdateObservation

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyNativeModelStep

open SourceCopyProgram (Index)
open SourceCopyTemporalBoundary (observer)
open SourceGeneratedAcquisitionContinuation SourceGeneratedActionObservationHistory
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def advanceModel (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (previous : Model SourceJointClockGraph.action.toLinearMap (observer runtime index (steps + 1)))
    (observed : SourceCopyFutureUpdate.Samples runtime index) :
    Model SourceJointClockGraph.action.toLinearMap (observer runtime index (steps + 2)) :=
  modelAction SourceJointClockGraph.action.toLinearMap (observer runtime index (steps + 2))
    (SourceCopyFutureUpdate.updateModel runtime index steps previous observed)

theorem advance_model_source (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (target : SourceJointClockGraph.Carrier) :
    advanceModel runtime index steps
      (projection SourceJointClockGraph.action.toLinearMap (observer runtime index (steps + 1)) target)
      (SourceCopyFutureUpdate.samples runtime index steps target) =
      projection SourceJointClockGraph.action.toLinearMap (observer runtime index (steps + 2)) (SourceJointClockGraph.action target) := by
  rw [advanceModel, SourceCopyFutureUpdate.update_model_source, modelAction_source]
  rfl

theorem native_model_next (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps ticks : Nat) :
    advanceModel runtime index steps
      (projection SourceJointClockGraph.action.toLinearMap (observer runtime index (steps + 1))
        (SourceJointClockGraph.read (SourceClockComplex.ofNative (SourceOperationNative.point (runtime.advance ticks)))))
      (SourceCopyFutureUpdate.samples runtime index steps
        (SourceJointClockGraph.read (SourceClockComplex.ofNative (SourceOperationNative.point (runtime.advance ticks))))) =
    projection SourceJointClockGraph.action.toLinearMap (observer runtime index (steps + 2))
      (SourceJointClockGraph.read (SourceClockComplex.ofNative (SourceOperationNative.point (runtime.advance (ticks + 1))))) := by
  rw [advance_model_source, ← SourceCopyTimeModel.time_native runtime (ticks + 1),
    SourceCopyTimeModel.time_succ, SourceCopyTimeModel.time_native]

end
end SourceCopyNativeModelStep
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
