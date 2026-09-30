import H0mework.Versions.X.Fock.CopyGraph.NativeModelStepFlow

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyNativeModelStep

open SourceCopyProgram (Index)
open SourceCopyTemporalBoundary (observer)
open SourceCopyFutureCoordinates (realize modelEquiv retained residual)
open SourceGeneratedAcquisitionContinuation SourceGeneratedActionObservationHistory
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def advanceGain (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (previous : Model SourceJointClockGraph.action.toLinearMap (observer runtime index (steps + 1)))
    (observed : SourceCopyFutureUpdate.Samples runtime index) : SourceJointClockGraph.Carrier :=
  realize runtime index (steps + 1) (modelEquiv runtime index (steps + 1) (advanceModel runtime index steps previous observed)) -
    SourceJointClockGraph.action (realize runtime index steps (modelEquiv runtime index steps previous))

theorem advance_gain_source (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (target : SourceJointClockGraph.Carrier) :
    advanceGain runtime index steps
      (projection SourceJointClockGraph.action.toLinearMap (observer runtime index (steps + 1)) target)
      (SourceCopyFutureUpdate.samples runtime index steps target) = flow runtime index steps target := by
  rw [advanceGain, advance_model_source, SourceCopyFutureCoordinates.model_equiv_source,
    SourceCopyFutureCoordinates.model_equiv_source]
  change retained runtime index (steps + 1) (SourceJointClockGraph.action target) -
    SourceJointClockGraph.action (retained runtime index steps target) = _
  rw [next_reconstruction]
  abel

theorem advance_gain_budget (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (target : SourceJointClockGraph.Carrier) :
    ‖advanceGain runtime index steps
      (projection SourceJointClockGraph.action.toLinearMap (observer runtime index (steps + 1)) target)
      (SourceCopyFutureUpdate.samples runtime index steps target)‖ ^ 2 +
        ‖residual runtime index (steps + 1) (SourceJointClockGraph.action target)‖ ^ 2 = ‖residual runtime index steps target‖ ^ 2 := by
  rw [advance_gain_source]
  exact flow_budget runtime index steps target

end
end SourceCopyNativeModelStep
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
