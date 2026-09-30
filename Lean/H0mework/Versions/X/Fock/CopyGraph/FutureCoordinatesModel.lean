import H0mework.Versions.X.Fock.CopyGraph.FutureCoordinatesResidual
import H0mework.Versions.X.Fock.CopyGraph.CurrentCoordinatesModel

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyFutureCoordinates

open SourceCopyProgram (Index)
open SourceCopyTemporalBoundary (observer)
open SourceGeneratedAcquisitionContinuation SourceGeneratedActionObservationHistory
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def modelEquiv (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :
    Model SourceJointClockGraph.action.toLinearMap (observer runtime index (steps + 1)) ≃ₗ[ℂ] Coordinates runtime index steps :=
  SourceCopyCurrentCoordinates.modelEquiv runtime index (steps + 1)

theorem model_equiv_source (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (target : SourceJointClockGraph.Carrier) :
    modelEquiv runtime index steps (projection SourceJointClockGraph.action.toLinearMap (observer runtime index (steps + 1)) target) =
      sourceRead runtime index steps target :=
  SourceCopyCurrentCoordinates.model_equiv_source runtime index (steps + 1) target

def step (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :
    Coordinates runtime index steps →ₗ[ℂ] Coordinates runtime index steps :=
  SourceCopyCurrentCoordinates.step runtime index (steps + 1)

theorem step_source (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (target : SourceJointClockGraph.Carrier) :
    step runtime index steps (sourceRead runtime index steps target) =
      sourceRead runtime index steps (SourceJointClockGraph.action target) :=
  SourceCopyCurrentCoordinates.step_source runtime index (steps + 1) target

theorem model_step (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (value : Model SourceJointClockGraph.action.toLinearMap (observer runtime index (steps + 1))) :
    modelEquiv runtime index steps (modelAction SourceJointClockGraph.action.toLinearMap (observer runtime index (steps + 1)) value) =
      step runtime index steps (modelEquiv runtime index steps value) :=
  SourceCopyCurrentCoordinates.model_step runtime index (steps + 1) value

def escape (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :
    SourceJointClockGraph.Carrier →ₗ[ℂ] SourceJointClockGraph.Carrier :=
  SourceCopyCurrentCoordinates.escape runtime index (steps + 1)

theorem residual_next (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (target : SourceJointClockGraph.Carrier) :
    residual runtime index steps (SourceJointClockGraph.action target) =
      SourceJointClockGraph.action (residual runtime index steps target) + escape runtime index steps target :=
  SourceCopyCurrentCoordinates.residual_next runtime index (steps + 1) target

theorem native_step (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps ticks : Nat) :
    step runtime index steps (sourceRead runtime index steps
      (SourceJointClockGraph.read (SourceClockComplex.ofNative (SourceOperationNative.point (runtime.advance ticks))))) =
    sourceRead runtime index steps (SourceJointClockGraph.read
      (SourceClockComplex.ofNative (SourceOperationNative.point (runtime.advance (ticks + 1))))) :=
  SourceCopyCurrentCoordinates.native_step runtime index (steps + 1) ticks


end
end SourceCopyFutureCoordinates
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
