import H0mework.Fock.CopyGraph.CurrentCoordinatesResidual

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyCurrentCoordinates

open SourceCopyProgram (Index)
open SourceCopyTemporalBoundary (observer)
open SourceGeneratedAcquisitionContinuation SourceGeneratedActionObservationHistory
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def modelEquiv (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :
    Model SourceJointClockGraph.action.toLinearMap (observer runtime index steps) ≃ₗ[ℂ] Coordinates runtime index steps :=
  (Submodule.quotEquivOfEq _ _ (kernel_exact runtime index steps)).trans
    ((sourceRead runtime index steps).quotKerEquivOfSurjective (source_surjective runtime index steps))

theorem model_equiv_source (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (target : SourceJointClockGraph.Carrier) :
    modelEquiv runtime index steps (projection SourceJointClockGraph.action.toLinearMap (observer runtime index steps) target) =
      sourceRead runtime index steps target := by
  change modelEquiv runtime index steps (Submodule.Quotient.mk target) = _
  simp only [modelEquiv, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]

def step (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :
    Coordinates runtime index steps →ₗ[ℂ] Coordinates runtime index steps :=
  (sourceRead runtime index steps).comp (SourceJointClockGraph.action.toLinearMap.comp (realize runtime index steps))

theorem step_source (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (target : SourceJointClockGraph.Carrier) :
    step runtime index steps (sourceRead runtime index steps target) =
      sourceRead runtime index steps (SourceJointClockGraph.action target) := by
  have source := source_zero_next runtime index steps (residual runtime index steps target) (residual_source runtime index steps target)
  change sourceRead runtime index steps (SourceJointClockGraph.action
    (target - realize runtime index steps (sourceRead runtime index steps target))) = 0 at source
  rw [map_sub, map_sub] at source
  exact (sub_eq_zero.mp source).symm

theorem model_step (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (value : Model SourceJointClockGraph.action.toLinearMap (observer runtime index steps)) :
    modelEquiv runtime index steps (modelAction SourceJointClockGraph.action.toLinearMap (observer runtime index steps) value) =
      step runtime index steps (modelEquiv runtime index steps value) := by
  rcases Submodule.mkQ_surjective (LinearMap.ker
    (sourceMap SourceJointClockGraph.action.toLinearMap (observer runtime index steps))) value with ⟨target, same⟩
  change projection SourceJointClockGraph.action.toLinearMap (observer runtime index steps) target = value at same
  rw [← same, modelAction_source, model_equiv_source, model_equiv_source, step_source]
  rfl

def escape (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :
    SourceJointClockGraph.Carrier →ₗ[ℂ] SourceJointClockGraph.Carrier :=
  SourceJointClockGraph.action.toLinearMap.comp (retained runtime index steps) -
    (retained runtime index steps).comp SourceJointClockGraph.action.toLinearMap

theorem residual_next (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (target : SourceJointClockGraph.Carrier) :
    residual runtime index steps (SourceJointClockGraph.action target) =
      SourceJointClockGraph.action (residual runtime index steps target) + escape runtime index steps target := by
  simp only [residual, escape, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
    ContinuousLinearMap.coe_coe, map_sub]
  abel

theorem native_step (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps ticks : Nat) :
    step runtime index steps (sourceRead runtime index steps
      (SourceJointClockGraph.read (SourceClockComplex.ofNative (SourceOperationNative.point (runtime.advance ticks))))) =
    sourceRead runtime index steps (SourceJointClockGraph.read
      (SourceClockComplex.ofNative (SourceOperationNative.point (runtime.advance (ticks + 1))))) := by
  rw [step_source, ← SourceCopyTimeModel.time_native runtime ticks, ← SourceCopyTimeModel.time_native runtime (ticks + 1),
    SourceCopyTimeModel.time_succ]

end
end SourceCopyCurrentCoordinates
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
