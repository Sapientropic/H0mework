import H0mework.Versions.X.Fock.CopyGraph.CurrentCoordinatesFamily

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyCurrentCoordinates

open SourceCopyProgram (Index)
open SourceCopyRecordedRecurrence (cutoff)
open SourceGeneratedAcquisitionContinuation SourceGeneratedActionObservationHistory
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def jointModelEquiv (runtime : LivingRuntimeState process) :
    Model SourceJointClockGraph.action.toLinearMap (jointObserver runtime) ≃ₗ[ℂ] Coordinates runtime (maximumIndex runtime) 0 :=
  (Submodule.quotEquivOfEq _ _ (joint_kernel runtime)).trans
    ((sourceRead runtime (maximumIndex runtime) 0).quotKerEquivOfSurjective (source_surjective runtime (maximumIndex runtime) 0))

theorem joint_model_source (runtime : LivingRuntimeState process) (target : SourceJointClockGraph.Carrier) :
    jointModelEquiv runtime (projection SourceJointClockGraph.action.toLinearMap (jointObserver runtime) target) =
      sourceRead runtime (maximumIndex runtime) 0 target := by
  change jointModelEquiv runtime (Submodule.Quotient.mk target) = _
  simp only [jointModelEquiv, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]

theorem joint_model_step (runtime : LivingRuntimeState process)
    (value : Model SourceJointClockGraph.action.toLinearMap (jointObserver runtime)) :
    jointModelEquiv runtime (modelAction SourceJointClockGraph.action.toLinearMap (jointObserver runtime) value) =
      step runtime (maximumIndex runtime) 0 (jointModelEquiv runtime value) := by
  rcases Submodule.mkQ_surjective (LinearMap.ker (sourceMap SourceJointClockGraph.action.toLinearMap (jointObserver runtime))) value with ⟨target, same⟩
  change projection SourceJointClockGraph.action.toLinearMap (jointObserver runtime) target = value at same
  rw [← same, modelAction_source, joint_model_source, joint_model_source, step_source]
  rfl

theorem maximum_cutoff (runtime : LivingRuntimeState process) :
    cutoff runtime (maximumIndex runtime) 0 + 1 = (inventoryBound runtime + 1) ^ 2 := by
  simpa only [cutoff, Nat.add_zero, SourceCopyProgram.scale_source, maximum_index_val, pow_two] using
    SourceCopyProgram.index_exact (inventoryBound runtime) (maximumIndex runtime) (inventoryBound runtime)

theorem joint_dimension (runtime : LivingRuntimeState process) :
    Module.finrank ℂ (Model SourceJointClockGraph.action.toLinearMap (jointObserver runtime)) = (inventoryBound runtime + 1) ^ 2 + 2 := by
  rw [(jointModelEquiv runtime).finrank_eq]
  simp only [Coordinates, Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_self, maximum_cutoff]

theorem linear_code_lower (runtime : LivingRuntimeState process) (size : Nat)
    (encode : SourceJointClockGraph.Carrier →ₗ[ℂ] (Fin size → ℂ))
    (decode : (Fin size → ℂ) →ₗ[ℂ] Model SourceJointClockGraph.action.toLinearMap (jointObserver runtime))
    (recovers : decode.comp encode = projection SourceJointClockGraph.action.toLinearMap (jointObserver runtime)) :
    (inventoryBound runtime + 1) ^ 2 + 2 ≤ size := by
  have onto : Function.Surjective decode := by
    intro value
    rcases Submodule.mkQ_surjective (LinearMap.ker (sourceMap SourceJointClockGraph.action.toLinearMap (jointObserver runtime))) value with ⟨target, same⟩
    refine ⟨encode target, ?_⟩
    exact (LinearMap.congr_fun recovers target).trans same
  have lower := LinearMap.finrank_le_finrank_of_surjective onto
  simpa only [joint_dimension, Module.finrank_fin_fun] using lower

end
end SourceCopyCurrentCoordinates
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
