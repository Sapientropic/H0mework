import H0mework.Realization.ObservationActions.HilbertAction
import Mathlib.Analysis.InnerProductSpace.Semisimple

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionObservationHistory.Hilbert

open SourceGeneratedActionObservationHistory
open scoped InnerProductSpace

noncomputable section

universe r u

variable {𝕜 : Type r} [RCLike 𝕜]
variable {C B : Type u} [NormedAddCommGroup C] [InnerProductSpace 𝕜 C] [CompleteSpace C]
  [NormedAddCommGroup B] [NormedSpace 𝕜 B]
variable (action : C →L[𝕜] C) (observation : C →L[𝕜] B)

local instance symmetricCompleteKernel :
    CompleteSpace (LinearMap.ker (sourceMap action.toLinearMap observation.toLinearMap)) :=
  (kernel_closed action observation).isComplete.completeSpace_coe

theorem recover_symmetric_action (symmetric : action.toLinearMap.IsSymmetric)
    (model : Model action.toLinearMap observation.toLinearMap) :
    recover action observation (modelAction action.toLinearMap observation.toLinearMap model) =
      action (recover action observation model) := by
  have invariant := symmetric.orthogonalComplement_mem_invtSubmodule
    (kernel_invariant action.toLinearMap observation.toLinearMap)
  have remains : action (recover action observation model) ∈
      (LinearMap.ker (sourceMap action.toLinearMap observation.toLinearMap))ᗮ :=
    invariant (realization action observation model).property
  rw [recover_action, recover_projection]
  exact Submodule.starProjection_eq_self_iff.mpr remains

theorem residual_symmetric_action (symmetric : action.toLinearMap.IsSymmetric) (value : C) :
    residual action observation (action value) = action (residual action observation value) := by
  have reconstructed := recover_residual action observation (action value)
  have source := congrArg action (recover_residual action observation value)
  rw [map_add] at source
  have next : recover action observation
      (projection action.toLinearMap observation.toLinearMap (action value)) =
        action (recover action observation
          (projection action.toLinearMap observation.toLinearMap value)) := by
    exact (congrArg (recover action observation)
      (modelAction_source action.toLinearMap observation.toLinearMap value).symm).trans
        (recover_symmetric_action action observation symmetric _)
  rw [next] at reconstructed
  exact add_right_cancel (reconstructed.trans source.symm)

end
end SourceGeneratedActionObservationHistory.Hilbert
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
