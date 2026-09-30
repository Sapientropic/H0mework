import H0mework.Realization.Operations.ObservationModel
import Mathlib.Analysis.InnerProductSpace.ProdL2

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionObservationHistory.Hilbert

open SourceGeneratedActionObservationHistory
open scoped InnerProductSpace

noncomputable section

universe r u

variable {𝕜 : Type r} [RCLike 𝕜]
variable {C B : Type u} [NormedAddCommGroup C] [InnerProductSpace 𝕜 C]
  [NormedAddCommGroup B] [NormedSpace 𝕜 B]
variable (action : C →L[𝕜] C) (observation : C →L[𝕜] B)

theorem kernel_closed :
    IsClosed (LinearMap.ker (sourceMap action.toLinearMap observation.toLinearMap) : Set C) := by
  rw [kernel_eq_iInf, Submodule.coe_iInf]
  apply isClosed_iInter
  intro stage
  convert (observation.comp (action ^ stage)).isClosed_ker using 1
  simp only [stageEvaluator, ContinuousLinearMap.toLinearMap_comp, ContinuousLinearMap.toLinearMap_pow]

variable [CompleteSpace C]

local instance closedKernel :
    IsClosed (LinearMap.ker (sourceMap action.toLinearMap observation.toLinearMap) : Set C) :=
  kernel_closed action observation

local instance completeKernel :
    CompleteSpace (LinearMap.ker (sourceMap action.toLinearMap observation.toLinearMap)) :=
  (kernel_closed action observation).isComplete.completeSpace_coe

def realization : Model action.toLinearMap observation.toLinearMap ≃ₗᵢ[𝕜]
    (LinearMap.ker (sourceMap action.toLinearMap observation.toLinearMap))ᗮ :=
  Submodule.quotientEquivOrthogonal _

theorem realization_projection (value : C) :
    realization action observation (projection action.toLinearMap observation.toLinearMap value) =
      (LinearMap.ker (sourceMap action.toLinearMap observation.toLinearMap))ᗮ.orthogonalProjectionOnto
        value := by
  change Submodule.quotientEquivOrthogonal _ (Submodule.Quotient.mk value) = _
  rw [Submodule.coe_quotientEquivOrthogonal, Submodule.quotientEquivOfIsCompl_apply_mk]
  rw [Submodule.orthogonalProjectionOnto_apply_eq_projectionOnto]
  simp only [Submodule.orthogonal_orthogonal]

def recover : Model action.toLinearMap observation.toLinearMap →L[𝕜] C :=
  (LinearMap.ker (sourceMap action.toLinearMap observation.toLinearMap))ᗮ.subtypeL.comp
    (realization action observation).toContinuousLinearEquiv.toContinuousLinearMap

def residual : C →L[𝕜] C :=
  (LinearMap.ker (sourceMap action.toLinearMap observation.toLinearMap)).starProjection

theorem recover_projection (value : C) :
    recover action observation (projection action.toLinearMap observation.toLinearMap value) =
      (LinearMap.ker (sourceMap action.toLinearMap observation.toLinearMap))ᗮ.starProjection value := by
  exact congrArg Subtype.val (realization_projection action observation value)

theorem recover_residual (value : C) :
    residual action observation value +
      recover action observation (projection action.toLinearMap observation.toLinearMap value) = value := by
  rw [recover_projection]
  exact Submodule.starProjection_add_starProjection_orthogonal value

theorem residual_invisible (value : C) (stage : Nat) :
    observation ((action.toLinearMap ^ stage) (residual action observation value)) = 0 :=
  (mem_kernel_iff action.toLinearMap observation.toLinearMap _).mp
    (Submodule.starProjection_apply_mem _ value) stage

theorem source_energy (value : C) :
    ‖value‖ ^ 2 = ‖residual action observation value‖ ^ 2 +
      ‖projection action.toLinearMap observation.toLinearMap value‖ ^ 2 := by
  have isometry := (realization action observation).norm_map
    (projection action.toLinearMap observation.toLinearMap value)
  rw [realization_projection] at isometry
  rw [← isometry]
  exact Submodule.norm_sq_eq_add_norm_sq_projection value _

end
end SourceGeneratedActionObservationHistory.Hilbert
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
