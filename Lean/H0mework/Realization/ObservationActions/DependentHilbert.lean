import H0mework.Realization.ObservationActions.DependentFibre
import H0mework.Realization.HilbertTransfer.Composition
import Mathlib.Analysis.InnerProductSpace.ProdL2

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionObservationHistory.Dependent

open SourceGeneratedScalarDifferentialResidual
open scoped InnerProductSpace

noncomputable section

universe u v

variable {State : Type v} (step : State → State) {C : State → Type u} {B : Type u}
variable [∀ state, NormedAddCommGroup (C state)] [∀ state, InnerProductSpace ℂ (C state)]
variable [∀ state, CompleteSpace (C state)] [NormedAddCommGroup B] [NormedSpace ℂ B]
variable (action : ∀ state, C state →L[ℂ] C (step state))
variable (observation : ∀ state, C state →L[ℂ] B)

local instance geometryClosed (state : State) :
    IsClosed (LinearMap.ker (sourceMap step action observation state) : Set (C state)) :=
  kernel_closed step action observation state

local instance geometryComplete (state : State) :
    CompleteSpace (LinearMap.ker (sourceMap step action observation state)) :=
  (kernel_closed step action observation state).isComplete.completeSpace_coe

def realization (state : State) :
    ResidualCarrier (sourceMap step action observation state) ≃ₗᵢ[ℂ]
      (LinearMap.ker (sourceMap step action observation state))ᗮ :=
  Submodule.quotientEquivOrthogonal _

def embedding (state : State) : ResidualCarrier (sourceMap step action observation state) →ₗᵢ[ℂ] C state where
  toLinearMap := (LinearMap.ker (sourceMap step action observation state))ᗮ.subtype.comp
    (realization step action observation state).toLinearEquiv.toLinearMap
  norm_map' value := (realization step action observation state).norm_map value

theorem embedding_source (state : State) (value : C state) :
    embedding step action observation state
        (canonicalResidual (sourceMap step action observation state) value) =
      (LinearMap.ker (sourceMap step action observation state))ᗮ.starProjection value := by
  have same : realization step action observation state
      (canonicalResidual (sourceMap step action observation state) value) =
        (LinearMap.ker (sourceMap step action observation state))ᗮ.orthogonalProjectionOnto value := by
    change Submodule.quotientEquivOrthogonal _ (Submodule.Quotient.mk value) = _
    rw [Submodule.coe_quotientEquivOrthogonal, Submodule.quotientEquivOfIsCompl_apply_mk,
      Submodule.orthogonalProjectionOnto_apply_eq_projectionOnto]
    simp only [Submodule.orthogonal_orthogonal]
  exact congrArg Subtype.val same

theorem transfer_embedding (state : State) (value : C state) :
    IsometricRetainedTransfer.transfer (embedding step action observation state) value =
      canonicalResidual (sourceMap step action observation state) value := by
  apply ext_inner_left ℂ
  intro model
  calc
    _ = ⟪embedding step action observation state model, value⟫_ℂ :=
      (embedding step action observation state).toContinuousLinearMap.adjoint_inner_right model value
    _ = ⟪embedding step action observation state model,
        embedding step action observation state
          (canonicalResidual (sourceMap step action observation state) value)⟫_ℂ := by
      rw [embedding_source]
      exact (Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left
        (realization step action observation state model) value).symm
    _ = _ := (embedding step action observation state).inner_map_map _ _

end
end SourceGeneratedActionObservationHistory.Dependent
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
