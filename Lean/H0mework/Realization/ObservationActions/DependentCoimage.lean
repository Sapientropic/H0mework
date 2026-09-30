import H0mework.Realization.ObservationActions.DependentFibre

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionObservationHistory.Dependent

open SourceGeneratedScalarDifferentialResidual

noncomputable section

universe r u v

variable {𝕜 : Type r} [NontriviallyNormedField 𝕜]
variable {State : Type v} (step : State → State) {C : State → Type u} {B : Type u}
variable [∀ state, NormedAddCommGroup (C state)] [∀ state, NormedSpace 𝕜 (C state)]
variable [NormedAddCommGroup B] [NormedSpace 𝕜 B]
variable (action : ∀ state, C state →L[𝕜] C (step state))
variable (observation : ∀ state, C state →L[𝕜] B)

def generatedMorphism (state : State) :
    Morphism (sourceMap step action observation state) (sourceMap step action observation (step state)) where
  sourceMap := (action state).toLinearMap
  targetMap := nextCompletion step action observation state
  commutes := LinearMap.ext (next_source step action observation state)

def nextCoimage (state : State) :
    ResidualCarrier (sourceMap step action observation state) →ₗ[𝕜]
      ResidualCarrier (sourceMap step action observation (step state)) :=
  inducedResidualMap (generatedMorphism step action observation state)

theorem next_coimage_source (state : State) (value : C state) :
    nextCoimage step action observation state
        (canonicalResidual (sourceMap step action observation state) value) =
      canonicalResidual (sourceMap step action observation (step state)) (action state value) :=
  LinearMap.congr_fun (inducedResidualMap_comp_canonical (generatedMorphism step action observation state)) value

theorem coimage_fibre_iff (state : State) (left right : C state) :
    canonicalResidual (sourceMap step action observation state) left =
        canonicalResidual (sourceMap step action observation state) right ↔
      ∀ stage, stageEvaluator step action observation state stage left =
        stageEvaluator step action observation state stage right := by
  have exactFibre := (canonicalResidual_eq_zero_iff (sourceMap step action observation state) (left - right)).trans
    (source_zero_iff step action observation state (left - right))
  simpa only [map_sub, sub_eq_zero] using exactFibre

end
end SourceGeneratedActionObservationHistory.Dependent
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
