import H0mework.Realization.ObservationActions.DependentCoimage

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

theorem kernel_le_observer (state : State) :
    LinearMap.ker (sourceMap step action observation state) ≤ (observation state).toLinearMap.ker := by
  intro value invisible
  have first := (data step action observation state).evaluator_eq_zero_of_completionMap_eq_zero
    (compatible step action observation state) value invisible 0
  exact congrFun first (0 : Fin 1)

def coimageRead (state : State) : ResidualCarrier (sourceMap step action observation state) →ₗ[𝕜] B :=
  (LinearMap.ker (sourceMap step action observation state)).liftQ (observation state).toLinearMap
    (kernel_le_observer step action observation state)

theorem coimageRead_source (state : State) (value : C state) :
    coimageRead step action observation state (canonicalResidual (sourceMap step action observation state) value) =
      observation state value := rfl

theorem next_read (state : State) (value : C state) :
    coimageRead step action observation (step state)
        (nextCoimage step action observation state
          (canonicalResidual (sourceMap step action observation state) value)) =
      observation (step state) (action state value) := by
  rw [next_coimage_source, coimageRead_source]

end
end SourceGeneratedActionObservationHistory.Dependent
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
