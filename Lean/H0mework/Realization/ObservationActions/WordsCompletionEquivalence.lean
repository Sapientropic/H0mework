import H0mework.Realization.ObservationActions.WordsCompletionLift

/-! The existing residual coimage identifies the full word completion with its already generated autonomous Model. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionWords

open SourceGeneratedActionObservationHistory SourceGeneratedScalarDifferentialResidual

noncomputable section
universe r u
variable {R : Type r} [CommRing R]
variable {I C B : Type u} [AddCommGroup C] [Module R C] [AddCommGroup B] [Module R B]
variable (actions : I → C →ₗ[R] C) (read : C →ₗ[R] B) (primary : I)

def modelToCompletion : Model actions read primary →ₗ[R] completion (actions primary) (inventory actions read) :=
  (LinearMap.range (sourceMap (actions primary) (inventory actions read))).subtype.comp
    (residualToRange (sourceMap (actions primary) (inventory actions read)))

theorem model_to_completion_source (source : C) :
    modelToCompletion actions read primary (projection actions read primary source) =
      sourceMap (actions primary) (inventory actions read) source := rfl

theorem model_to_completion_injective : Function.Injective (modelToCompletion actions read primary) := by
  intro left right same
  apply residualToRange_injective (sourceMap (actions primary) (inventory actions read))
  exact Subtype.ext same

theorem model_to_completion_surjective : Function.Surjective (modelToCompletion actions read primary) := by
  intro value
  obtain ⟨source, same⟩ := full_source_surjective actions read primary value
  exact ⟨projection actions read primary source, (model_to_completion_source actions read primary source).trans same⟩

def completionEquiv : Model actions read primary ≃ₗ[R] completion (actions primary) (inventory actions read) :=
  LinearEquiv.ofBijective (modelToCompletion actions read primary)
    ⟨model_to_completion_injective actions read primary, model_to_completion_surjective actions read primary⟩

theorem completion_equiv_source (source : C) :
    completionEquiv actions read primary (projection actions read primary source) =
      sourceMap (actions primary) (inventory actions read) source :=
  model_to_completion_source actions read primary source

theorem completion_inverse_source (source : C) :
    (completionEquiv actions read primary).symm (sourceMap (actions primary) (inventory actions read) source) =
      projection actions read primary source := by
  rw [← completion_equiv_source, LinearEquiv.symm_apply_apply]

end
end SourceGeneratedActionWords
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
