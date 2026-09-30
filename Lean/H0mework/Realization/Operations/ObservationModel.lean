import H0mework.Realization.Operations.ObservationKernel
import H0mework.Foundation.Relations.ScalarDifferentialResidual
import H0mework.Realization.Determinant.RestrictionAction

/-! The generated observation model supplies the existing surjective-restriction action consumer. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionObservationHistory

open SourceGeneratedScalarDifferentialResidual SurjectiveRestrictionActionDeterminant

noncomputable section

universe r u

variable {R : Type r} [CommRing R]
variable {C B : Type u} [AddCommGroup C] [Module R C] [AddCommGroup B] [Module R B]
variable (action : C →ₗ[R] C) (observation : C →ₗ[R] B)

def generatedMorphism : Morphism (sourceMap action observation) (sourceMap action observation) where
  sourceMap := action
  targetMap := endomorphism action observation
  commutes := by
    ext value
    exact endomorphism_source action observation value

abbrev Model := ResidualCarrier (sourceMap action observation)

def projection : C →ₗ[R] Model action observation :=
  canonicalResidual (sourceMap action observation)

def modelAction : Model action observation →ₗ[R] Model action observation :=
  inducedResidualMap (generatedMorphism action observation)

def modelReadout : Model action observation →ₗ[R] B :=
  (LinearMap.ker (sourceMap action observation)).liftQ observation
    (kernel_le_observer_kernel action observation)

theorem modelReadout_projection (value : C) :
    modelReadout action observation (projection action observation value) = observation value := rfl

theorem modelAction_source (value : C) :
    modelAction action observation (projection action observation value) =
      projection action observation (action value) :=
  LinearMap.congr_fun (inducedResidualMap_comp_canonical (generatedMorphism action observation)) value

def actionRow : SurjectiveRestrictionActionAt R C (Model action observation) where
  sourceAction := action
  targetAction := modelAction action observation
  restriction := projection action observation
  restriction_surjective := Submodule.mkQ_surjective (LinearMap.ker (sourceMap action observation))
  action_square := (inducedResidualMap_comp_canonical (generatedMorphism action observation)).symm

theorem model_fibre_iff (left right : C) :
    projection action observation left = projection action observation right ↔
      ∀ stage : Nat, observation ((action ^ stage) left) = observation ((action ^ stage) right) := by
  rw [← source_fibre_iff]
  constructor
  · intro same
    exact congrArg (fun value => (residualToRange (sourceMap action observation) value).val) same
  · intro same
    apply residualToRange_injective (sourceMap action observation)
    apply Subtype.ext
    exact same

theorem generated_quotient_action_matches :
    (actionRow action observation).quotientEquiv.conj (actionRow action observation).quotientAction =
      modelAction action observation :=
  (actionRow action observation).quotientAction_conj_eq_target

end
end SourceGeneratedActionObservationHistory
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
