import H0mework.Probability.FullSource.Read
import H0mework.Realization.HistoryTopology.Carrier

/-! The complete native observer recovers a whole source word from its generated zero coordinate. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOwnedObservationHistory.FullWord

open SourceGeneratedActionObservationHistory SourceGeneratedScalarCofinalTopology
open CategoryTheory

noncomputable section

universe u

variable {State : Type u} (step : State → State)

def word : Field step (sourcePoint (State := State)) →ₗ[ℤ] Carrier State :=
  (LinearMap.proj (0 : Fin 1)).comp (stageRead (sourceAction step) (observation sourcePoint) 0)

theorem word_source (value : Carrier State) :
    word step (sourceMap (sourceAction step) (observation sourcePoint) value) = value := by
  change stageRead (sourceAction step) (observation sourcePoint) 0 (sourceMap _ _ value) 0 = value
  rw [source_reads_stage, full_observation]
  rfl

private theorem quotientMap_injective (stage : Nat) :
    Function.Injective ((data (sourceAction step) (observation (sourcePoint (State := State)))).quotientMap stage) := by
  intro left right same
  have observed := congrArg
    (fun value => (data (sourceAction step) (observation sourcePoint)).stageRealization stage value 0) same
  change observation sourcePoint left = observation sourcePoint right at observed
  rw [full_observation] at observed
  exact observed

private theorem quotientTransition_injective (stage : Nat) :
    Function.Injective ((data (sourceAction step) (observation (sourcePoint (State := State)))).quotientTransition
      (compatible (sourceAction step) (observation sourcePoint)) stage) := by
  intro left right same
  obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective
    ((data (sourceAction step) (observation sourcePoint)).stageKernel (stage + 1)) left
  obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective
    ((data (sourceAction step) (observation sourcePoint)).stageKernel (stage + 1)) right
  have sourceEq := quotientMap_injective step stage same
  exact congrArg ((data (sourceAction step) (observation sourcePoint)).quotientMap (stage + 1)) sourceEq

theorem word_injective : Function.Injective (word step) := by
  intro left right same
  let tower := data (sourceAction step) (observation (sourcePoint (State := State)))
  let laws := compatible (sourceAction step) (observation (sourcePoint (State := State)))
  apply coordinates_injective tower laws
  funext stage
  induction stage with
  | zero =>
      apply tower.stageRealization_injective 0
      funext index
      have indexZero : index = 0 := Fin.eq_zero index
      subst index
      exact same
  | succ stage previous =>
      apply quotientTransition_injective step stage
      exact (coordinates_coherent tower laws left stage).trans
        (previous.trans (coordinates_coherent tower laws right stage).symm)

theorem source_word (value : Field step (sourcePoint (State := State))) :
    sourceMap (sourceAction step) (observation sourcePoint) (word step value) = value :=
  word_injective step (word_source step (word step value))

def equivalence : Carrier State ≃ₗ[ℤ] Field step (sourcePoint (State := State)) :=
  LinearEquiv.ofLinearMap (sourceMap (sourceAction step) (observation sourcePoint)) (word step)
    (LinearMap.ext (source_word step)) (LinearMap.ext (word_source step))

theorem word_action (value : Field step (sourcePoint (State := State))) :
    word step (fieldAction step sourcePoint value) = sourceAction step (word step value) := by
  rw [← source_word step value]
  change word step (endomorphism (sourceAction step) (observation sourcePoint) (sourceMap _ _ _)) = _
  rw [endomorphism_source, word_source, word_source]

end
end SourceOwnedObservationHistory.FullWord
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
