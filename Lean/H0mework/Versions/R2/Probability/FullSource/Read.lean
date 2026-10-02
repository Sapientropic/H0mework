import H0mework.Versions.R2.Probability.Source.Field

/-! A full native read keeps exact source identities inside the generated field. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOwnedObservationHistory

open SourceGeneratedActionObservationHistory

noncomputable section

universe u

variable {State : Type u} (step : State → State)

theorem full_observation : observation (sourcePoint (State := State)) = LinearMap.id := by
  apply Finsupp.lhom_ext'
  intro state
  apply LinearMap.ext_ring
  exact observation_point sourcePoint state

theorem full_sourceMap_injective :
    Function.Injective (sourceMap (sourceAction step) (observation (sourcePoint (State := State)))) := by
  intro left right same
  have readback := ((source_fibre_iff (sourceAction step) (observation sourcePoint) _ _).mp same) 0
  change observation sourcePoint left = observation sourcePoint right at readback
  rw [full_observation] at readback
  exact readback

theorem full_fieldPoint_injective :
    Function.Injective (fieldPoint step (sourcePoint (State := State))) := by
  intro left right same
  exact Finsupp.single_left_injective (one_ne_zero : (1 : ℤ) ≠ 0) (full_sourceMap_injective step same)

end
end SourceOwnedObservationHistory
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
