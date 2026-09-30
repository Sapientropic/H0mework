import H0mework.Probability.Source.Field
import H0mework.Realization.Operations.ObservationModel

/-! Actual native updates and their additive source charges generate one closed observation action. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceAccountedAction

open SourceOwnedObservationHistory

noncomputable section
universe u
variable {State Account : Type u} [AddCommGroup Account]

def update (step : State → State) (charge : State → Account) :
    Carrier State × Account →ₗ[ℤ] Carrier State × Account :=
  ((sourceAction step).comp (LinearMap.fst ℤ (Carrier State) Account)).prod
    (LinearMap.snd ℤ (Carrier State) Account +
      (observation charge).comp (LinearMap.fst ℤ (Carrier State) Account))

theorem update_source (step : State → State) (charge : State → Account) (state : State) (account : Account) :
    update step charge (sourcePoint state, account) = (sourcePoint (step state), account + charge state) := by
  simp [update]

theorem current_kernel_is_complete
    {C : Type u} [AddCommGroup C] [Module ℤ C]
    (sourceUpdate : C →ₗ[ℤ] C) (read : C →ₗ[ℤ] Carrier State × Account)
    (step : State → State) (charge : State → Account)
    (sourceSquare : read.comp sourceUpdate = (update step charge).comp read) :
    LinearMap.ker (SourceGeneratedActionObservationHistory.sourceMap sourceUpdate read) = LinearMap.ker read := by
  apply le_antisymm (SourceGeneratedActionObservationHistory.kernel_le_observer_kernel _ _)
  apply SourceGeneratedActionObservationHistory.invariant_submodule_le_kernel _ _ (LinearMap.ker read) le_rfl
  intro value invisible
  change read (sourceUpdate value) = 0
  have actual := LinearMap.congr_fun sourceSquare value
  change read (sourceUpdate value) = update step charge (read value) at actual
  rw [show read value = 0 from invisible, map_zero] at actual
  exact actual

end
end SourceAccountedAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
