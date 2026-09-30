import H0mework.Fock.SourceHistoryClock.BinomialPrefixCore

/-! The complete finite prefix supplies its own source-generated next update. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceBinomialClock.Prefix

noncomputable section

theorem recover_moments (samples : Window) :
    massRead (recover samples) = samples 2 - 2 * samples 1 + samples 0 ∧
      clockRead (recover samples) = samples 1 - samples 0 ∧
      secondRead (recover samples) = samples 0 := by
  rw [recover_apply, Frame.rebuild_apply]
  constructor
  · simp only [map_add, map_smul, Fock.mass_point, Frame.mass_effect, Frame.mass_secondEffect,
      smul_eq_mul, mul_one, mul_zero, add_zero]
  constructor
  · simp only [map_add, map_smul, Fock.clock_point, Frame.clock_effect, Frame.clock_secondEffect,
      smul_eq_mul, mul_zero, add_zero]
    norm_num
    ring
  · simp only [map_add, map_smul, Fock.second_point, Frame.second_effect, Fock.clock_point,
      Frame.second_secondEffect, smul_eq_mul]
    norm_num [rawSecond]
    ring

theorem window_recover (samples : Window) : window (recover samples) = samples := by
  rw [window_apply, (recover_moments samples).1, (recover_moments samples).2.1, (recover_moments samples).2.2]
  funext index
  fin_cases index
  · rfl
  · change samples 0 + (samples 1 - samples 0) = samples 1
    ring
  · change samples 0 + 2 * (samples 1 - samples 0) + (samples 2 - 2 * samples 1 + samples 0) = samples 2
    ring

def next : Window →ₗ[ℤ] Window := window.comp (action.comp recover)

theorem next_window (value : Model) : next (window value) = window (action value) := by
  change window (action (recover (window value))) = _
  rw [recover_window]

theorem next_apply (samples : Window) :
    next samples = ![samples 1, samples 2, samples 0 - 3 * samples 1 + 3 * samples 2] := by
  change window (action (recover samples)) = _
  rw [window_apply, secondRead_action, clockRead_action, massRead_action,
    (recover_moments samples).1, (recover_moments samples).2.1, (recover_moments samples).2.2]
  funext index
  fin_cases index
  · change samples 0 + (samples 1 - samples 0) = samples 1
    ring
  · change samples 0 + (samples 1 - samples 0) +
        (samples 1 - samples 0 + (samples 2 - 2 * samples 1 + samples 0)) = samples 2
    ring
  · change samples 0 + (samples 1 - samples 0) +
      2 * (samples 1 - samples 0 + (samples 2 - 2 * samples 1 + samples 0)) +
        (samples 2 - 2 * samples 1 + samples 0) = samples 0 - 3 * samples 1 + 3 * samples 2
    ring

end
end SourceBinomialClock.Prefix
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
