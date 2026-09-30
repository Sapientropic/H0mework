import H0mework.Fock.SourceHistoryClock.FrameAction
import H0mework.Fock.SourceHistory.ClockModelRegression

/-! The generated inverse is total in the model; its first predecessor is the actual hidden source word, not a native runtime point. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceClockFrame.Controls

open SourceClockModel
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime

noncomputable section

theorem inverse_initial_clock_zero : clockRead (inverse 0 (Fock.point 0)) = 0 := by
  rw [inverse_apply, map_sub, map_smul, clock_effect, Fock.mass_current, Fock.clock_current,
    runtimeAt_scanIndex]
  norm_num

theorem inverse_is_hidden_word :
    inverse 0 (Fock.point 0) = projection (SourceClockModel.Controls.hiddenWord 0) := by
  apply (model_ext_iff _ _).mpr
  constructor
  · rw [inverse_apply, map_sub, map_smul, mass_effect, smul_zero, sub_zero, Fock.mass_current,
      massRead_source, SourceClockModel.Controls.hidden_mass]
  · rw [inverse_initial_clock_zero, clockRead_source, SourceClockModel.Controls.hidden_clock]

theorem inverse_is_not_native (depth : Nat) : inverse 0 (Fock.point 0) ≠ Fock.point depth := by
  intro identifies
  have clockEquality := congrArg clockRead identifies
  rw [inverse_initial_clock_zero, Fock.clock_current, runtimeAt_scanIndex] at clockEquality
  have positive : (0 : ℤ) < ((depth + 1 : Nat) : ℤ) := by positivity
  exact (ne_of_gt positive) clockEquality.symm

end
end SourceClockFrame.Controls
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
