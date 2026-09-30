import H0mework.Fock.SourceHistoryClock.BinomialFrame
import H0mework.Fock.SourceHistoryClock.FrameAction

/-! The old clock model is a restriction of the same generated source; its full forgotten direction is explicit. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceBinomialClock

noncomputable section

def forgetClock : Model →ₗ[ℤ] SourceClockModel.Model :=
  (SourceClockFrame.rebuild 0).comp (massRead.prod (clockRead - massRead))

theorem forget_mass (value : Model) : SourceClockModel.massRead (forgetClock value) = massRead value := by
  change SourceClockModel.massRead (massRead value • SourceClockModel.Fock.point 0 +
    (clockRead value - massRead value) • SourceClockFrame.effect 0) = _
  simp only [map_add, map_smul, SourceClockModel.Fock.mass_current, SourceClockFrame.mass_effect,
    smul_eq_mul, mul_one, mul_zero, add_zero]

theorem forget_clock (value : Model) : SourceClockModel.clockRead (forgetClock value) = clockRead value := by
  change SourceClockModel.clockRead (massRead value • SourceClockModel.Fock.point 0 +
    (clockRead value - massRead value) • SourceClockFrame.effect 0) = _
  simp only [map_add, map_smul, SourceClockFrame.clock_effect, smul_eq_mul, mul_one]
  have initial : SourceClockModel.clockRead (SourceClockModel.Fock.point 0) = 1 := by
    rw [SourceClockModel.Fock.clock_current, NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime.runtimeAt_scanIndex]
    rfl
  rw [initial, mul_one]
  abel

theorem forget_source (word : Nat →₀ ℤ) : forgetClock (projection word) = SourceClockModel.projection word := by
  apply (SourceClockModel.model_ext_iff _ _).mpr
  exact ⟨(forget_mass _).trans ((massRead_source word).trans (SourceClockModel.massRead_source word).symm),
    (forget_clock _).trans ((clockRead_source word).trans (SourceClockModel.clockRead_source word).symm)⟩

theorem forget_action (value : Model) : forgetClock (action value) = SourceClockModel.action (forgetClock value) := by
  apply (SourceClockModel.model_ext_iff _ _).mpr
  constructor
  · rw [forget_mass, massRead_action, SourceClockModel.massRead_action, forget_mass]
  · rw [forget_clock, clockRead_action, SourceClockModel.clockRead_action, forget_clock, forget_mass]

theorem forget_zero_iff (value : Model) : forgetClock value = 0 ↔ massRead value = 0 ∧ clockRead value = 0 := by
  rw [SourceClockModel.model_ext_iff, forget_mass, forget_clock, map_zero, map_zero]

theorem forgotten_direction (depth : Nat) (value : Model) :
    forgetClock value = 0 ↔ value = secondRead value • Frame.secondEffect depth := by
  constructor
  · intro zero
    obtain ⟨massZero, clockZero⟩ := (forget_zero_iff value).mp zero
    have source := Frame.reconstruction depth value
    simpa only [massZero, clockZero, zero_smul, zero_mul, sub_zero, sub_self, zero_add] using source
  · intro source
    apply (forget_zero_iff value).mpr
    rw [source, map_smul, map_smul, Frame.mass_secondEffect, Frame.clock_secondEffect, smul_zero]
    exact ⟨rfl, rfl⟩

end
end SourceBinomialClock
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
