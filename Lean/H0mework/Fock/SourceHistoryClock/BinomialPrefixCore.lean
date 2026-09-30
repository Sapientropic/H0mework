import H0mework.Fock.SourceHistoryClock.BinomialAction

/-! Three actual readouts of the existing model recover its complete source frame over the integers. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceBinomialClock.Prefix

noncomputable section

abbrev Window := Fin 3 → ℤ

def window : Model →ₗ[ℤ] Window :=
  SourceGeneratedActionObservationHistory.prefixEvaluator action secondRead 2

theorem window_apply (value : Model) :
    window value = ![secondRead value, secondRead value + clockRead value,
      secondRead value + 2 * clockRead value + massRead value] := by
  funext index
  fin_cases index
  · rfl
  · exact secondRead_action value
  · change secondRead (action (action value)) = secondRead value + 2 * clockRead value + massRead value
    rw [secondRead_action, secondRead_action, clockRead_action]
    ring

private def momentCoordinates : Window →ₗ[ℤ] ℤ × ℤ × ℤ :=
  let first : Window →ₗ[ℤ] ℤ := LinearMap.proj 0
  let second : Window →ₗ[ℤ] ℤ := LinearMap.proj 1
  let third : Window →ₗ[ℤ] ℤ := LinearMap.proj 2
  (third - (2 : ℤ) • second + first).prod
    (((3 : ℤ) • second - (2 : ℤ) • first - third).prod
      ((3 : ℤ) • first - (3 : ℤ) • second + third))

def recover : Window →ₗ[ℤ] Model := (Frame.rebuild 0).comp momentCoordinates

theorem recover_apply (samples : Window) :
    recover samples = Frame.rebuild 0
      (samples 2 - 2 * samples 1 + samples 0,
        3 * samples 1 - 2 * samples 0 - samples 2,
        3 * samples 0 - 3 * samples 1 + samples 2) := rfl

theorem recover_window (value : Model) : recover (window value) = value := by
  rw [recover_apply]
  have coordinates :
      ((window value) 2 - 2 * (window value) 1 + (window value) 0,
        3 * (window value) 1 - 2 * (window value) 0 - (window value) 2,
        3 * (window value) 0 - 3 * (window value) 1 + (window value) 2) = Frame.coordinates 0 value := by
    rw [window_apply, Frame.coordinates_apply, Fock.clock_point, Fock.second_point]
    change (secondRead value + 2 * clockRead value + massRead value - 2 * (secondRead value + clockRead value) + secondRead value,
      3 * (secondRead value + clockRead value) - 2 * secondRead value - (secondRead value + 2 * clockRead value + massRead value),
      3 * secondRead value - 3 * (secondRead value + clockRead value) + (secondRead value + 2 * clockRead value + massRead value)) =
      (massRead value, clockRead value - massRead value * 1,
        secondRead value - massRead value * 0 - (clockRead value - massRead value * 1) * 1)
    exact Prod.ext (by ring) (Prod.ext (by ring) (by ring))
  rw [coordinates, Frame.rebuild_coordinates]

theorem window_injective : Function.Injective window :=
  Function.LeftInverse.injective recover_window

end
end SourceBinomialClock.Prefix
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
