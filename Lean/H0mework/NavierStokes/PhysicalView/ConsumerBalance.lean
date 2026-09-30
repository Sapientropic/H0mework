import H0mework.NavierStokes.PhysicalView.ConsumerNext
import H0mework.NavierStokes.PhysicalView.ConsumerEnergy

set_option autoImplicit false
open scoped Topology ENNReal NNReal

namespace SaturationMonoid.NavierStokes.NativeViewConsumerBalance

open MeasureTheory
open NativeViewRuntime NativeViewConsumerNext NativeViewObservation NativeViewObservedEnergy

noncomputable section

/-- The next energy is computed from the complete state actually written by this runtime tick. -/
theorem resolved_next (runtime : Runtime) (time : ℝ) :
    resolved (payload runtime.tick.next) resolution time =
      resolved (payload runtime) resolution (advance runtime + time) := by
  unfold resolved
  erw [measured_next]

theorem total_next (runtime : Runtime) (time : ℝ) :
    total (payload runtime.tick.next) resolution time =
      total (payload runtime) resolution (advance runtime + time) := by
  unfold total
  erw [measured_next]

theorem unresolved_next (runtime : Runtime) (time : ℝ) :
    unresolved (payload runtime.tick.next) resolution time =
      unresolved (payload runtime) resolution (advance runtime + time) := by
  unfold unresolved
  erw [measured_next]

theorem energy_write_next (runtime : Runtime) :
    resolved (payload runtime.tick.next) resolution 0 - resolved (payload runtime) resolution 0 =
      ∫ time in (0 : ℝ)..advance runtime,
        work (payload runtime) resolution time -
          RationalVorticityEvaluator.butterflyGainViscosity.coeff * dissipation (payload runtime) resolution time := by
  rw [resolved_next, add_zero]
  exact energy_integral _ _ 0 _ le_rfl (advance_nonnegative runtime)

end
end SaturationMonoid.NavierStokes.NativeViewConsumerBalance
