import H0mework.Physics.NonlinearOrbit.Continuation

/-! Zero impulse recovers the original constant gauge and source phase on
the whole generated window, by nonlinear flow uniqueness. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Nonlinear

open SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Dynamics Stage9C.Material.SpinPair

noncomputable section

def background (radius : ℝ) (positive : 0 < radius) : LocalOrbit (seed 0) 0 where
  radius := radius
  positive := positive
  curve := fun time => (gaugeScale, 0, frequency*time)
  starts := by simp [seed]
  evolves := by
    intro time _
    have derivative := (hasDerivAt_const time gaugeScale).prodMk
      ((hasDerivAt_const time (0 : ℝ)).prodMk ((hasDerivAt_id time).const_mul frequency))
    convert derivative using 1
    all_goals first | rfl | simp [generator_eq, equilibrium, frequency]

theorem orbit_zero_recovers (time : ℝ) (inside : time ∈ (orbit 0).window) :
    (orbit 0).curve time = (gaugeScale, 0, frequency*time) := by
  exact (orbit 0).unique_on (background (orbit 0).radius (orbit 0).positive) ⟨inside, inside⟩

theorem orbit_initial_velocity (canonicalImpulse : ℝ) :
    HasDerivAt (orbit canonicalImpulse).amplitude (canonicalImpulse/inertia) 0 := by
  have derivative := (orbit canonicalImpulse).amplitude_derivative 0 (orbit canonicalImpulse).initial_mem
  rwa [orbit_velocity_initial] at derivative

end
end SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Nonlinear
