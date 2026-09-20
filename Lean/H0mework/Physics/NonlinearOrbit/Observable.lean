import H0mework.Physics.NonlinearOrbit.Field

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Nonlinear

open SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Dynamics Stage9C.Material.SpinPair
open Set Filter
open scoped Topology

noncomputable section

variable {initial : PhaseSpace} {initialTime : ℝ}

theorem LocalOrbit.helicity_derivative (flow : LocalOrbit initial initialTime) (time : ℝ)
    (inside : time ∈ flow.window) :
    HasDerivAt flow.helicity (15*(flow.amplitude time)^4*flow.velocity time) time := by
  rw [show flow.helicity = fun t => 3*(flow.amplitude t)^5 from funext flow.helicity_eq]
  convert ((flow.amplitude_derivative time inside).pow 5).const_mul 3 using 1
  all_goals first | rfl | ring

theorem orbit_amplitude_initial (canonicalImpulse : ℝ) : (orbit canonicalImpulse).amplitude 0 = gaugeScale :=
  congrArg Prod.fst (orbit_source canonicalImpulse)

theorem orbit_velocity_initial (canonicalImpulse : ℝ) :
    (orbit canonicalImpulse).velocity 0 = canonicalImpulse/inertia := by
  change (orbit canonicalImpulse).curve 0 |>.2.1 / inertia = _
  rw [orbit_source]

theorem orbit_helicity_derivative (canonicalImpulse : ℝ) :
    HasDerivAt (orbit canonicalImpulse).helicity (15*gaugeScale^4*canonicalImpulse/inertia) 0 := by
  have derivative := (orbit canonicalImpulse).helicity_derivative 0 (orbit canonicalImpulse).initial_mem
  rw [orbit_amplitude_initial, orbit_velocity_initial] at derivative
  convert derivative using 1
  ring

theorem orbit_helicity_velocity_nonzero (canonicalImpulse : ℝ) (nonzero : canonicalImpulse ≠ 0) :
    deriv (orbit canonicalImpulse).helicity 0 ≠ 0 := by
  rw [(orbit_helicity_derivative canonicalImpulse).deriv]
  exact div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ (ne_of_gt gaugeScale_pos))) nonzero)
    (ne_of_gt inertia_pos)

theorem orbit_helicity_changes (canonicalImpulse : ℝ) (nonzero : canonicalImpulse ≠ 0) :
    ∃ time ∈ (orbit canonicalImpulse).window,
      (orbit canonicalImpulse).helicity time ≠ (orbit canonicalImpulse).helicity 0 := by
  by_contra unchanged
  push Not at unchanged
  have localConstant : (orbit canonicalImpulse).helicity =ᶠ[𝓝 0]
      fun _ => (orbit canonicalImpulse).helicity 0 := by
    filter_upwards [isOpen_Ioo.mem_nhds (orbit canonicalImpulse).initial_mem] with time inside
    exact unchanged time inside
  have derivative := (hasDerivAt_const 0 ((orbit canonicalImpulse).helicity 0)).congr_of_eventuallyEq localConstant
  exact orbit_helicity_velocity_nonzero canonicalImpulse nonzero derivative.deriv

theorem orbit_field_changes (canonicalImpulse : ℝ) (nonzero : canonicalImpulse ≠ 0) :
    ∃ point : ProofFreeRicherAnholonomicSource.BasePoint, point 0 ∈ (orbit canonicalImpulse).window ∧
      (orbit canonicalImpulse).fieldValue point ≠ (orbit canonicalImpulse).fieldValue 0 := by
  obtain ⟨time, inside, differs⟩ := orbit_helicity_changes canonicalImpulse nonzero
  have timeInside : Stage9DEF.Dynamics.timeDisplacement time 0 ∈ (orbit canonicalImpulse).window := by
    simpa only [Stage9DEF.Dynamics.timeDisplacement_zero] using inside
  refine ⟨Stage9DEF.Dynamics.timeDisplacement time, timeInside, ?_⟩
  rw [(orbit canonicalImpulse).fieldValue_helicity _ timeInside,
    (orbit canonicalImpulse).fieldValue_helicity 0 (orbit canonicalImpulse).initial_mem]
  simpa using differs

end
end SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Nonlinear
