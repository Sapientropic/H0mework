import H0mework.Physics.NonlinearOrbit.Generator

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Nonlinear

open SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Dynamics Stage9C.Material.SpinPair
open Set Filter
open scoped Topology

noncomputable section

variable {initial : PhaseSpace} {initialTime : ℝ}

def LocalOrbit.window (flow : LocalOrbit initial initialTime) : Set ℝ :=
  Ioo (initialTime-flow.radius) (initialTime+flow.radius)

theorem LocalOrbit.initial_mem (flow : LocalOrbit initial initialTime) : initialTime ∈ flow.window := by
  constructor <;> linarith [flow.positive]

def LocalOrbit.amplitude (flow : LocalOrbit initial initialTime) (time : ℝ) : ℝ := (flow.curve time).1
def LocalOrbit.momentum (flow : LocalOrbit initial initialTime) (time : ℝ) : ℝ := (flow.curve time).2.1
def LocalOrbit.angle (flow : LocalOrbit initial initialTime) (time : ℝ) : ℝ := (flow.curve time).2.2
def LocalOrbit.velocity (flow : LocalOrbit initial initialTime) (time : ℝ) : ℝ := flow.momentum time/inertia
def LocalOrbit.acceleration (flow : LocalOrbit initial initialTime) (time : ℝ) : ℝ := -restoring (flow.amplitude time)/inertia

theorem LocalOrbit.amplitude_derivative (flow : LocalOrbit initial initialTime) (time : ℝ) (inside : time ∈ flow.window) :
    HasDerivAt flow.amplitude (flow.velocity time) time := by
  have projected := (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).hasFDerivAt.comp_hasDerivAt time (flow.evolves time inside)
  convert projected using 1 <;> first | rfl | simp [LocalOrbit.velocity, LocalOrbit.momentum, generator_eq]

theorem LocalOrbit.momentum_derivative (flow : LocalOrbit initial initialTime) (time : ℝ) (inside : time ∈ flow.window) :
    HasDerivAt flow.momentum (-restoring (flow.amplitude time)) time := by
  have projected := ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp
    (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))).hasFDerivAt.comp_hasDerivAt time (flow.evolves time inside)
  convert projected using 1 <;> first | rfl | simp [LocalOrbit.amplitude, generator_eq]

theorem LocalOrbit.angle_derivative (flow : LocalOrbit initial initialTime) (time : ℝ) (inside : time ∈ flow.window) :
    HasDerivAt flow.angle (3*lapse/2*(spinScale-flow.amplitude time)) time := by
  have projected := ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp
    (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))).hasFDerivAt.comp_hasDerivAt time (flow.evolves time inside)
  convert projected using 1 <;> rfl

theorem LocalOrbit.velocity_derivative (flow : LocalOrbit initial initialTime) (time : ℝ) (inside : time ∈ flow.window) :
    HasDerivAt flow.velocity (flow.acceleration time) time :=
  (flow.momentum_derivative time inside).div_const inertia

theorem LocalOrbit.gauge_force_zero (flow : LocalOrbit initial initialTime) (time : ℝ) :
    force (flow.amplitude time) (flow.acceleration time) = 0 := by
  have generated := euler_action (flow.amplitude time) (flow.acceleration time)
  have cancellation : inertia*flow.acceleration time + restoring (flow.amplitude time) = 0 := by
    unfold LocalOrbit.acceleration
    field_simp [ne_of_gt inertia_pos]
    ring
  rw [cancellation] at generated
  linarith

theorem LocalOrbit.energy_derivative (flow : LocalOrbit initial initialTime) (time : ℝ) (inside : time ∈ flow.window) :
    HasDerivAt (fun t => hamiltonian (flow.curve t)) 0 time := by
  have kinetic := ((flow.momentum_derivative time inside).pow 2).div_const (2*inertia)
  have potential := (potential_hasDerivAt (flow.amplitude time)).comp time (flow.amplitude_derivative time inside)
  rw [← restoring_eq] at potential
  have values : (fun t => hamiltonian (flow.curve t)) =
      fun t => (flow.momentum t)^2/(2*inertia) + Dynamics.potential (flow.amplitude t) := by
    funext t
    exact energy_eq _ _
  rw [values]
  convert kinetic.add potential using 1
  all_goals first | rfl | simp only [LocalOrbit.velocity]; ring

theorem LocalOrbit.energy_conserved (flow : LocalOrbit initial initialTime) (time : ℝ) (inside : time ∈ flow.window) :
    hamiltonian (flow.curve time) = hamiltonian initial := by
  have constant := isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
    (fun t ht => (flow.energy_derivative t ht).differentiableAt.differentiableWithinAt)
    (fun t ht => (flow.energy_derivative t ht).deriv) inside flow.initial_mem
  simpa only [flow.starts] using constant

theorem LocalOrbit.unique_germ (first second : LocalOrbit initial initialTime) :
    first.curve =ᶠ[𝓝 initialTime] second.curve := by
  obtain ⟨K, region, neighborhood, lipschitz⟩ :=
    (generator_contDiff.contDiffAt (x := initial)).exists_lipschitzOnWith
  have first_in : ∀ᶠ t in 𝓝 initialTime, first.curve t ∈ region :=
    (first.evolves initialTime first.initial_mem).continuousAt.preimage_mem_nhds (by simpa only [first.starts] using neighborhood)
  have second_in : ∀ᶠ t in 𝓝 initialTime, second.curve t ∈ region :=
    (second.evolves initialTime second.initial_mem).continuousAt.preimage_mem_nhds (by simpa only [second.starts] using neighborhood)
  apply ODE_solution_unique_of_eventually (v := fun _ => generator) (s := fun _ => region) (K := K)
  · exact Eventually.of_forall (fun _ => lipschitz)
  · filter_upwards [isOpen_Ioo.mem_nhds first.initial_mem, first_in] with t ht hr
    exact ⟨first.evolves t ht, hr⟩
  · filter_upwards [isOpen_Ioo.mem_nhds second.initial_mem, second_in] with t ht hr
    exact ⟨second.evolves t ht, hr⟩
  · exact first.starts.trans second.starts.symm

end
end SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Nonlinear
