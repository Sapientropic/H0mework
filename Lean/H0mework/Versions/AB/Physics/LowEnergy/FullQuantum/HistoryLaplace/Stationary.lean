import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.HistoryLaplace.Equation

/-! Only an actual constant source history permits the force to leave the retarded integral. -/
set_option autoImplicit false
open MeasureTheory Set
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryLaplace
open FullSpace GaugeGreen ScalarGreen GaugeHistory MatterSpace.Response
noncomputable section

def stationaryValue (gauge : GaugeProfile) (coupling : ℝ) (scalar : ScalarProfile)
    (energy damping : ℝ) (initial : FullMatterL2) : FullMatterL2 :=
  value (fun _ => gauge) continuous_const coupling (fun _ => scalar) continuous_const energy damping initial

theorem constant_forceValue (gauge : GaugeProfile) (coupling : ℝ) (scalar : ScalarProfile)
    (energy damping : ℝ) (positive : 0<damping) (initial : FullMatterL2) :
    forceValue (fun _ => gauge) continuous_const coupling (fun _ => scalar) continuous_const energy damping initial=
      localForce gauge coupling scalar (stationaryValue gauge coupling scalar energy damping initial) := by
  exact (localForce gauge coupling scalar).integral_comp_comm
    (integrand_integrable (fun _ => gauge) continuous_const coupling (fun _ => scalar) continuous_const
      ‖scalarDriftMap scalar‖ (fun _ _ => le_rfl) energy damping positive initial)

theorem stationary_frequency_equation (gauge : GaugeProfile) (coupling : ℝ) (scalar : ScalarProfile)
    (energy damping : ℝ) (positive : 0<damping) (test : Quantum.Generator.domain freeAction) (initial : FullMatterL2) :
    ((energy : ℂ)+Complex.I*(damping : ℂ))*inner ℂ (test : FullMatterL2)
      (stationaryValue gauge coupling scalar energy damping initial)-
      inner ℂ (Quantum.Generator.hamiltonian freeAction test)
        (stationaryValue gauge coupling scalar energy damping initial)-
      Complex.I*inner ℂ (test : FullMatterL2)
        (localForce gauge coupling scalar (stationaryValue gauge coupling scalar energy damping initial))=
          Complex.I*inner ℂ (test : FullMatterL2) initial := by
  have generated := frequency_equation (fun _ => gauge) continuous_const coupling (fun _ => scalar) continuous_const
    ‖gaugePotential gauge‖ ‖scalarDriftMap scalar‖ (fun _ _ => le_rfl) (fun _ _ => le_rfl)
    energy damping positive test initial
  rw [constant_forceValue gauge coupling scalar energy damping positive initial] at generated
  exact generated

theorem stationary_bound (gauge : GaugeProfile) (coupling : ℝ) (scalar : ScalarProfile)
    (energy damping : ℝ) (positive : 0<damping) (initial : FullMatterL2) :
    ‖stationaryValue gauge coupling scalar energy damping initial‖≤
      (damping⁻¹+‖scalarDriftMap scalar‖*damping⁻¹^2)*‖initial‖ :=
  value_bound (fun _ => gauge) continuous_const coupling (fun _ => scalar) continuous_const
    ‖scalarDriftMap scalar‖ (fun _ _ => le_rfl) energy damping positive initial

theorem stationaryValue_injective (gauge : GaugeProfile) (coupling : ℝ) (scalar : ScalarProfile)
    (energy damping : ℝ) (positive : 0<damping) :
    Function.Injective (stationaryValue gauge coupling scalar energy damping) := by
  intro u v same
  have paired (test : Quantum.Generator.domain freeAction) : inner ℂ (test : FullMatterL2) u=inner ℂ (test : FullMatterL2) v := by
    have first := stationary_frequency_equation gauge coupling scalar energy damping positive test u
    have second := stationary_frequency_equation gauge coupling scalar energy damping positive test v
    rw [same] at first
    exact mul_left_cancel₀ Complex.I_ne_zero (first.symm.trans second)
  have all (test : FullMatterL2) : inner ℂ test u=inner ℂ test v :=
    free_domain_dense.induction (fun x inside => paired ⟨x,inside⟩)
      (isClosed_eq (continuous_id.inner continuous_const) (continuous_id.inner continuous_const)) test
  exact ext_inner_left ℂ all

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryLaplace
