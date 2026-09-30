import H0mework.Physics.LowEnergy.FullQuantum.HistoryGreen.FreeWeak
import H0mework.Physics.LowEnergy.FullQuantum.HistoryGreen.WeakUnique
import H0mework.Physics.LowEnergy.FullQuantum.HistoryLaplace.Native

/-! The source weak frequency equation determines the actual Fourier integral equation. -/
set_option autoImplicit false
open MeasureTheory
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryGreen
open FullSpace GaugeGreen ScalarGreen GaugeHistory HistoryLaplace
noncomputable section
attribute [local irreducible] fullOperator value

theorem history_free_equation (gauge : ℝ → GaugeProfile) (continuousGauge : Continuous gauge) (coupling : ℝ)
    (scalar : ℝ → ScalarProfile) (continuousScalar : Continuous scalar) (G M : ℝ)
    (gaugeBound : ∀ t, 0≤t → ‖gaugePotential (gauge t)‖≤G)
    (scalarBound : ∀ t, 0≤t → ‖scalarDriftMap (scalar t)‖≤M)
    (energy damping : ℝ) (positive : 0<damping) (initial : FullMatterL2) :
    value gauge continuousGauge coupling scalar continuousScalar energy damping initial=
      freeR 0 energy damping positive (Complex.I • (initial+
        forceValue gauge continuousGauge coupling scalar continuousScalar energy damping initial)) := by
  apply weak_free_unique energy damping positive
  intro test
  rw [freeR_weak energy damping positive test]
  simp only [inner_smul_right,inner_add_right]
  linear_combination frequency_equation gauge continuousGauge coupling scalar continuousScalar
    G M gaugeBound scalarBound energy damping positive test initial

theorem stationary_free_equation (gauge : GaugeProfile) (coupling : ℝ) (scalar : ScalarProfile)
    (energy damping : ℝ) (positive : 0<damping) (initial : FullMatterL2) :
    stationaryValue gauge coupling scalar energy damping initial=
      freeR 0 energy damping positive (Complex.I • (initial+
        localForce gauge coupling scalar (stationaryValue gauge coupling scalar energy damping initial))) := by
  have generated := history_free_equation (fun _ => gauge) continuous_const coupling
    (fun _ => scalar) continuous_const ‖gaugePotential gauge‖ ‖scalarDriftMap scalar‖
    (fun _ _ => le_rfl) (fun _ _ => le_rfl) energy damping positive initial
  rw [constant_forceValue gauge coupling scalar energy damping positive initial] at generated
  exact generated

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryGreen
