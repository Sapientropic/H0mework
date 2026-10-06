import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.HistoryGreen.FreeSpace
import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.HistoryLaplace.Stationary

/-! The same free time integral supplies the original Fourier resolvent's weak equation. -/
set_option autoImplicit false
open MeasureTheory Set
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryGreen
open FullSpace GaugeGreen ScalarGreen GaugeHistory
noncomputable section

theorem zero_scalar_history (gauge : ℝ → GaugeProfile) (continuousGauge : Continuous gauge)
    (coupling start time : ℝ) (initial : FullMatterL2) :
    fullOperator gauge continuousGauge coupling (fun _ => 0) continuous_const start time initial=
      gaugeUnitary gauge continuousGauge coupling start time initial := by
  rw [fullOperator_apply]
  have killed (t : ℝ) (v : FullMatterL2) : scalarInteraction gauge continuousGauge coupling (fun _ => 0) t v=0 := by
    rw [scalarInteraction_apply,map_zero,zero_apply,map_zero]
  simp only [triangularCurve,insertionIntegral,killed,intervalIntegral.integral_zero,add_zero]
  exact gaugeUnitary_compose gauge continuousGauge coupling start 0 time initial

theorem zero_coupling_history (gauge : ℝ → GaugeProfile) (continuousGauge : Continuous gauge)
    (start time : ℝ) (initial : FullMatterL2) :
    gaugeUnitary gauge continuousGauge 0 start time initial=spatialFree (time-start) initial := by
  let d := nativeDevelopment gauge continuousGauge
  have constant (v : FullMatterL2) : d.curve 0 start v=fun _ => v := by
    apply global_curve_unique _ (interactionHamiltonian_selfAdjoint gauge) 0 start
      _ _ (d.evolves 0 start v)
    · intro t
      simpa only [generator,Complex.ofReal_zero,mul_zero,zero_smul,zero_apply] using! hasDerivAt_const t v
    · exact d.starts 0 start v
  rw [gaugeUnitary_apply]
  change spatialFree time (d.curve 0 start (spatialFree (-start) initial) time)=_
  rw [constant,← spatialFree_add,sub_eq_add_neg]

theorem free_history_integral (energy damping : ℝ) (positive : 0<damping) (initial : FullMatterL2) :
    HistoryLaplace.stationaryValue 0 0 0 energy damping initial=
      Complex.I • freeR 0 energy damping positive initial := by
  rw [HistoryLaplace.stationaryValue,HistoryLaplace.value]
  calc
    _ = ∫ t : ℝ in Ioi 0, MatterSpace.Response.temporalWeight energy damping t • spatialFree t initial := by
      apply integral_congr_ae
      exact ae_of_all _ fun t => by
        unfold HistoryLaplace.integrand
        rw [zero_scalar_history,zero_coupling_history,sub_zero]
    _ = _ := freeSpatialIntegral_original energy damping positive initial

theorem freeR_weak (energy damping : ℝ) (positive : 0<damping)
    (test : Quantum.Generator.domain freeAction) (source : FullMatterL2) :
    ((energy : ℂ)+Complex.I*(damping : ℂ))*inner ℂ (test : FullMatterL2)
        (freeR 0 energy damping positive source)-
      inner ℂ (Quantum.Generator.hamiltonian freeAction test)
        (freeR 0 energy damping positive source)=inner ℂ (test : FullMatterL2) source := by
  have weak := HistoryLaplace.stationary_frequency_equation 0 0 0 energy damping positive test source
  rw [free_history_integral energy damping positive source] at weak
  simp only [localForce,Complex.ofReal_zero,mul_zero,zero_smul,map_zero,add_zero,zero_apply,
    inner_zero_right,mul_zero,sub_zero,inner_smul_right] at weak
  apply mul_left_cancel₀ Complex.I_ne_zero
  calc
    _ = ((energy : ℂ)+Complex.I*(damping : ℂ))*(Complex.I*inner ℂ (test : FullMatterL2)
        (freeR 0 energy damping positive source))-
      Complex.I*inner ℂ (Quantum.Generator.hamiltonian freeAction test)
        (freeR 0 energy damping positive source) := by ring
    _ = _ := weak

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryGreen
