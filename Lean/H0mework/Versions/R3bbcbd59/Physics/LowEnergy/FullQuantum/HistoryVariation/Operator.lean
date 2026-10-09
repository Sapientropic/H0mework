import H0mework.Versions.R3bbcbd59.Physics.LowEnergy.FullQuantum.HistoryVariation.Quadratic

/-! The genuine source insertion becomes a bounded operator using its common initial-data bound. -/
set_option autoImplicit false
open MeasureTheory Set
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryVariation
open FullSpace GaugeGreen ScalarGreen GaugeHistory HistoryForcing PerturbedGreen
noncomputable section
variable (gauge direction : ℝ → GaugeProfile) (continuousGauge : Continuous gauge) (continuousDirection : Continuous direction)
    (coupling : ℝ) (scalar scalarDirection : ℝ → ScalarProfile)
    (continuousScalar : Continuous scalar) (continuousScalarDirection : Continuous scalarDirection)
local notation "R" => insertionResponse gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
  continuousScalar continuousScalarDirection

def responseLinear (time : ℝ) : FullMatterL2 →ₗ[ℂ] FullMatterL2 where
  toFun := R 0 time
  map_add' u v := by
    simp only [insertionResponse,insertionIntegrand,map_add]
    exact intervalIntegral.integral_add
      ((insertionIntegrand_continuous gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
        continuousScalar continuousScalarDirection 0 time u).intervalIntegrable (μ := volume) 0 time)
      ((insertionIntegrand_continuous gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
        continuousScalar continuousScalarDirection 0 time v).intervalIntegrable (μ := volume) 0 time)
  map_smul' c u := by
    simp only [insertionResponse,insertionIntegrand,map_smul,intervalIntegral.integral_smul,RingHom.id_apply]

theorem responseLinear_bounded (time : ℝ) :
    ∃ C, ∀ u, ‖responseLinear gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
      continuousScalar continuousScalarDirection time u‖≤C*‖u‖ := by
  obtain ⟨M,nonnegative,bounded⟩ := source_window_bound direction continuousDirection coupling scalar scalarDirection
    continuousScalar continuousScalarDirection time
  refine ⟨|time| * (1+|time| * M)^2 * M,fun u => ?_⟩
  exact insertionResponse_bound gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
    continuousScalar continuousScalarDirection time M nonnegative bounded 0 (by norm_num) time right_mem_uIcc u

def responseOperator (time : ℝ) : SpatialOperators :=
  (responseLinear gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
    continuousScalar continuousScalarDirection time).mkContinuousOfExistsBound
    (responseLinear_bounded gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
      continuousScalar continuousScalarDirection time)

theorem responseOperator_apply (time : ℝ) (initial : FullMatterL2) :
    responseOperator gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
      continuousScalar continuousScalarDirection time initial=R 0 time initial := rfl

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryVariation
