import H0mework.Versions.R3bbcbd59.Physics.LowEnergy.FullQuantum.HistoryVariation.ResponseBound

/-! Reinsert the exact finite difference to obtain the genuine quadratic remainder. -/
set_option autoImplicit false
open MeasureTheory Set
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryVariation
open FullSpace GaugeGreen ScalarGreen GaugeHistory HistoryForcing PerturbedGreen
noncomputable section
variable (gauge direction : ℝ → GaugeProfile) (continuousGauge : Continuous gauge) (continuousDirection : Continuous direction)
    (coupling : ℝ) (scalar scalarDirection : ℝ → ScalarProfile)
    (continuousScalar : Continuous scalar) (continuousScalarDirection : Continuous scalarDirection)
local notation "U" => familyOperator gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
  continuousScalar continuousScalarDirection
local notation "R" => insertionResponse gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
  continuousScalar continuousScalarDirection
attribute [local irreducible] fullOperator

theorem family_difference_bound (window M : ℝ) (nonnegative : 0≤M)
    (bounded : ∀ r ∈ uIcc 0 window, sourceMajorant direction coupling scalar scalarDirection r≤M)
    (epsilon : ℝ) (near : |epsilon|≤1) (time : ℝ) (timeIn : time ∈ uIcc 0 window) (initial : FullMatterL2) :
    ‖U epsilon 0 time initial-fullOperator gauge continuousGauge coupling scalar continuousScalar 0 time initial‖≤
      |epsilon| * |window| * (1+|window| * M)^2 * M * ‖initial‖ := by
  rw [family_difference,norm_smul,Complex.norm_real,Real.norm_eq_abs]
  have estimate := insertionResponse_bound gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
    continuousScalar continuousScalarDirection window M nonnegative bounded epsilon near time timeIn initial
  exact (mul_le_mul_of_nonneg_left estimate (abs_nonneg epsilon)).trans_eq (by ring)

theorem response_difference (epsilon time : ℝ) (initial : FullMatterL2) :
    R epsilon time initial-R 0 time initial=
      ∫ r in (0 : ℝ)..time, fullOperator gauge continuousGauge coupling scalar continuousScalar r time
        (localForce (direction r) coupling (scalarDirection r)
          (U epsilon 0 r initial-fullOperator gauge continuousGauge coupling scalar continuousScalar 0 r initial)) := by
  rw [insertionResponse,insertionResponse,← intervalIntegral.integral_sub
    ((insertionIntegrand_continuous gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
      continuousScalar continuousScalarDirection epsilon time initial).intervalIntegrable (μ := volume) 0 time)
    ((insertionIntegrand_continuous gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
      continuousScalar continuousScalarDirection 0 time initial).intervalIntegrable (μ := volume) 0 time)]
  apply intervalIntegral.integral_congr
  intro r _
  simp only [insertionIntegrand,familyOperator_zero,map_sub]

theorem remainder_exact (epsilon time : ℝ) (initial : FullMatterL2) :
    U epsilon 0 time initial-fullOperator gauge continuousGauge coupling scalar continuousScalar 0 time initial-
      (epsilon : ℂ) • R 0 time initial=(epsilon : ℂ) • (R epsilon time initial-R 0 time initial) := by
  rw [family_difference,smul_sub]

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryVariation
