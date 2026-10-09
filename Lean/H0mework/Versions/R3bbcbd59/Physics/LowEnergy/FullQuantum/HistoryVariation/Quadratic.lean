import H0mework.Versions.R3bbcbd59.Physics.LowEnergy.FullQuantum.HistoryVariation.Remainder

/-! The second actual insertion gives a uniform quadratic parameter remainder. -/
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

theorem response_difference_bound (window M : ℝ) (nonnegative : 0≤M)
    (bounded : ∀ r ∈ uIcc 0 window, sourceMajorant direction coupling scalar scalarDirection r≤M)
    (epsilon : ℝ) (near : |epsilon|≤1) (time : ℝ) (timeIn : time ∈ uIcc 0 window) (initial : FullMatterL2) :
    ‖R epsilon time initial-R 0 time initial‖≤|epsilon| * |window|^2 * (1+|window| * M)^3 * M^2 * ‖initial‖ := by
  let K := 1+|window| * M
  have Kpos : 0≤K := by dsimp only [K]; positivity
  have scalarBound (r : ℝ) (hr : r ∈ uIcc 0 window) : ‖scalarDriftMap (scalar r)‖≤M := by
    have controls := (source_majorant_controls direction coupling scalar scalarDirection r M (bounded r hr)).1
    linarith [norm_nonneg (scalarDriftMap (scalarDirection r))]
  have propagated (r : ℝ) (hr : r ∈ uIcc 0 window) (v : FullMatterL2) :
      ‖fullOperator gauge continuousGauge coupling scalar continuousScalar r time
        (localForce (direction r) coupling (scalarDirection r) v)‖≤K*M*‖v‖ := by
    have forceBound := (source_majorant_controls direction coupling scalar scalarDirection r M (bounded r hr)).2
    have applied := ((localForce (direction r) coupling (scalarDirection r)).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right forceBound (norm_nonneg v))
    exact (fullOperator_window_bound gauge continuousGauge coupling scalar continuousScalar window M nonnegative scalarBound
      r time hr timeIn _).trans ((mul_le_mul_of_nonneg_left applied Kpos).trans_eq (by ring))
  have integrandBound (r : ℝ) (hr : r ∈ uIcc 0 window) :
      ‖fullOperator gauge continuousGauge coupling scalar continuousScalar r time
        (localForce (direction r) coupling (scalarDirection r)
          (U epsilon 0 r initial-fullOperator gauge continuousGauge coupling scalar continuousScalar 0 r initial))‖≤
        |epsilon| * |window| * K^3 * M^2 * ‖initial‖ := by
    have difference := family_difference_bound gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
      continuousScalar continuousScalarDirection window M nonnegative bounded epsilon near r hr initial
    exact (propagated r hr _).trans
      ((mul_le_mul_of_nonneg_left difference (mul_nonneg Kpos nonnegative)).trans_eq (by dsimp only [K]; ring))
  rw [response_difference]
  have generated := window_integral_bound _ window
    (|epsilon| * |window| * K^3 * M^2 * ‖initial‖) (by positivity) integrandBound 0 time left_mem_uIcc timeIn
  exact generated.trans_eq (by dsimp only [K]; ring)

theorem quadratic_remainder (window M : ℝ) (nonnegative : 0≤M)
    (bounded : ∀ r ∈ uIcc 0 window, sourceMajorant direction coupling scalar scalarDirection r≤M)
    (epsilon : ℝ) (near : |epsilon|≤1) (time : ℝ) (timeIn : time ∈ uIcc 0 window) (initial : FullMatterL2) :
    ‖U epsilon 0 time initial-fullOperator gauge continuousGauge coupling scalar continuousScalar 0 time initial-
      (epsilon : ℂ) • R 0 time initial‖≤|epsilon|^2 * |window|^2 * (1+|window| * M)^3 * M^2 * ‖initial‖ := by
  rw [remainder_exact,norm_smul,Complex.norm_real,Real.norm_eq_abs]
  have bound := response_difference_bound gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
    continuousScalar continuousScalarDirection window M nonnegative bounded epsilon near time timeIn initial
  exact (mul_le_mul_of_nonneg_left bound (abs_nonneg epsilon)).trans_eq (by ring)

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryVariation
