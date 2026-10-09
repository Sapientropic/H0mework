import H0mework.Versions.R3bbcbd59.Physics.LowEnergy.FullQuantum.HistoryVariation.Operator

/-! A genuine operator-norm derivative of the actual all-time primitive field family. -/
set_option autoImplicit false
open MeasureTheory Set Filter Topology Asymptotics
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryVariation
open FullSpace GaugeGreen ScalarGreen GaugeHistory HistoryForcing PerturbedGreen
noncomputable section
variable (gauge direction : ℝ → GaugeProfile) (continuousGauge : Continuous gauge) (continuousDirection : Continuous direction)
    (coupling : ℝ) (scalar scalarDirection : ℝ → ScalarProfile)
    (continuousScalar : Continuous scalar) (continuousScalarDirection : Continuous scalarDirection)
local notation "U" => familyOperator gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
  continuousScalar continuousScalarDirection
local notation "D" => responseOperator gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
  continuousScalar continuousScalarDirection
attribute [local irreducible] fullOperator familyOperator responseOperator

theorem operator_remainder (time M : ℝ) (nonnegative : 0≤M)
    (bounded : ∀ r ∈ uIcc 0 time, sourceMajorant direction coupling scalar scalarDirection r≤M)
    (epsilon : ℝ) (near : |epsilon|≤1) :
    ‖U epsilon 0 time-fullOperator gauge continuousGauge coupling scalar continuousScalar 0 time-
      (epsilon : ℂ) • D time‖≤|epsilon|^2 * |time|^2 * (1+|time| * M)^3 * M^2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro initial
  simpa only [sub_apply,smul_apply,responseOperator_apply] using!
    quadratic_remainder gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
      continuousScalar continuousScalarDirection time M nonnegative bounded epsilon near time right_mem_uIcc initial

theorem familyOperator_derivative (time : ℝ) : HasDerivAt (fun epsilon : ℝ => U epsilon 0 time) (D time) 0 := by
  obtain ⟨M,nonnegative,bounded⟩ := source_window_bound direction continuousDirection coupling scalar scalarDirection
    continuousScalar continuousScalarDirection time
  have near : ∀ᶠ epsilon : ℝ in 𝓝 0, |epsilon|≤1 := by
    filter_upwards [Icc_mem_nhds (by norm_num : (-1 : ℝ)<0) (by norm_num : (0 : ℝ)<1)] with epsilon inside
    exact abs_le.mpr inside
  have quadratic : (fun epsilon : ℝ => U epsilon 0 time-
      fullOperator gauge continuousGauge coupling scalar continuousScalar 0 time-epsilon • D time)
      =O[𝓝 0] (fun epsilon : ℝ => epsilon^2) := by
    apply IsBigO.of_bound (|time|^2 * (1+|time| * M)^3 * M^2)
    filter_upwards [near] with epsilon small
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
    apply (operator_remainder gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
      continuousScalar continuousScalarDirection time M nonnegative bounded epsilon small).trans_eq
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg epsilon),sq_abs]
    ring
  have little := quadratic.trans_isLittleO (isLittleO_pow_id (𝕜 := ℝ) (by norm_num : 1<2))
  have atZero : U 0 0 time=fullOperator gauge continuousGauge coupling scalar continuousScalar 0 time := by
    apply ContinuousLinearMap.ext
    intro initial
    exact familyOperator_zero gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
      continuousScalar continuousScalarDirection 0 time initial
  rw [hasDerivAt_iff_isLittleO]
  simpa only [atZero,sub_zero] using little

theorem responseOperator_integral (time : ℝ) (initial : FullMatterL2) :
    D time initial=∫ r in (0 : ℝ)..time, fullOperator gauge continuousGauge coupling scalar continuousScalar r time
      (localForce (direction r) coupling (scalarDirection r)
        (fullOperator gauge continuousGauge coupling scalar continuousScalar 0 r initial)) := by
  simp only [responseOperator_apply,insertionResponse,insertionIntegrand,familyOperator_zero]

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryVariation
