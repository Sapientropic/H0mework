import H0mework.Physics.LowEnergy.VertexTensor.Normalization

/-! The source tensor anisotropy is an exact quadratic-momentum correction,
with a generated uniform bound and its first nonzero coefficient. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.VertexTensor
open LightModes LightInteraction DrivenInteraction Stage9C.Material.SpinPair Filter Topology
noncomputable section

theorem difference_at_zero (same : Bool) (r : ℝ) :
    value (differenceTerms same) r 0= -(4475/972 : ℝ)*r := by
  cases same <;> norm_num [differenceTerms,sameDifference,oppositeDifference,value]

def physicalCorrection (same : Bool) (q : ℝ) : ℝ :=
  (lapse*spinScale)^2*responseScale*value (differenceTerms same) (axialRoot q) (q^2)/
    (axialRoot q*(axialDerivative q)^2)

theorem physical_difference (same : Bool) (q : ℝ) :
    physicalLongitudinal same q-physicalTransverse same q=q^2*physicalCorrection same q := by
  rw [physicalLongitudinal,physicalTransverse,transverse_coupling_normal]
  unfold longitudinalCoupling longitudinalNormal physicalCorrection
  ring

theorem denominator_lower (q : ℝ) (small : |q| ≤ momentumRadius) :
    (1/8 : ℝ)≤ axialRoot q*(axialDerivative q)^2 := by
  have window := (sourceRoot .axialPhase).root_in_window (q^2)
  have rootLower := window.1
  change (125/162 : ℝ)-1/20≤ axialRoot q at rootLower
  have derivativeError := ((sourceRoot .axialPhase).error_bound
    (axialRoot q) (q^2) ((sourceRoot .axialPhase).window_bound _ window)
    (momentum_root_domain .axialPhase q small)).2
  have derivativeLower : (1/2 : ℝ)≤ axialDerivative q := by
    unfold axialDerivative
    linarith [(abs_le.mp derivativeError).1]
  have rootHalf : (1/2 : ℝ)≤ axialRoot q := by linarith
  have derivativeSquare : (1/4 : ℝ)≤(axialDerivative q)^2 := by nlinarith
  have generated := mul_le_mul rootHalf derivativeSquare (by norm_num : (0 : ℝ)≤1/4)
    (axial_root_positive q).le
  norm_num at generated ⊢
  exact generated

theorem physical_correction_bound (same : Bool) (q : ℝ) (small : |q| ≤ momentumRadius) :
    |physicalCorrection same q|≤
      8*(lapse*spinScale)^2*responseScale*coefficientBound (differenceTerms same) := by
  have window := (sourceRoot .axialPhase).root_in_window (q^2)
  have qbound : |q^2|≤1 := by
    rw [abs_pow]
    exact (pow_le_pow_left₀ (abs_nonneg q) (small.trans momentumRadius_bound) 2).trans (by norm_num)
  have table := value_bound (differenceTerms same) _ _
    ((sourceRoot .axialPhase).window_bound _ window) qbound
  change |value (differenceTerms same) (axialRoot q) (q^2)|≤ coefficientBound (differenceTerms same) at table
  have factorPositive : 0<(lapse*spinScale)^2*responseScale :=
    mul_pos (sq_pos_of_pos (mul_pos lapse_pos spinScale_pos)) response_scale_positive
  have denominatorPositive : 0<axialRoot q*(axialDerivative q)^2 := by
    have lower := denominator_lower q small
    linarith
  rw [physicalCorrection,abs_div,abs_mul,
    abs_of_pos factorPositive,abs_of_pos denominatorPositive]
  apply (div_le_iff₀ denominatorPositive).mpr
  have numerator := mul_le_mul_of_nonneg_left table factorPositive.le
  have product := mul_le_mul_of_nonneg_left (denominator_lower q small)
    (mul_nonneg factorPositive.le (coefficientBound_nonnegative (differenceTerms same)))
  exact numerator.trans (by nlinarith only [product])

theorem physical_difference_bound (same : Bool) (q : ℝ) (small : |q| ≤ momentumRadius) :
    |physicalLongitudinal same q-physicalTransverse same q|≤
      (8*(lapse*spinScale)^2*responseScale*coefficientBound (differenceTerms same))*q^2 := by
  rw [physical_difference,abs_mul,abs_of_nonneg (sq_nonneg q)]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left (physical_correction_bound same q small) (sq_nonneg q)

theorem physical_correction_limit (same : Bool) :
    Tendsto (physicalCorrection same) (𝓝 0) (𝓝 (-(179*Real.sqrt 15/31250 : ℝ))) := by
  have square : Tendsto (fun q : ℝ => q^2) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_pow 2).tendsto (0 : ℝ)
  have table := ((value_continuous (differenceTerms same)).tendsto ((125/162 : ℝ),0)).comp
    (axial_root_limit.prodMk_nhds square)
  have generated := (table.const_mul ((lapse*spinScale)^2*responseScale)).div
    (axial_root_limit.mul (axial_derivative_limit.pow 2)) (by norm_num)
  rw [difference_at_zero] at generated
  have coefficient : ((lapse*spinScale)^2*responseScale*(-(4475/972 : ℝ)*(125/162)))/
      ((125/162 : ℝ)*1^2)= -(179*Real.sqrt 15/31250) := by
    rw [mul_pow,lapse_sq,spinScale_sq]
    unfold responseScale
    ring
  rw [coefficient] at generated
  exact generated

theorem physical_difference_quadratic_limit (same : Bool) :
    Tendsto (fun q => (physicalLongitudinal same q-physicalTransverse same q)/q^2)
      (𝓝[≠] 0) (𝓝 (-(179*Real.sqrt 15/31250 : ℝ))) := by
  apply ((physical_correction_limit same).mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with q nonzero
  rw [physical_difference]
  have hq : q≠0 := nonzero
  field_simp

end
end SaturationMonoid.PhysicsCore.LowEnergy.VertexTensor
