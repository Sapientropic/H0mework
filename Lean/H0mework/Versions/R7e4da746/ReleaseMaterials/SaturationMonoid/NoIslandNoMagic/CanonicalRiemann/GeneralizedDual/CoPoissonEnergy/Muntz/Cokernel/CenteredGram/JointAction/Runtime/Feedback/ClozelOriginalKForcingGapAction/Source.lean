import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceGramAction.Receipt

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKForcingGapAction
open Complex MeasureTheory Set Filter FourierTransform BurnolPhysicalState
open OriginalRieszSource OriginalKSourceResolventReconstruction OriginalKSourceGramAction
open OriginalRieszFinitePairing.CoPoisson.Ward
open scoped Topology InnerProductSpace
noncomputable section

local notation "q" => (1/4 : ℝ)
local notation "μq" => volume.restrict (symmetricInterval q)
local notation "mu" => burnolQuarterMeanCoefficient (burnolTruncatedFourier (Response.u : BurnolQuarterIntervalL2))
local notation "nu" => burnolQuarterMeanCoefficient (burnolTruncatedFourier (Response.v : BurnolQuarterIntervalL2))

private theorem original_v_full : (Response.v : BurnolQuarterIntervalL2) =
    burnolTruncatedFourier (Response.u : BurnolQuarterIntervalL2) - mu • intervalConstant q := by
  exact Constructor.zeroMean_read _

private theorem original_u_full :
    (Response.u : BurnolQuarterIntervalL2) - burnolTruncatedFourier (Response.v : BurnolQuarterIntervalL2) =
      (Response.eta : BurnolQuarterIntervalL2) - nu • intervalConstant q := by
  have paid := congrArg (fun value : BurnolQuarterMeanZeroCarrier => (value : BurnolQuarterIntervalL2))
    Response.source_pair_equation
  change (Response.u : BurnolQuarterIntervalL2) -
    (Constructor.zeroMean (burnolTruncatedFourier (Response.v : BurnolQuarterIntervalL2)) : BurnolQuarterIntervalL2) =
      (Response.eta : BurnolQuarterIntervalL2) at paid
  rw [Constructor.zeroMean_read] at paid
  linear_combination (norm := module) paid

private theorem constant_reflection : reflectL2 ConstantDual.seed = ConstantDual.seed := by
  change reflectL2 (burnolRadiusZeroExtension q (intervalConstant q)) = _
  rw [burnolRadiusZeroExtension_reflect, reflectRestricted_intervalConstant]
  rfl

/-- This is the original fixed B response equation, before any source membership is inferred. -/
theorem forcing0_quarter_restriction (coordinate : BurnolCompletedMellinCoordinate) :
    burnolQuarterRestriction (regularForcing coordinate 0) =
      (mu + 1/2 - sourceRate coordinate) • intervalConstant q := by
  change burnolQuarterRestriction (fourierL2 Response.wholeU - Response.wholeV +
    (1/2 - sourceRate coordinate) • ConstantDual.seed) = _
  rw [map_add, map_sub, map_smul]
  change burnolTruncatedFourier (Response.u : BurnolQuarterIntervalL2) -
    burnolQuarterRestriction (burnolQuarterZeroExtension (Response.v : BurnolQuarterIntervalL2)) +
    (1/2 - sourceRate coordinate) • burnolQuarterRestriction (burnolQuarterZeroExtension (intervalConstant q)) = _
  rw [burnolQuarterRestriction_zeroExtension, burnolQuarterRestriction_zeroExtension, original_v_full]
  module

theorem forcing1_quarter_restriction (coordinate : BurnolCompletedMellinCoordinate) :
    burnolQuarterRestriction (regularForcing coordinate 1) =
      (Response.eta : BurnolQuarterIntervalL2) - nu • intervalConstant q +
        (sourceRate coordinate + 1/2) • burnolTruncatedFourier (intervalConstant q) := by
  change burnolQuarterRestriction (Response.wholeU - fourierL2 Response.wholeV +
    (sourceRate coordinate + 1/2) • fourierL2 ConstantDual.seed) = _
  rw [map_add, map_sub, map_smul]
  change burnolQuarterRestriction (burnolQuarterZeroExtension (Response.u : BurnolQuarterIntervalL2)) -
    burnolTruncatedFourier (Response.v : BurnolQuarterIntervalL2) +
    (sourceRate coordinate + 1/2) • burnolTruncatedFourier (intervalConstant q) = _
  rw [burnolQuarterRestriction_zeroExtension, original_u_full]

/-- F² is consumed only on the already even original U, V and constant source. -/
theorem fourier_forcing0_source (coordinate : BurnolCompletedMellinCoordinate) :
    fourierL2 (regularForcing coordinate 0) = regularForcing coordinate 1 -
      (2*sourceRate coordinate) • fourierL2 ConstantDual.seed := by
  change fourierL2 (fourierL2 Response.wholeU - Response.wholeV +
    (1/2-sourceRate coordinate) • ConstantDual.seed) = _
  rw [map_add, map_sub, map_smul, fourierL2_fourierL2, Response.wholeU_reflection]
  change _ = Response.wholeU - fourierL2 Response.wholeV +
    (sourceRate coordinate+1/2) • fourierL2 ConstantDual.seed -
      (2*sourceRate coordinate) • fourierL2 ConstantDual.seed
  module

theorem fourier_forcing1_source (coordinate : BurnolCompletedMellinCoordinate) :
    fourierL2 (regularForcing coordinate 1) = regularForcing coordinate 0 +
      (2*sourceRate coordinate) • ConstantDual.seed := by
  change fourierL2 (Response.wholeU - fourierL2 Response.wholeV +
    (sourceRate coordinate+1/2) • fourierL2 ConstantDual.seed) = _
  rw [map_add, map_sub, map_smul, fourierL2_fourierL2, fourierL2_fourierL2,
    Response.wholeV_reflection, constant_reflection]
  change _ = fourierL2 Response.wholeU - Response.wholeV +
    (1/2-sourceRate coordinate) • ConstantDual.seed +
      (2*sourceRate coordinate) • ConstantDual.seed
  module

theorem forcing0_fourier_quarter_restriction (coordinate : BurnolCompletedMellinCoordinate) :
    burnolQuarterRestriction (fourierL2 (regularForcing coordinate 0)) =
      (Response.eta : BurnolQuarterIntervalL2) - nu • intervalConstant q +
        (1/2-sourceRate coordinate) • burnolTruncatedFourier (intervalConstant q) := by
  rw [fourier_forcing0_source, map_sub, map_smul, forcing1_quarter_restriction]
  change (Response.eta : BurnolQuarterIntervalL2) - nu • intervalConstant q +
    (sourceRate coordinate+1/2) • burnolTruncatedFourier (intervalConstant q) -
    (2*sourceRate coordinate) • burnolTruncatedFourier (intervalConstant q) = _
  module

theorem forcing1_fourier_quarter_restriction (coordinate : BurnolCompletedMellinCoordinate) :
    burnolQuarterRestriction (fourierL2 (regularForcing coordinate 1)) =
      (mu + sourceRate coordinate + 1/2) • intervalConstant q := by
  rw [fourier_forcing1_source, map_add, map_smul, forcing0_quarter_restriction]
  change (mu+1/2-sourceRate coordinate) • intervalConstant q +
    (2*sourceRate coordinate) • burnolQuarterRestriction (burnolQuarterZeroExtension (intervalConstant q)) = _
  rw [burnolQuarterRestriction_zeroExtension]
  module

private theorem mean_add (left right : BurnolQuarterIntervalL2) :
    burnolQuarterMeanCoefficient (left+right) =
      burnolQuarterMeanCoefficient left + burnolQuarterMeanCoefficient right := by
  simp only [burnolQuarterMeanCoefficient, inner_add_right, add_div]

private theorem mean_sub (left right : BurnolQuarterIntervalL2) :
    burnolQuarterMeanCoefficient (left-right) =
      burnolQuarterMeanCoefficient left - burnolQuarterMeanCoefficient right := by
  simp only [burnolQuarterMeanCoefficient, inner_sub_right, sub_div]

private theorem mean_smul (scalar : ℂ) (value : BurnolQuarterIntervalL2) :
    burnolQuarterMeanCoefficient (scalar • value) = scalar * burnolQuarterMeanCoefficient value := by
  simp only [burnolQuarterMeanCoefficient, inner_smul_right]
  ring

private theorem constant_inner : inner ℂ (intervalConstant q) (intervalConstant q) = (1/2 : ℂ) := by
  rw [L2.inner_def]
  have actual : (fun x : ℝ => inner ℂ (intervalConstant q x) (intervalConstant q x)) =ᵐ[μq]
      fun _ => (1 : ℂ) := by
    filter_upwards [intervalConstant_coeFn q] with x read
    rw [read]
    norm_num
  rw [integral_congr_ae actual,integral_const]
  norm_num [symmetricInterval,Complex.real_smul]

private theorem mean_constant : burnolQuarterMeanCoefficient (intervalConstant q) = 1 := by
  have normEq := burnolIntervalConstant_norm_sq (by norm_num : (0 : ℝ) < q)
  have normRealRaw : ‖intervalConstant q‖^2 = 2*q := by exact_mod_cast normEq
  have normReal : ‖intervalConstant q‖^2 = (1/2 : ℝ) := by linarith [normRealRaw]
  unfold burnolQuarterMeanCoefficient
  rw [constant_inner,normReal]
  norm_num

/-- Both original means survive, with their correct position/Fourier roles. -/
theorem forcing_quarter_means (coordinate : BurnolCompletedMellinCoordinate) :
    burnolQuarterMeanCoefficient (burnolQuarterRestriction (regularForcing coordinate 0)) = mu+1/2-sourceRate coordinate ∧
    burnolQuarterMeanCoefficient (burnolQuarterRestriction (regularForcing coordinate 1)) =
      -nu + (sourceRate coordinate+1/2)*burnolQuarterMeanCoefficient (burnolTruncatedFourier (intervalConstant q)) ∧
    burnolQuarterMeanCoefficient (burnolQuarterRestriction (fourierL2 (regularForcing coordinate 0))) =
      -nu + (1/2-sourceRate coordinate)*burnolQuarterMeanCoefficient (burnolTruncatedFourier (intervalConstant q)) ∧
    burnolQuarterMeanCoefficient (burnolQuarterRestriction (fourierL2 (regularForcing coordinate 1))) = mu+sourceRate coordinate+1/2 := by
  rw [forcing0_quarter_restriction,forcing1_quarter_restriction,
    forcing0_fourier_quarter_restriction,forcing1_fourier_quarter_restriction]
  simp only [mean_add,mean_sub,mean_smul,mean_constant,Constructor.mean_zero,mul_one,zero_sub]
  exact ⟨True.intro,True.intro,True.intro,True.intro⟩

/-- Quarter restriction is kept distinct from the physical Q projection. -/
theorem quarter_dilation_constant (value : BurnolL2) (coefficient : ℂ)
    (gap : burnolQuarterRestriction value = coefficient • intervalConstant q)
    (shift : ℝ) (nonpositive : shift ≤ 0) :
    burnolQuarterRestriction (burnolMultiplicativeDilation shift value) =
      ((Real.exp (shift/2) : ℂ)*coefficient) • intervalConstant q := by
  have sourceRestricted : (value : ℝ → ℂ) =ᵐ[μq] fun _ => coefficient := by
    filter_upwards [LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q) value,
      Lp.coeFn_smul coefficient (intervalConstant q),intervalConstant_coeFn q] with x read scalar constant
    have actual : burnolQuarterRestriction value x = value x := read
    rw [gap] at actual
    rw [← actual,scalar,Pi.smul_apply,smul_eq_mul,constant,mul_one]
  have sourceGlobal := (ae_restrict_iff' (measurableSet_symmetricInterval q)).mp sourceRestricted
  have qmp : Measure.QuasiMeasurePreserving (fun x : ℝ => Real.exp shift*x) volume volume := by
    simpa only [smul_eq_mul] using
      (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
        (r := Real.exp shift) (Real.exp_ne_zero shift))
  apply Lp.ext
  filter_upwards [LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q) (burnolMultiplicativeDilation shift value),
    ae_restrict_of_ae (burnolMultiplicativeDilation_coeFn shift value),
    ae_restrict_of_ae (qmp.ae sourceGlobal),ae_restrict_mem (measurableSet_symmetricInterval q),
    Lp.coeFn_smul ((Real.exp (shift/2) : ℂ)*coefficient) (intervalConstant q),
    intervalConstant_coeFn q] with x restriction dilation source inside scalar constant
  have scaled : Real.exp shift*x ∈ symmetricInterval q := by
    have small := abs_le.mpr inside
    have bounded : |Real.exp shift*x| ≤ q := by
      rw [abs_mul,abs_of_pos (Real.exp_pos shift)]
      exact (mul_le_of_le_one_left (abs_nonneg x) (Real.exp_le_one_iff.mpr nonpositive)).trans small
    exact abs_le.mp bounded
  change burnolQuarterRestriction (burnolMultiplicativeDilation shift value) x = _
  rw [show burnolQuarterRestriction (burnolMultiplicativeDilation shift value) x =
    burnolMultiplicativeDilation shift value x from restriction,dilation,scalar]
  change (Real.exp (shift/2) : ℂ)*value (Real.exp shift*x) =
    ((Real.exp (shift/2) : ℂ)*coefficient)*intervalConstant q x
  rw [source scaled,constant,mul_one]

/-- The actual inward R integral computes the full constant gap, with no Pa premise. -/
theorem right_resolvent_quarter_constant (z : ℂ) (right : 1/4 < z.re)
    (value : BurnolL2) (coefficient : ℂ)
    (gap : burnolQuarterRestriction value = coefficient • intervalConstant q) :
    burnolQuarterRestriction (burnolDirectRightResolvent z value) =
      (-coefficient/z) • intervalConstant q := by
  have integrable := burnolDirectRightResolventIntegrand_integrableOn z right value
  unfold burnolDirectRightResolvent
  rw [map_neg, ← burnolQuarterRestriction.integral_comp_comm integrable]
  have actual : (fun time : ℝ => burnolQuarterRestriction (burnolDirectRightResolventIntegrand z value time)) =ᵐ[
      volume.restrict (Ioi 0)] fun time => (Complex.exp (-z*(time : ℂ))*coefficient) • intervalConstant q := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with time positive
    have timePositive : 0 < time := positive
    unfold burnolDirectRightResolventIntegrand
    rw [map_smul,quarter_dilation_constant value coefficient gap (-time/2) (by linarith),smul_smul]
    congr 1
    unfold positiveMellinQuarterRightResolventWeight
    rw [Complex.ofReal_exp,← mul_assoc,← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [integral_congr_ae actual,integral_smul_const,integral_mul_const]
  have exponential := integral_exp_mul_complex_Ioi (a := -z) (by
    simp only [Complex.neg_re];linarith) 0
  simp only [Complex.ofReal_zero,mul_zero,Complex.exp_zero,neg_div_neg_eq] at exponential
  rw [exponential]
  rw [← neg_smul]
  congr 1
  ring

theorem forcing0_resolvent_quarter (coordinate : BurnolCompletedMellinCoordinate) :
    burnolQuarterRestriction (sourceResolvent coordinate (regularForcing coordinate 0)) =
      (-2*(mu+1/2-sourceRate coordinate)/star coordinate.value) • intervalConstant q := by
  have right : 1/4 < (star coordinate.value/2).re := by
    rw [Complex.div_re];norm_num;linarith [coordinate.rightHalf]
  have actual := right_resolvent_quarter_constant (star coordinate.value/2) right
    (regularForcing coordinate 0) (mu+1/2-sourceRate coordinate) (forcing0_quarter_restriction coordinate)
  change burnolQuarterRestriction (sourceResolvent coordinate (regularForcing coordinate 0)) = _ at actual
  rw [actual]
  congr 1
  ring

theorem regular0_quarter (coordinate : BurnolCompletedMellinCoordinate) :
    burnolQuarterRestriction (regularColumns coordinate 0) =
      ((mu+1/2-sourceRate coordinate)/star coordinate.value) • intervalConstant q := by
  change burnolQuarterRestriction (-(1/2 : ℂ) • sourceResolvent coordinate (regularForcing coordinate 0)) = _
  rw [map_smul,forcing0_resolvent_quarter,smul_smul]
  congr 1
  ring

/-- Only the inward contact is computed; the expanding shell remains a separate operand. -/
theorem inward_constant_contact (value : BurnolL2) (coefficient : ℂ)
    (gap : burnolQuarterRestriction value = coefficient • intervalConstant q)
    (h : ℝ) (nonnegative : 0 ≤ h) :
    inner ℂ value (burnolMultiplicativeDilation h ConstantDual.seed) =
      ((Real.exp (-h/2) : ℂ)/2)*star coefficient := by
  have flip := (burnolMultiplicativeDilation (-h)).inner_map_eq_flip value ConstantDual.seed
  rw [← burnolMultiplicativeDilation_neg_eq_symm (-h),neg_neg] at flip
  rw [← flip]
  have paired : inner ℂ (burnolMultiplicativeDilation (-h) value) ConstantDual.seed =
      inner ℂ (burnolQuarterRestriction (burnolMultiplicativeDilation (-h) value)) (intervalConstant q) :=
    ContinuousLinearMap.adjoint_inner_right burnolQuarterRestriction _ _
  rw [paired,quarter_dilation_constant value coefficient gap (-h) (by linarith),inner_smul_left]
  rw [constant_inner]
  change star ((Real.exp (-h/2) : ℂ)*coefficient)*(1/2 : ℂ) = _
  rw [star_mul]
  have realScalar : star (Real.exp (-h/2) : ℂ) = (Real.exp (-h/2) : ℂ) := by
    exact Complex.conj_ofReal _
  rw [realScalar]
  ring

theorem regular0_inward_constant_contact (coordinate : BurnolCompletedMellinCoordinate)
    (h : ℝ) (nonnegative : 0 ≤ h) :
    inner ℂ (regularColumns coordinate 0) (burnolMultiplicativeDilation h ConstantDual.seed) =
      ((Real.exp (-h/2) : ℂ)/2)*
        star ((mu+1/2-sourceRate coordinate)/star coordinate.value) :=
  inward_constant_contact _ _ (regular0_quarter coordinate) h nonnegative

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKForcingGapAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
