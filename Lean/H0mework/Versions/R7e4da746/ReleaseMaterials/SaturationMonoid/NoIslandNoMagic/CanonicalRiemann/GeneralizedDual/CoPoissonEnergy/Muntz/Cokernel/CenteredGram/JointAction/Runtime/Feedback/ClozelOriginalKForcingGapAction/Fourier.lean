import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKForcingGapAction.Source

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1400000
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKForcingGapAction
open Complex MeasureTheory Set Filter FourierTransform BurnolPhysicalState
open OriginalRieszSource OriginalKSourceResolventReconstruction OriginalKSourceGramAction
open OriginalRieszFinitePairing.CoPoisson.Ward
open scoped Topology InnerProductSpace
noncomputable section
local notation "q" => (1/4 : ℝ)
local notation "μq" => volume.restrict (symmetricInterval q)
local notation "rho" => burnolQuarterMeanCoefficient (Constructor.compact (Edge.raw q) (Edge.raw_continuous q)) +
  burnolQuarterMeanCoefficient (burnolTruncatedFourier (Response.v : BurnolQuarterIntervalL2))
local notation "mu" => burnolQuarterMeanCoefficient (burnolTruncatedFourier (Response.u : BurnolQuarterIntervalL2))

def constantFourierRaw : ℝ → ℂ := Constructor.fourierRaw (fun _ => (1 : ℂ))
private def constantFourierSlope : ℝ → ℂ := Constructor.fourierDerivative (fun _ => (1 : ℂ))

private theorem constantFourier_continuous : Continuous constantFourierRaw :=
  Constructor.fourierRaw_continuous _ continuous_const
private theorem constantFourier_slope_continuous : Continuous constantFourierSlope :=
  Constructor.fourierDerivative_continuous _ continuous_const
private theorem constantFourier_derivative (x : ℝ) : HasDerivAt constantFourierRaw (constantFourierSlope x) x :=
  Constructor.fourierRaw_hasDerivAt _ continuous_const x

private theorem constantFourier_read :
    (burnolTruncatedFourier (intervalConstant q) : ℝ → ℂ) =ᵐ[μq] constantFourierRaw := by
  have same := Constructor.fourierRaw_congr _ _ (intervalConstant_coeFn q)
  exact (Constructor.truncatedFourier_read _).trans (EventuallyEq.of_eq same)

private theorem constantFourier_even (x : ℝ) : constantFourierRaw (-x) = constantFourierRaw x := by
  have reflected := intervalIntegral.integral_comp_neg
    (f := fun y => Constructor.phase x y * (1 : ℂ)) (a := -q) (b := q)
  simp only [neg_neg] at reflected
  unfold constantFourierRaw
  rw [Constructor.fourierRaw_integral,Constructor.fourierRaw_integral,← reflected]
  congr 1
  funext y
  simp only [Constructor.phase,neg_mul,mul_neg,neg_neg]

/-- Finite Fourier integration generates the constant source's actual Euler bulk. -/
private theorem constantFourier_ward (frequency : ℝ) :
    (frequency : ℂ)*constantFourierSlope frequency + constantFourierRaw frequency =
      (q : ℂ)*(Constructor.phase frequency q + Constructor.phase frequency (-q)) := by
  let density := fun x : ℝ => Constructor.phase frequency x +
    (x : ℂ)*(-2*(Real.pi : ℂ)*Complex.I*(frequency : ℂ)*Constructor.phase frequency x)
  have regular : Continuous density := by
    have phase := Constructor.phaseContinuous frequency
    dsimp only [density]
    fun_prop
  have derivative (x : ℝ) : HasDerivAt
      (fun t : ℝ => (t : ℂ)*Constructor.phase frequency t) (density x) x := by
    convert! (Complex.ofRealCLM.hasDerivAt (x := x)).mul (Constructor.phase_derivative frequency x) using 1
    simp only [Complex.ofRealCLM_apply,Complex.ofReal_one,density]
    ring
  have integrated := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => derivative x) (regular.intervalIntegrable (-q) q)
  have moment : Continuous (fun x : ℝ => Constructor.phase frequency x*
      (-2*(Real.pi : ℂ)*Complex.I*(x : ℂ))) := by
    have phase := Constructor.phaseContinuous frequency
    fun_prop
  calc
    _ = ∫ x : ℝ in (-q)..q, density x := by
      rw [constantFourierSlope,Constructor.fourierDerivative_integral _ continuous_const,
        constantFourierRaw,Constructor.fourierRaw_integral,← intervalIntegral.integral_const_mul]
      simp only [mul_one]
      rw [← intervalIntegral.integral_add ((moment.const_mul (frequency : ℂ)).intervalIntegrable (-q) q)
          ((Constructor.phaseContinuous frequency).intervalIntegrable (-q) q)]
      apply intervalIntegral.integral_congr
      intro x _
      dsimp only [density]
      ring
    _ = _ := by
      rw [integrated]
      push_cast
      ring

/-- The endpoint subtraction is paid before a global L² Euler inverse is used. -/
def endpointCorrectedConstantState : BurnolQuarterIntervalL2 :=
  burnolTruncatedFourier (intervalConstant q) - constantFourierRaw q • intervalConstant q

def endpointCorrectedConstant : BurnolL2 := burnolQuarterZeroExtension endpointCorrectedConstantState

private theorem endpointCorrected_read :
    (endpointCorrectedConstantState : ℝ → ℂ) =ᵐ[μq] fun x => constantFourierRaw x-constantFourierRaw q := by
  filter_upwards [Lp.coeFn_sub (burnolTruncatedFourier (intervalConstant q))
      (constantFourierRaw q • intervalConstant q),Lp.coeFn_smul (constantFourierRaw q) (intervalConstant q),
    constantFourier_read,intervalConstant_coeFn q] with x difference scalar fourier constant
  change (burnolTruncatedFourier (intervalConstant q)-constantFourierRaw q • intervalConstant q : BurnolQuarterIntervalL2) x = _
  rw [difference,Pi.sub_apply,scalar,Pi.smul_apply,smul_eq_mul,constant,mul_one,fourier]

private def endpointCorrectedForcingRaw (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  (x : ℂ)*constantFourierSlope x +
    (sourceRate coordinate+1/2)*(constantFourierRaw x-constantFourierRaw q)

private theorem endpointCorrectedForcing_continuous (coordinate : BurnolCompletedMellinCoordinate) :
    Continuous (endpointCorrectedForcingRaw coordinate) := by
  have h := constantFourier_continuous
  have hd := constantFourier_slope_continuous
  unfold endpointCorrectedForcingRaw
  fun_prop

def endpointCorrectedForcing (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  burnolQuarterZeroExtension (Constructor.compact (endpointCorrectedForcingRaw coordinate)
    (endpointCorrectedForcing_continuous coordinate))

/-- The full weak cutoff source contains no endpoint delta, because both actual endpoint values are zero. -/
theorem endpointCorrected_euler (coordinate : BurnolCompletedMellinCoordinate) :
    GapEuler.euler (endpointCorrectedConstant : TemperedDistribution ℝ ℂ) +
      sourceRate coordinate • (endpointCorrectedConstant : TemperedDistribution ℝ ℂ) =
        (endpointCorrectedForcing coordinate : TemperedDistribution ℝ ℂ) := by
  ext test
  let bulk := fun x : ℝ => ((x : ℂ)*constantFourierSlope x +
    (constantFourierRaw x-constantFourierRaw q))*test x
  let moment := fun x : ℝ => ((x : ℂ)*(constantFourierRaw x-constantFourierRaw q))*deriv test x
  let mass := fun x : ℝ => (constantFourierRaw x-constantFourierRaw q)*test x
  have testDerivative : Continuous (deriv test) := by
    change Continuous (SchwartzMap.derivCLM ℂ ℂ test)
    exact (SchwartzMap.derivCLM ℂ ℂ test).continuous
  have cb : Continuous bulk := by
    have h := constantFourier_continuous
    have hd := constantFourier_slope_continuous
    dsimp only [bulk]
    fun_prop
  have cm : Continuous moment := by
    have h := constantFourier_continuous
    dsimp only [moment]
    fun_prop
  have cz : Continuous mass := by
    have h := constantFourier_continuous
    dsimp only [mass]
    fun_prop
  have derivative (x : ℝ) : HasDerivAt
      (fun t : ℝ => ((t : ℂ)*(constantFourierRaw t-constantFourierRaw q))*test t)
      (bulk x+moment x) x := by
    convert! (((Complex.ofRealCLM.hasDerivAt (x := x)).mul
      ((constantFourier_derivative x).sub_const (constantFourierRaw q))).mul (test.hasDerivAt x)) using 1
    simp only [Pi.mul_apply,Complex.ofRealCLM_apply,Complex.ofReal_one,bulk,moment]
    ring
  have boundary := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => derivative x) ((cb.add cm).intervalIntegrable (-q) q)
  simp only [constantFourier_even,sub_self,mul_zero,zero_mul] at boundary
  rw [intervalIntegral.integral_add (cb.intervalIntegrable (-q) q) (cm.intervalIntegrable (-q) q),
    intervalIntegral.integral_of_le (by norm_num : -q ≤ q),
    intervalIntegral.integral_of_le (by norm_num : -q ≤ q)] at boundary
  have sourceSplit : (∫ x : ℝ in Ioc (-q) q, endpointCorrectedForcingRaw coordinate x*test x) =
      (∫ x : ℝ in Ioc (-q) q, bulk x) +
        (sourceRate coordinate-1/2)*(∫ x : ℝ in Ioc (-q) q, mass x) := by
    rw [← integral_const_mul,← integral_add
      ((cb.integrableOn_Icc).mono_set Ioc_subset_Icc_self)
      (((cz.integrableOn_Icc).mono_set Ioc_subset_Icc_self).const_mul _)]
    apply integral_congr_ae
    filter_upwards with x
    dsimp only [endpointCorrectedForcingRaw,bulk,mass]
    ring
  change GapEuler.euler (burnolQuarterZeroExtension endpointCorrectedConstantState : TemperedDistribution ℝ ℂ) test +
    sourceRate coordinate*(burnolQuarterZeroExtension endpointCorrectedConstantState : TemperedDistribution ℝ ℂ) test =
      (burnolQuarterZeroExtension (Constructor.compact (endpointCorrectedForcingRaw coordinate)
        (endpointCorrectedForcing_continuous coordinate)) : TemperedDistribution ℝ ℂ) test
  rw [Translator.ForcingCutoff.euler_zeroExtension_pairing _ _ endpointCorrected_read,
    Translator.ForcingCutoff.zeroExtension_pairing _ _ endpointCorrected_read,
    Translator.ForcingCutoff.zeroExtension_pairing _ _ (Constructor.compact_read _ _),sourceSplit]
  change -(∫ x : ℝ in Ioc (-q) q, moment x) -
    (1/2 : ℂ)*(∫ x : ℝ in Ioc (-q) q,mass x) +
    sourceRate coordinate*(∫ x : ℝ in Ioc (-q) q,mass x) = _
  linear_combination -boundary

private theorem endpointCorrectedForcing_state (coordinate : BurnolCompletedMellinCoordinate) :
    burnolQuarterRestriction (endpointCorrectedForcing coordinate) =
      Constructor.compact (Edge.raw q) (Edge.raw_continuous q) +
        (sourceRate coordinate+1/2) • burnolTruncatedFourier (intervalConstant q) -
        (constantFourierRaw q*(sourceRate coordinate+1/2)) • intervalConstant q := by
  rw [endpointCorrectedForcing,burnolQuarterRestriction_zeroExtension]
  have same := Constructor.fourierRaw_congr _ _ (intervalConstant_coeFn q)
  apply Lp.ext
  filter_upwards [Constructor.compact_read (endpointCorrectedForcingRaw coordinate)
      (endpointCorrectedForcing_continuous coordinate),
    Lp.coeFn_sub (Constructor.compact (Edge.raw q) (Edge.raw_continuous q) +
      (sourceRate coordinate+1/2) • burnolTruncatedFourier (intervalConstant q))
      ((constantFourierRaw q*(sourceRate coordinate+1/2)) • intervalConstant q),
    Lp.coeFn_add (Constructor.compact (Edge.raw q) (Edge.raw_continuous q))
      ((sourceRate coordinate+1/2) • burnolTruncatedFourier (intervalConstant q)),
    Lp.coeFn_smul (sourceRate coordinate+1/2) (burnolTruncatedFourier (intervalConstant q)),
    Lp.coeFn_smul (constantFourierRaw q*(sourceRate coordinate+1/2)) (intervalConstant q),
    Edge.quarter_restriction_read,constantFourier_read,intervalConstant_coeFn q]
    with x original difference addition scalar endpoint edge fourier constant
  rw [original,difference,Pi.sub_apply,addition,Pi.add_apply,scalar,endpoint,
    Pi.smul_apply,Pi.smul_apply,smul_eq_mul,smul_eq_mul,fourier,constant,mul_one,edge]
  have rawMatch : burnolRadiusTruncatedFourierRaw q (intervalConstant q) = constantFourierRaw := same
  rw [Edge.raw_apply,rawMatch]
  have ward := constantFourier_ward x
  dsimp only [endpointCorrectedForcingRaw,constantFourierRaw] at ward ⊢
  linear_combination ward

theorem endpointCorrected_resolvent (coordinate : BurnolCompletedMellinCoordinate) :
    -(1/2 : ℂ) • sourceResolvent coordinate (endpointCorrectedForcing coordinate) = endpointCorrectedConstant := by
  have generated := sourceResolvent_euler coordinate (endpointCorrectedForcing coordinate)
  have actual := endpointCorrected_euler coordinate
  have homogeneous : GapEuler.euler
      ((-(1/2 : ℂ) • sourceResolvent coordinate (endpointCorrectedForcing coordinate)-endpointCorrectedConstant : BurnolL2) : TemperedDistribution ℝ ℂ) +
      sourceRate coordinate •
        ((-(1/2 : ℂ) • sourceResolvent coordinate (endpointCorrectedForcing coordinate)-endpointCorrectedConstant : BurnolL2) : TemperedDistribution ℝ ℂ) = 0 := by
    change GapEuler.euler (Lp.toTemperedDistributionCLM ℂ volume 2
      (-(1/2 : ℂ) • sourceResolvent coordinate (endpointCorrectedForcing coordinate)-endpointCorrectedConstant)) +
      sourceRate coordinate • Lp.toTemperedDistributionCLM ℂ volume 2
      (-(1/2 : ℂ) • sourceResolvent coordinate (endpointCorrectedForcing coordinate)-endpointCorrectedConstant) = 0
    simp only [map_sub,map_smul,Lp.toTemperedDistributionCLM_apply]
    linear_combination (norm := module) -(1/2 : ℂ) • generated - actual
  have positive : 0 < (sourceRate coordinate).re := by
    simp only [sourceRate,Complex.sub_re,Complex.star_def,Complex.conj_re]
    norm_num
    linarith [coordinate.rightHalf]
  exact sub_eq_zero.mp (homogeneous_L2_unique _ positive _ homogeneous)

private theorem forcing1_corrected_gap (coordinate : BurnolCompletedMellinCoordinate) :
    burnolQuarterRestriction (regularForcing coordinate 1-endpointCorrectedForcing coordinate) =
      (constantFourierRaw q*(sourceRate coordinate+1/2)-rho) • intervalConstant q := by
  rw [map_sub,forcing1_quarter_restriction,endpointCorrectedForcing_state]
  have eta := Constructor.zeroMean_read (Constructor.compact (Edge.raw q) (Edge.raw_continuous q))
  rw [Edge.zeroMean_raw_eq_endpointColumns] at eta
  change (Response.eta : BurnolQuarterIntervalL2) = _ at eta
  rw [eta]
  module

private theorem coordinate_star_nonzero (coordinate : BurnolCompletedMellinCoordinate) : star coordinate.value ≠ 0 := by
  intro zero
  have realZero := congrArg Complex.re zero
  simp only [Complex.star_def,Complex.conj_re,Complex.zero_re] at realZero
  linarith [coordinate.rightHalf]

/-- The actual second R input is split only by a genuine compact L² forcing and a source-certified constant gap. -/
theorem regular1_quarter (coordinate : BurnolCompletedMellinCoordinate) :
    burnolQuarterRestriction (regularColumns coordinate 1) =
      burnolTruncatedFourier (intervalConstant q) - (rho/star coordinate.value) • intervalConstant q := by
  have right : 1/4 < (star coordinate.value/2).re := by
    rw [Complex.div_re];norm_num;linarith [coordinate.rightHalf]
  have difference := right_resolvent_quarter_constant (star coordinate.value/2) right
    (regularForcing coordinate 1-endpointCorrectedForcing coordinate)
    (constantFourierRaw q*(sourceRate coordinate+1/2)-rho) (forcing1_corrected_gap coordinate)
  rw [burnolDirectRightResolvent_sub _ right,map_sub] at difference
  have generated := congrArg burnolQuarterRestriction (endpointCorrected_resolvent coordinate)
  simp only [map_smul] at generated
  have regular := congrArg (fun value : BurnolQuarterIntervalL2 => -(1/2 : ℂ) • value) difference
  simp only [smul_sub,smul_smul] at regular
  change -(1/2 : ℂ) • burnolQuarterRestriction (sourceResolvent coordinate (regularForcing coordinate 1)) -
    -(1/2 : ℂ) • burnolQuarterRestriction (sourceResolvent coordinate (endpointCorrectedForcing coordinate)) = _ at regular
  rw [generated] at regular
  change -(1/2 : ℂ) • burnolQuarterRestriction (sourceResolvent coordinate (regularForcing coordinate 1)) -
    burnolQuarterRestriction (burnolQuarterZeroExtension endpointCorrectedConstantState) = _ at regular
  rw [burnolQuarterRestriction_zeroExtension] at regular
  have coefficient : (-(1/2 : ℂ))*(-(constantFourierRaw q*(sourceRate coordinate+1/2)-rho)/(star coordinate.value/2)) =
      constantFourierRaw q-rho/star coordinate.value := by
    have rate : sourceRate coordinate+1/2 = star coordinate.value := by unfold sourceRate;ring
    rw [rate]
    calc
      _ = constantFourierRaw q*(star coordinate.value*(star coordinate.value)⁻¹)-rho/star coordinate.value := by ring
      _ = _ := by rw [mul_inv_cancel₀ (coordinate_star_nonzero coordinate),mul_one]
  rw [coefficient] at regular
  change burnolQuarterRestriction (-(1/2 : ℂ) • sourceResolvent coordinate (regularForcing coordinate 1)) = _
  rw [map_smul]
  unfold endpointCorrectedConstantState at regular
  linear_combination (norm := module) regular

theorem sourceY1_quarter (coordinate : BurnolCompletedMellinCoordinate) :
    burnolQuarterRestriction (sourceY1 coordinate) = -(rho/star coordinate.value) • intervalConstant q := by
  have born := sourceColumns_from_regular_resolvent coordinate 1
  change sourceY1 coordinate = regularColumns coordinate 1 + -fourierL2 ConstantDual.seed at born
  rw [born,map_add,map_neg,regular1_quarter]
  change burnolTruncatedFourier (intervalConstant q)-(rho/star coordinate.value) • intervalConstant q +
    -burnolTruncatedFourier (intervalConstant q) = _
  module

theorem sourceY0_quarter (coordinate : BurnolCompletedMellinCoordinate) :
    burnolQuarterRestriction (sourceY0 coordinate) = ((mu+1)/star coordinate.value) • intervalConstant q := by
  have born := sourceColumns_from_regular_resolvent coordinate 0
  change sourceY0 coordinate = regularColumns coordinate 0+ConstantDual.seed at born
  rw [born,map_add,regular0_quarter]
  change ((mu+1/2-sourceRate coordinate)/star coordinate.value) • intervalConstant q +
    burnolQuarterRestriction (burnolQuarterZeroExtension (intervalConstant q)) = _
  rw [burnolQuarterRestriction_zeroExtension]
  have coefficient : (mu+1/2-sourceRate coordinate)/star coordinate.value+1 = (mu+1)/star coordinate.value := by
    calc
      _ = (mu+1)/star coordinate.value-star coordinate.value*(star coordinate.value)⁻¹+1 := by unfold sourceRate;ring
      _ = _ := by rw [mul_inv_cancel₀ (coordinate_star_nonzero coordinate)];ring
  rw [← coefficient]
  module

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKForcingGapAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
