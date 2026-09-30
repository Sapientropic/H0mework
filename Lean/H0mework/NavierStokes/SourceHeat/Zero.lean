import H0mework.NavierStokes.WindowPhysics.HeatEvolution
import H0mework.NavierStokes.StressDynamics.Cofinal
import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.MetricSpace.UniformConvergence

set_option autoImplicit false
open scoped Topology ENNReal NNReal
namespace SaturationMonoid.NavierStokes.NativeZeroHeat
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinMildDuhamel
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteMildDuhamel
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open NativeCompleteStressAction NativeCompleteHeatTransport NativeUnifiedHeatAction NativeEndpointVelocityCarrier
noncomputable section

theorem tensorHeat_zero (nu : Viscosity) : tensorHeat nu 0 = ContinuousLinearMap.id ℝ _ := by
  ext value wave entry
  simp [tensorHeat_row, finiteStateVorticityHeatMultiplier]

theorem fullHeat_zero (nu : Viscosity) : fullHeatCLM nu 0 = ContinuousLinearMap.id ℝ FullSpace := by
  apply ContinuousLinearMap.ext
  intro value
  simp only [fullHeatCLM_apply, fullHeat, heatCLM_zero, tensorHeat_zero, ContinuousLinearMap.id_apply]
  exact WithLp.toLp_ofLp 2 value

theorem multiplier_continuous (nu : Viscosity) (wave : IntegerWavevector) :
    Continuous (fun lag : ℝ≥0 => finiteStateVorticityHeatMultiplier nu.coeff lag wave) := by
  unfold finiteStateVorticityHeatMultiplier
  fun_prop

theorem velocity_continuous (nu : Viscosity) (value : WholeRestartVelocityEndpointState) :
    Continuous (fun lag : ℝ≥0 => heatCLM nu lag value) := by
  apply continuous_iff_seqContinuous.mpr
  intro sequence lag convergence
  have summable : Summable (fun wave => ‖value wave‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) value).summable
  apply NativeCompleteStressCofinal.lp_tendsto_of_sq_bound _ _ summable
  · intro index wave
    change ‖heatCLM nu (sequence index) value wave‖ ^ 2 ≤ ‖value wave‖ ^ 2
    rw [heatCLM_row, norm_smul, Real.norm_of_nonneg (finiteStateVorticityHeatMultiplier_nonneg _ _ _)]
    exact pow_le_pow_left₀ (mul_nonneg (finiteStateVorticityHeatMultiplier_nonneg _ _ _) (norm_nonneg _))
      (mul_le_of_le_one_left (norm_nonneg _) (finiteStateVorticityHeatMultiplier_le_one nu.coeff_pos.le (sequence index).2 wave.1)) 2
  · intro wave
    have row := ((multiplier_continuous nu wave.1).smul (continuous_const (y := value wave))).tendsto lag |>.comp convergence
    simpa only [Function.comp_def, heatCLM_row] using! row

theorem tensor_continuous (nu : Viscosity) (value : NativeCompleteStressCarrier.Space) :
    Continuous (fun lag : ℝ≥0 => tensorHeat nu lag value) := by
  apply continuous_iff_seqContinuous.mpr
  intro sequence lag convergence
  have summable : Summable (fun wave => ‖value wave‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) value).summable
  apply NativeCompleteStressCofinal.lp_tendsto_of_sq_bound _ _ summable
  · intro index wave
    change ‖tensorHeat nu (sequence index) value wave‖ ^ 2 ≤ ‖value wave‖ ^ 2
    rw [tensorHeat_row, norm_smul, Real.norm_of_nonneg (finiteStateVorticityHeatMultiplier_nonneg _ _ _)]
    exact pow_le_pow_left₀ (mul_nonneg (finiteStateVorticityHeatMultiplier_nonneg _ _ _) (norm_nonneg _))
      (mul_le_of_le_one_left (norm_nonneg _) (finiteStateVorticityHeatMultiplier_le_one nu.coeff_pos.le (sequence index).2 wave)) 2
  · intro wave
    have row := ((multiplier_continuous nu wave).smul (continuous_const (y := value wave))).tendsto lag |>.comp convergence
    simpa only [Function.comp_def, tensorHeat_row] using! row

theorem fullHeat_continuous (nu : Viscosity) (value : FullSpace) :
    Continuous (fun lag : ℝ≥0 => fullHeatCLM nu lag value) := by
  exact (WithLp.prodContinuousLinearEquiv 2 ℝ WholeRestartVelocityEndpointState NativeCompleteStressCarrier.Space).symm.continuous.comp
    ((velocity_continuous nu value.fst).prodMk (tensor_continuous nu value.snd))

theorem fullHeat_tendsto (nu : Viscosity) (value : FullSpace) :
    Tendsto (fun lag : ℝ≥0 => fullHeatCLM nu lag value) (𝓝 0) (𝓝 value) := by
  simpa only [fullHeat_zero, ContinuousLinearMap.id_apply] using (fullHeat_continuous nu value).tendsto 0

theorem fullHeat_uniform_on_compact (nu : Viscosity) {domain : Set FullSpace} (compact : IsCompact domain) :
    TendstoUniformlyOn (fun lag : ℝ≥0 => fullHeatCLM nu lag) id (𝓝 0) domain := by
  let : CompactSpace domain := isCompact_iff_compactSpace.mp compact
  have contractive (lag : ℝ≥0) : LipschitzWith 1 (fun value : domain => fullHeatCLM nu lag value.1) := by
    apply LipschitzWith.mk_one
    intro first last
    change dist (fullHeatCLM nu lag first.1) (fullHeatCLM nu lag last.1) ≤ dist first.1 last.1
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    exact fullHeat_bound nu lag _
  have equicontinuous := (LipschitzWith.uniformEquicontinuous
    (fun lag : ℝ≥0 => fun value : domain => fullHeatCLM nu lag value.1) 1 contractive).equicontinuous
  have pointwise : Tendsto (fun lag : ℝ≥0 => fun value : domain => fullHeatCLM nu lag value.1)
      (𝓝 0) (𝓝 (fun value : domain => value.1)) :=
    tendsto_pi_nhds.mpr (fun value => fullHeat_tendsto nu value.1)
  rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
  exact UniformFun.tendsto_iff_tendstoUniformly.mp
    ((equicontinuous.tendsto_uniformFun_iff_pi (𝓝 (0 : ℝ≥0)) (fun value : domain => value.1)).mpr pointwise)

theorem residual_continuous : Continuous residualValue := by
  let pair := WithLp.prodContinuousLinearEquiv 2 ℝ WholeRestartVelocityEndpointState NativeCompleteStressCarrier.Space
  exact pair.continuous.snd.sub (NativeCompleteStressCofinal.quadratic_continuous.comp pair.continuous.fst)

theorem residual_tendsto (nu : Viscosity) (value : FullSpace) :
    Tendsto (fun lag : ℝ≥0 => residualValue (fullHeatCLM nu lag value)) (𝓝 0) (𝓝 (residualValue value)) :=
  residual_continuous.continuousAt.tendsto.comp (fullHeat_tendsto nu value)

theorem momentum_tendsto (nu : Viscosity) (value : FullSpace) :
    Tendsto (fun lag : ℝ≥0 => momentumCLM nu (fullHeatCLM nu lag value)) (𝓝 0) (𝓝 (momentumCLM nu value)) :=
  (momentumCLM nu).continuous.continuousAt.tendsto.comp (fullHeat_tendsto nu value)

end
end SaturationMonoid.NavierStokes.NativeZeroHeat
