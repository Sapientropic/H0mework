import H0mework.NavierStokes.NativeAction.Operator
import H0mework.NavierStokes.UnifiedAction.UnifiedHeatAction
import H0mework.NavierStokes.StressAction.StressDynamicsBilinear
import Mathlib.MeasureTheory.Group.Measure

set_option autoImplicit false
open scoped Topology ENNReal NNReal
namespace SaturationMonoid.NavierStokes.NativeCompleteHeatTransport
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinMildDuhamel
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteMildDuhamel
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelKineticTriadRedirect
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open SourceGeneratedNativeResponseDisposition NativeCompleteStressAction NativeEndpointVelocityCarrier
open NativeUnifiedHeatAction NativeTimeJetCarrier
noncomputable section

def tensorHeat (nu : Viscosity) (lag : ℝ≥0) : NativeCompleteStressCarrier.Space →L[ℝ] NativeCompleteStressCarrier.Space :=
  lp.mapCLM 2 (fun wave : IntegerWavevector =>
    finiteStateVorticityHeatMultiplier nu.coeff lag wave • ContinuousLinearMap.id ℝ NativeCompleteStressCarrier.Tensor)
    (show (0 : ℝ) ≤ 1 from zero_le_one) (fun wave => by
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro value
      change ‖finiteStateVorticityHeatMultiplier nu.coeff lag wave • value‖ ≤ 1 * ‖value‖
      rw [one_mul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (finiteStateVorticityHeatMultiplier_nonneg _ _ _)]
      exact mul_le_of_le_one_left (norm_nonneg _)
        (finiteStateVorticityHeatMultiplier_le_one nu.coeff_pos.le lag.2 wave))

theorem tensorHeat_row (nu : Viscosity) (lag : ℝ≥0) (value : NativeCompleteStressCarrier.Space)
    (wave : IntegerWavevector) :
    tensorHeat nu lag value wave = finiteStateVorticityHeatMultiplier nu.coeff lag wave • value wave := rfl

theorem tensorHeat_read (nu : Viscosity) (lag : ℝ≥0) (value : NativeCompleteStressCarrier.Space)
    (wave : IntegerWavevector) :
    NativeCompleteStressCarrier.read (tensorHeat nu lag value) wave =
      finiteStateVorticityHeatMultiplier nu.coeff lag wave • NativeCompleteStressCarrier.read value wave := by
  funext output input
  change (NativeCompleteStressCarrier.weight wave)⁻¹ • (tensorHeat nu lag value wave) (output,input) =
    finiteStateVorticityHeatMultiplier nu.coeff lag wave •
      ((NativeCompleteStressCarrier.weight wave)⁻¹ • value wave (output,input))
  rw [tensorHeat_row, PiLp.smul_apply]
  exact smul_comm _ _ _

def fullHeat (nu : Viscosity) (lag : ℝ≥0) (value : FullSpace) : FullSpace :=
  WithLp.toLp 2 (heatCLM nu lag value.fst, tensorHeat nu lag value.snd)

def fullHeatCLM (nu : Viscosity) (lag : ℝ≥0) : FullSpace →L[ℝ] FullSpace :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ WholeRestartVelocityEndpointState NativeCompleteStressCarrier.Space).symm.toContinuousLinearMap.comp
    (((heatCLM nu lag).prodMap (tensorHeat nu lag)).comp
      (WithLp.prodContinuousLinearEquiv 2 ℝ WholeRestartVelocityEndpointState NativeCompleteStressCarrier.Space).toContinuousLinearMap)

theorem fullHeatCLM_apply (nu : Viscosity) (lag : ℝ≥0) (value : FullSpace) :
    fullHeatCLM nu lag value = fullHeat nu lag value := rfl

theorem tensorHeat_bound (nu : Viscosity) (lag : ℝ≥0) (value : NativeCompleteStressCarrier.Space) :
    ‖tensorHeat nu lag value‖ ≤ ‖value‖ := by
  apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  intro wave
  rw [tensorHeat_row, norm_smul, Real.norm_of_nonneg (finiteStateVorticityHeatMultiplier_nonneg _ _ _)]
  exact mul_le_of_le_one_left (norm_nonneg _) (finiteStateVorticityHeatMultiplier_le_one nu.coeff_pos.le lag.2 wave)

theorem fullHeat_bound (nu : Viscosity) (lag : ℝ≥0) (value : FullSpace) :
    ‖fullHeatCLM nu lag value‖ ≤ ‖value‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [fullHeatCLM_apply, fullHeat, WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2]
  exact add_le_add (pow_le_pow_left₀ (norm_nonneg _) (heat_bound nu lag value.fst) 2)
    (pow_le_pow_left₀ (norm_nonneg _) (tensorHeat_bound nu lag value.snd) 2)

theorem velocity_heat (nu : Viscosity) (lag : ℝ≥0) (value : WholeRestartVelocityEndpointState)
    (wave : IntegerWavevector) :
    wholeVelocity (heatCLM nu lag value) wave = finiteStateVorticityHeatMultiplier nu.coeff lag wave • wholeVelocity value wave := by
  by_cases zero : wave = 0
  · subst wave
    simp
  · funext coordinate
    rw [Pi.smul_apply, wholeVelocity_nonzero _ ⟨wave,zero⟩, wholeVelocity_nonzero _ ⟨wave,zero⟩,
      heatCLM_row, PiLp.smul_apply]

theorem momentum_row (nu : Viscosity) (lag : ℝ≥0) (value : FullSpace) (wave : IntegerWavevector) :
    NativeCompleteAction.momentum nu (fullHeat nu lag value) wave =
      finiteStateVorticityHeatMultiplier nu.coeff lag wave • NativeCompleteAction.momentum nu value wave := by
  change projectedDivergenceCLM wave (NativeCompleteStressCarrier.read (tensorHeat nu lag value.snd) wave) -
    (nu.coeff * integerWaveViscousMultiplier wave) • wholeVelocity (heatCLM nu lag value.fst) wave = _
  rw [tensorHeat_read, velocity_heat, map_smul, smul_comm (nu.coeff * integerWaveViscousMultiplier wave), ← smul_sub]
  rfl

theorem momentum_heat (nu : Viscosity) (lag : ℝ≥0) (value : FullSpace) :
    momentumCLM nu (fullHeat nu lag value) = heatCLM nu lag (momentumCLM nu value) := by
  apply lp.ext
  funext wave
  rw [NativeCompleteActionOperator.momentum_complete_row, momentum_row, map_smul,
    heatCLM_row, NativeCompleteActionOperator.momentum_complete_row]

theorem nativeRHS_heat (nu : Viscosity) (lag : ℝ≥0) (frequencies : Finset IntegerWavevector)
    (value : FullSpace) (wave : IntegerWavevector) :
    NativeCompleteEvolution.nativeRHS nu frequencies (fullHeat nu lag value) wave =
      finiteStateVorticityHeatMultiplier nu.coeff lag wave • NativeCompleteEvolution.nativeRHS nu frequencies value wave := by
  simp only [NativeCompleteActionOperator.nativeRHS_eq_actionCLM, NativeCompleteActionOperator.actionCLM,
    ContinuousLinearMap.comp_apply]
  rw [momentum_heat, NativeCompleteFilteredWrite.readCLM_apply, NativeCompleteFilteredWrite.readCLM_apply]
  by_cases included : wave ∈ frequencies
  · simp only [if_pos included, NativeCompleteFilteredWrite.curlRowCLM_apply, velocity_heat]
    rw [smul_comm (integerWaveNormSq wave ^ 2)]
    exact ((fourierCurlCoefficientContinuousLinearMap wave).restrictScalars ℝ).map_smul _ _
  · simp [included]

def residualValue (value : FullSpace) : NativeCompleteStressCarrier.Space :=
  value.snd - NativeCompleteStressBilinear.mixed (wholeVelocity value.fst) (wholeVelocity value.fst)

theorem heat_residual_split (nu : Viscosity) (lag : ℝ≥0) (value : FullSpace) :
    residualValue (fullHeat nu lag value) = tensorHeat nu lag (residualValue value) +
      (tensorHeat nu lag (NativeCompleteStressBilinear.mixed (wholeVelocity value.fst) (wholeVelocity value.fst)) -
        NativeCompleteStressBilinear.mixed (wholeVelocity (heatCLM nu lag value.fst))
          (wholeVelocity (heatCLM nu lag value.fst))) := by
  simp only [residualValue, map_sub]
  abel

end
end SaturationMonoid.NavierStokes.NativeCompleteHeatTransport
