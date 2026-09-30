import H0mework.NavierStokes.UnifiedAction.UnifiedCompleteSource
import Mathlib.Analysis.SpecialFunctions.Exponential

set_option autoImplicit false
open scoped Topology ENNReal NNReal

namespace SaturationMonoid.NavierStokes.NativeUnifiedHeatAction

open Set Filter
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientFiniteGalerkinMildDuhamel
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteMildDuhamel
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent

noncomputable section

abbrev RowEnd := ComplexCoordinateEuclidean →L[ℝ] ComplexCoordinateEuclidean

local instance : NormedAlgebra ℚ RowEnd := NormedAlgebra.restrictScalars ℚ ℝ _

def rowGenerator (nu : Viscosity) (wave : IntegerWavevector) : RowEnd :=
  -(nu.coeff * integerWaveViscousMultiplier wave) • 1

def rowEvolution (nu : Viscosity) (wave : IntegerWavevector) (time : ℝ) : RowEnd :=
  NormedSpace.exp (time • rowGenerator nu wave)

theorem rowEvolution_scalar (nu : Viscosity) (wave : IntegerWavevector) (time : ℝ) :
    rowEvolution nu wave time = finiteStateVorticityHeatMultiplier nu.coeff time wave • (1 : RowEnd) := by
  have natural := NormedSpace.map_exp (algebraMap ℝ RowEnd) (continuous_algebraMap ℝ RowEnd)
    (-(nu.coeff * integerWaveViscousMultiplier wave) * time)
  rw [← Real.exp_eq_exp_ℝ] at natural
  simpa only [rowEvolution, rowGenerator, finiteStateVorticityHeatMultiplier,
    Algebra.algebraMap_eq_smul_one, smul_smul, mul_comm] using natural.symm

theorem rowEvolution_hasDerivAt (nu : Viscosity) (wave : IntegerWavevector) (time : ℝ) :
    HasDerivAt (rowEvolution nu wave) (rowEvolution nu wave time * rowGenerator nu wave) time := by
  exact hasDerivAt_exp_smul_const (𝕂 := ℝ) (rowGenerator nu wave) time

theorem rowEvolution_bound (nu : Viscosity) (time : ℝ≥0) (wave : IntegerWavevector)
    (value : ComplexCoordinateEuclidean) : ‖rowEvolution nu wave time value‖ ≤ ‖value‖ := by
  rw [rowEvolution_scalar]
  change ‖finiteStateVorticityHeatMultiplier nu.coeff time wave • value‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (finiteStateVorticityHeatMultiplier_nonneg _ _ _)]
  exact mul_le_of_le_one_left (norm_nonneg _) (finiteStateVorticityHeatMultiplier_le_one nu.coeff_pos.le time.2 wave)

def heat (nu : Viscosity) (time : ℝ≥0) (value : WholeRestartVelocityEndpointState) : WholeRestartVelocityEndpointState :=
  ⟨fun wave => rowEvolution nu wave.1 time (value wave), by
    apply memℓp_gen
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    have original : Summable fun wave => ‖value wave‖ ^ 2 := by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
        (lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) value).summable
    exact original.of_nonneg_of_le (fun _ => sq_nonneg _) fun wave =>
      pow_le_pow_left₀ (norm_nonneg _) (rowEvolution_bound nu time wave.1 (value wave)) 2⟩

theorem heat_bound (nu : Viscosity) (time : ℝ≥0) (value : WholeRestartVelocityEndpointState) :
    ‖heat nu time value‖ ≤ ‖value‖ := by
  apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  intro wave
  exact rowEvolution_bound nu time wave.1 (value wave)

def heatCLM (nu : Viscosity) (time : ℝ≥0) : WholeRestartVelocityEndpointState →L[ℝ] WholeRestartVelocityEndpointState :=
  LinearMap.mkContinuous
    { toFun := heat nu time
      map_add' := fun first last => by
        apply lp.ext
        funext wave
        exact (rowEvolution nu wave.1 time).map_add _ _
      map_smul' := fun scalar value => by
        apply lp.ext
        funext wave
        exact (rowEvolution nu wave.1 time).map_smul scalar _ }
    1 (fun value => by
      change ‖heat nu time value‖ ≤ 1 * ‖value‖
      simpa only [one_mul] using heat_bound nu time value)

theorem heatCLM_row (nu : Viscosity) (time : ℝ≥0) (value : WholeRestartVelocityEndpointState)
    (wave : NonzeroIntegerWavevector) :
    heatCLM nu time value wave = finiteStateVorticityHeatMultiplier nu.coeff time wave.1 • value wave := by
  change rowEvolution nu wave.1 time (value wave) = _
  rw [rowEvolution_scalar]
  rfl

theorem heatCLM_zero (nu : Viscosity) : heatCLM nu 0 = ContinuousLinearMap.id ℝ _ := by
  apply ContinuousLinearMap.ext
  intro value
  apply lp.ext
  funext wave
  rw [heatCLM_row]
  simp [finiteStateVorticityHeatMultiplier]

theorem heatCLM_add (nu : Viscosity) (first last : ℝ≥0) :
    heatCLM nu (first + last) = (heatCLM nu last).comp (heatCLM nu first) := by
  apply ContinuousLinearMap.ext
  intro value
  apply lp.ext
  funext wave
  change heatCLM nu (first + last) value wave = heatCLM nu last (heatCLM nu first value) wave
  rw [heatCLM_row, heatCLM_row, heatCLM_row]
  simp only [NNReal.coe_add, finiteStateVorticityHeatMultiplier]
  rw [smul_smul, ← Real.exp_add]
  congr 1
  congr 1
  ring

theorem heatCLM_embed (nu : Viscosity) (time : ℝ≥0) (value : WholeRestartVelocityEndpointState) :
    heatCLM nu time (NativeNegativeFourMomentum.embed value) =
      NativeNegativeFourMomentum.embed (heatCLM nu time value) := by
  apply lp.ext
  funext wave
  rw [heatCLM_row, NativeNegativeFourMomentum.embed_apply, NativeNegativeFourMomentum.embed_apply, heatCLM_row]
  exact smul_comm _ _ _

end
end SaturationMonoid.NavierStokes.NativeUnifiedHeatAction
