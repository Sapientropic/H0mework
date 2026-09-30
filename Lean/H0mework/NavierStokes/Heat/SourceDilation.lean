import H0mework.NavierStokes.Heat.PulseDilation
import H0mework.NavierStokes.UnifiedAction.UnifiedHeatAction

set_option autoImplicit false
open scoped BigOperators Topology ENNReal NNReal

namespace SaturationMonoid.NavierStokes.NativeHeatSourceDilation

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientFiniteGalerkinMildDuhamel

noncomputable section

private def mapField {Index : Type*} {E F : Index → Type*}
    [∀ index, NormedAddCommGroup (E index)] [∀ index, NormedSpace ℂ (E index)]
    [∀ index, NormedAddCommGroup (F index)] [∀ index, NormedSpace ℂ (F index)]
    (action : ∀ index, E index →ₗᵢ[ℂ] F index) (value : lp E 2) : lp F 2 :=
  ⟨fun index => action index (value index), by
    apply memℓp_gen
    simpa only [LinearIsometry.norm_map] using
      (lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) value).summable⟩

private def mapIsometry {Index : Type*} {E F : Index → Type*}
    [∀ index, NormedAddCommGroup (E index)] [∀ index, NormedSpace ℂ (E index)]
    [∀ index, NormedAddCommGroup (F index)] [∀ index, NormedSpace ℂ (F index)]
    (action : ∀ index, E index →ₗᵢ[ℂ] F index) : lp E 2 →ₗᵢ[ℂ] lp F 2 where
  toFun := mapField action
  map_add' first last := by
    apply lp.ext
    funext index
    exact (action index).map_add _ _
  map_smul' scalar value := by
    apply lp.ext
    funext index
    exact (action index).map_smul scalar _
  norm_map' value := by
    have forward : ‖mapField action value‖ ≤ ‖value‖ :=
      lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0) (fun index => (action index).norm_map (value index) |>.le)
    have backward : ‖value‖ ≤ ‖mapField action value‖ :=
      lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0) (fun index => (action index).norm_map (value index) |>.ge)
    exact le_antisymm forward backward

abbrev Fiber := NativeTemporalActionCompression.Ambient ComplexCoordinateEuclidean
abbrev Ambient := lp (fun _ : NonzeroIntegerWavevector => Fiber) 2

def rate (nu : Viscosity) (wave : NonzeroIntegerWavevector) : ℝ :=
  nu.coeff * integerWaveViscousMultiplier wave.1

theorem rate_pos (nu : Viscosity) (wave : NonzeroIntegerWavevector) : 0 < rate nu wave := by
  have positive := integerWaveNormSq_pos wave.2
  have viscosity := nu.coeff_pos
  unfold rate integerWaveViscousMultiplier
  positivity

/-- Every rate is read from the original viscous Fourier generator. -/
def embed (nu : Viscosity) : WholeRestartVelocityEndpointState →ₗᵢ[ℂ] Ambient :=
  mapIsometry fun wave => NativeHeatPulseDilation.embed (E := ComplexCoordinateEuclidean)
    (rate nu wave) (rate_pos nu wave)

def translation (time : ℝ) : Ambient →ₗᵢ[ℂ] Ambient :=
  mapIsometry fun _ => NativeTemporalActionCompression.translation ComplexCoordinateEuclidean time

theorem translation_inverse (time : ℝ) (value : Ambient) :
    translation (-time) (translation time value) = value := by
  apply lp.ext
  funext wave
  exact NativeHeatPulseDilation.translation_inverse time (value wave)

def unitary (time : ℝ) : Ambient ≃ₗᵢ[ℂ] Ambient :=
  LinearIsometryEquiv.ofLinearIsometry (translation time) (translation (-time)).toLinearMap
    (by
      apply LinearMap.ext
      intro value
      change translation time (translation (-time) value) = value
      simpa only [neg_neg] using translation_inverse (-time) value)
    (by
      apply LinearMap.ext
      intro value
      exact translation_inverse time value)

def read (nu : Viscosity) : Ambient →L[ℂ] WholeRestartVelocityEndpointState :=
  (embed nu).toContinuousLinearMap.adjoint

theorem read_embed (nu : Viscosity) (value : WholeRestartVelocityEndpointState) : read nu (embed nu value) = value := by
  apply ext_inner_left ℂ
  intro test
  rw [read, ContinuousLinearMap.adjoint_inner_right]
  exact (embed nu).inner_map_map test value

theorem read_norm_le (nu : Viscosity) (value : Ambient) : ‖read nu value‖ ≤ ‖value‖ := by
  have normEq : ‖read nu‖ = ‖(embed nu).toContinuousLinearMap‖ :=
    ContinuousLinearMap.adjoint.norm_map ((embed nu).toContinuousLinearMap)
  have operatorBound : ‖read nu‖ ≤ 1 :=
    normEq.trans_le (embed nu).norm_toContinuousLinearMap_le
  simpa only [one_mul] using ((read nu).le_opNorm value).trans
    (mul_le_mul_of_nonneg_right operatorBound (norm_nonneg value))

/-- The whole original heat action is a bounded readout of one physical-time translation. -/
theorem read_translation (nu : Viscosity) (time : ℝ≥0) (value : WholeRestartVelocityEndpointState) :
    read nu (translation time (embed nu value)) = NativeUnifiedHeatAction.heatCLM nu time value := by
  apply ext_inner_left ℂ
  intro test
  rw [read, ContinuousLinearMap.adjoint_inner_right, lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro wave
  change inner ℂ (NativeHeatPulseDilation.embed (rate nu wave) (rate_pos nu wave) (test wave))
    (NativeTemporalActionCompression.translation ComplexCoordinateEuclidean time
      (NativeHeatPulseDilation.embed (rate nu wave) (rate_pos nu wave) (value wave))) = _
  have adjointPair := ContinuousLinearMap.adjoint_inner_right
    (NativeHeatPulseDilation.embed (E := ComplexCoordinateEuclidean)
      (rate nu wave) (rate_pos nu wave)).toContinuousLinearMap (test wave)
    (NativeTemporalActionCompression.translation ComplexCoordinateEuclidean time
      (NativeHeatPulseDilation.embed (rate nu wave) (rate_pos nu wave) (value wave)))
  change inner ℂ (test wave) (NativeHeatPulseDilation.read (rate nu wave) (rate_pos nu wave)
    (NativeTemporalActionCompression.translation ComplexCoordinateEuclidean time
      (NativeHeatPulseDilation.embed (rate nu wave) (rate_pos nu wave) (value wave)))) = _ at adjointPair
  refine adjointPair.symm.trans ?_
  apply congrArg (inner ℂ (test wave))
  exact (NativeHeatPulseDilation.read_translation (rate nu wave) (rate_pos nu wave) time time.2
    (value wave)).trans (NativeUnifiedHeatAction.heatCLM_row nu time value wave).symm

end
end SaturationMonoid.NavierStokes.NativeHeatSourceDilation
