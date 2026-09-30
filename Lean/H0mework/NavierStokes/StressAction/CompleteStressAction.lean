import H0mework.NavierStokes.StressAction.CompleteStressCarrier
import Mathlib.Analysis.InnerProductSpace.ProdL2

set_option autoImplicit false
open scoped BigOperators Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeCompleteStressAction

open Set Filter
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinFiniteObservationTimeTightness
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open NativeCompleteStressCarrier NativeFullOrderStress NativeTimeJetCarrier NativeEndpointVelocityCarrier

noncomputable section

def untensorCLM : Tensor →L[ℝ] NativeFluidStressCoefficient :=
  ContinuousLinearMap.pi fun output => ContinuousLinearMap.pi fun input =>
    (ContinuousLinearMap.proj (output, input)).comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Coordinate × Coordinate => ℂ)).toContinuousLinearMap

def euclideanCLM : ComplexCoordinateVector →L[ℝ] ComplexCoordinateEuclidean :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Coordinate => ℂ)).symm.toContinuousLinearMap

def rowCLM (wave : NonzeroIntegerWavevector) : Tensor →L[ℝ] ComplexCoordinateEuclidean :=
  (integerWaveNormSq wave.1)⁻¹ • (euclideanCLM.comp ((projectedDivergenceCLM wave.1).comp untensorCLM))

theorem rowCLM_bound (wave : NonzeroIntegerWavevector) (value : Tensor) :
    ‖rowCLM wave value‖ ≤ (2 * Real.pi) * ‖value‖ := by
  have original := (transverseProjection_amplitudeSq_le wave.1 wave.2
    (nativeFluidStressDivergenceCoefficient (fun _ => untensor value) wave.1)).trans
      (divergence_amplitude_le (fun _ => untensor value) wave.1)
  have tensorSquare : (∑ output : Coordinate, ∑ input : Coordinate,
      Complex.normSq (untensor value output input)) = ‖value‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, Fintype.sum_prod_type]
    simp only [untensor, Complex.normSq_eq_norm_sq]
  rw [tensorSquare] at original
  have scalarNonnegative := inv_nonneg.mpr (integerWaveNormSq_nonneg wave.1)
  have scale : (integerWaveNormSq wave.1)⁻¹ ^ 2 * integerWaveViscousMultiplier wave.1 =
      (2 * Real.pi) ^ 2 * (integerWaveNormSq wave.1)⁻¹ := by
    unfold integerWaveViscousMultiplier
    field_simp
  have scaled := mul_le_mul_of_nonneg_left original (sq_nonneg ((integerWaveNormSq wave.1)⁻¹))
  have inverseBound := inv_le_one_of_one_le₀ (one_le_integerWaveNormSq wave.1 wave.2)
  have ceiling := mul_le_mul_of_nonneg_left inverseBound (sq_nonneg (2 * Real.pi))
  have ceiling' := mul_le_mul_of_nonneg_right ceiling (sq_nonneg ‖value‖)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by positivity) (norm_nonneg _))).mp
  change ‖(integerWaveNormSq wave.1)⁻¹ • euclideanCoordinateRow
    (transverseProjection wave.1 (nativeFluidStressDivergenceCoefficient (fun _ => untensor value) wave.1))‖ ^ 2 ≤ _
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg scalarNonnegative, mul_pow, euclideanCoordinateRow_norm_sq]
  apply scaled.trans
  rw [← mul_assoc, scale]
  simpa only [mul_one, mul_pow] using ceiling'

def divergence (value : Space) : WholeRestartVelocityEndpointState :=
  ⟨fun wave => rowCLM wave (value wave.1), by
    apply memℓp_gen
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    have source : Summable fun wave => ‖value wave‖ ^ 2 := by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
        (lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) value).summable
    exact ((source.subtype (fun wave => wave ≠ 0)).mul_left ((2 * Real.pi) ^ 2)).of_nonneg_of_le
      (fun _ => sq_nonneg _) (fun wave => by
        simpa only [mul_pow, Function.comp_def] using
          pow_le_pow_left₀ (norm_nonneg _) (rowCLM_bound wave (value wave.1)) 2)⟩

theorem divergence_bound (value : Space) : ‖divergence value‖ ≤ (2 * Real.pi) * ‖value‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by positivity) (norm_nonneg _))).mp
  have source := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) value
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at source
  have target := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num) (divergence value)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at target
  rw [target, mul_pow]
  calc
    _ ≤ ∑' wave : NonzeroIntegerWavevector, (2 * Real.pi) ^ 2 * ‖value wave.1‖ ^ 2 := by
      have targetSummable : Summable (fun wave => ‖divergence value wave‖ ^ 2) := by
        simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
          (lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) (divergence value)).summable
      have boundSummable : Summable (fun wave : NonzeroIntegerWavevector =>
          (2 * Real.pi) ^ 2 * ‖value wave.1‖ ^ 2) := by
        convert! (source.summable.subtype (fun wave => wave ≠ 0)).mul_left ((2 * Real.pi) ^ 2) using 1
      exact Summable.tsum_le_tsum
        (fun wave => by
          change ‖rowCLM wave (value wave.1)‖ ^ 2 ≤ _
          simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (rowCLM_bound wave (value wave.1)) 2)
        targetSummable boundSummable
    _ = (2 * Real.pi) ^ 2 * ∑' wave : NonzeroIntegerWavevector, ‖value wave.1‖ ^ 2 := tsum_mul_left
    _ ≤ (2 * Real.pi) ^ 2 * ‖value‖ ^ 2 := by
      rw [← source.tsum_eq]
      exact mul_le_mul_of_nonneg_left
        (source.summable.tsum_subtype_le _ {wave | wave ≠ 0} (fun _ => sq_nonneg _)) (sq_nonneg _)

/-- The original stress action is a bounded map of the whole tensor carrier. -/
def divergenceCLM : Space →L[ℝ] WholeRestartVelocityEndpointState :=
  LinearMap.mkContinuous
    { toFun := divergence
      map_add' := fun first last => by
        apply lp.ext
        funext wave
        exact (rowCLM wave).map_add _ _
      map_smul' := fun scalar value => by
        apply lp.ext
        funext wave
        exact (rowCLM wave).map_smul scalar _ }
    (2 * Real.pi) divergence_bound

theorem divergenceCLM_source (stress : NativeFluidStressFourierState) (budget : ℝ)
    (bounded : ∀ wave output input, ‖stress wave output input‖ ≤ budget) (wave : NonzeroIntegerWavevector) :
    divergenceCLM (ofBound stress budget bounded) wave =
      NativeNegativeFourMomentum.weightedRowCLM wave.1 (projectedDivergenceCLM wave.1 (stress wave.1)) := by
  change rowCLM wave (weight wave.1 • tensor (stress wave.1)) = _
  rw [map_smul]
  simp only [weight, if_neg wave.2, rowCLM, smul_apply, NativeNegativeFourMomentum.weightedRowCLM,
    NativeNegativeFourMomentum.weight, ContinuousLinearMap.comp_apply, ← smul_assoc, smul_eq_mul, ← pow_two]
  rfl

private def viscousRow (nu : Viscosity) (velocity : WholeRestartVelocityEndpointState)
    (wave : NonzeroIntegerWavevector) : ComplexCoordinateEuclidean :=
  (nu.coeff * (2 * Real.pi) ^ 2 * (integerWaveNormSq wave.1)⁻¹) • velocity wave

private theorem viscousRow_bound (nu : Viscosity) (velocity : WholeRestartVelocityEndpointState)
    (wave : NonzeroIntegerWavevector) :
    ‖viscousRow nu velocity wave‖ ≤ (nu.coeff * (2 * Real.pi) ^ 2) * ‖velocity wave‖ := by
  have scalarNonnegative : 0 ≤ nu.coeff * (2 * Real.pi) ^ 2 := mul_nonneg nu.coeff_pos.le (sq_nonneg _)
  have inverseNonnegative := inv_nonneg.mpr (integerWaveNormSq_nonneg wave.1)
  have inverseBound := inv_le_one_of_one_le₀ (one_le_integerWaveNormSq wave.1 wave.2)
  rw [viscousRow, norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg scalarNonnegative inverseNonnegative)]
  exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right scalarNonnegative inverseBound) (norm_nonneg _)

def viscous (nu : Viscosity) (velocity : WholeRestartVelocityEndpointState) : WholeRestartVelocityEndpointState :=
  ⟨viscousRow nu velocity, by
    apply memℓp_gen
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    have source : Summable (fun wave => ‖velocity wave‖ ^ 2) := by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
        (lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) velocity).summable
    exact (source.mul_left ((nu.coeff * (2 * Real.pi) ^ 2) ^ 2)).of_nonneg_of_le
      (fun _ => sq_nonneg _) (fun wave => by
        simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (viscousRow_bound nu velocity wave) 2)⟩

theorem viscous_bound (nu : Viscosity) (velocity : WholeRestartVelocityEndpointState) :
    ‖viscous nu velocity‖ ≤ (nu.coeff * (2 * Real.pi) ^ 2) * ‖velocity‖ := by
  have scalarNonnegative : 0 ≤ nu.coeff * (2 * Real.pi) ^ 2 := mul_nonneg nu.coeff_pos.le (sq_nonneg _)
  have actual := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) (viscous nu velocity)
  have source := (lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) velocity).mul_left
    ((nu.coeff * (2 * Real.pi) ^ 2) ^ 2)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at actual source
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg scalarNonnegative (norm_nonneg _))).mp
  rw [mul_pow]
  exact hasSum_le (fun wave => by
    change ‖viscousRow nu velocity wave‖ ^ 2 ≤ _
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (viscousRow_bound nu velocity wave) 2) actual source

def viscousCLM (nu : Viscosity) : WholeRestartVelocityEndpointState →L[ℝ] WholeRestartVelocityEndpointState :=
  LinearMap.mkContinuous
    { toFun := viscous nu
      map_add' := fun first last => by
        apply lp.ext
        funext wave
        exact smul_add _ _ _
      map_smul' := fun scalar value => by
        apply lp.ext
        funext wave
        exact smul_comm _ scalar _ }
    (nu.coeff * (2 * Real.pi) ^ 2) (viscous_bound nu)

theorem viscousCLM_source (nu : Viscosity) (velocity : WholeRestartVelocityEndpointState) (wave : NonzeroIntegerWavevector) :
    viscousCLM nu velocity wave = NativeNegativeFourMomentum.weightedRowCLM wave.1
      ((nu.coeff * integerWaveViscousMultiplier wave.1) • wholeVelocity velocity wave.1) := by
  change viscousRow nu velocity wave = _
  have rowIdentity := NativeNegativeFourMomentum.weightedRowCLM_row velocity wave
  change NativeNegativeFourMomentum.weightedRowCLM wave.1 (wholeVelocity velocity wave.1) =
    NativeNegativeFourMomentum.embed velocity wave at rowIdentity
  rw [map_smul, rowIdentity]
  change (nu.coeff * (2 * Real.pi) ^ 2 * (integerWaveNormSq wave.1)⁻¹) • velocity wave =
    (nu.coeff * integerWaveViscousMultiplier wave.1) • (NativeNegativeFourMomentum.weight wave.1 • velocity wave)
  rw [smul_smul]
  congr 1
  unfold integerWaveViscousMultiplier NativeNegativeFourMomentum.weight
  field_simp

abbrev FullSpace := WithLp 2 (WholeRestartVelocityEndpointState × Space)

def momentumCLM (nu : Viscosity) : FullSpace →L[ℝ] WholeRestartVelocityEndpointState :=
  divergenceCLM.comp (WithLp.sndL 2 ℝ WholeRestartVelocityEndpointState Space) -
    (viscousCLM nu).comp (WithLp.fstL 2 ℝ WholeRestartVelocityEndpointState Space)

theorem momentumCLM_source (nu : Viscosity) (velocity : WholeRestartVelocityEndpointState)
    (stress : NativeFluidStressFourierState) (budget : ℝ)
    (bounded : ∀ wave output input, ‖stress wave output input‖ ≤ budget) (wave : NonzeroIntegerWavevector) :
    momentumCLM nu (WithLp.toLp 2 (velocity, ofBound stress budget bounded)) wave =
      NativeNegativeFourMomentum.weightedRowCLM wave.1
        (projectedDivergenceCLM wave.1 (stress wave.1) -
          (nu.coeff * integerWaveViscousMultiplier wave.1) • wholeVelocity velocity wave.1) := by
  change divergenceCLM (ofBound stress budget bounded) wave - viscousCLM nu velocity wave = _
  rw [divergenceCLM_source, viscousCLM_source, map_sub]

end
end SaturationMonoid.NavierStokes.NativeCompleteStressAction
