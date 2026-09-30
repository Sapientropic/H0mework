import H0mework.Versions.X.NavierStokes.MomentumAction.MomentumIntegralSplice
import H0mework.NavierStokes.CorrectionControl.Whole

set_option autoImplicit false
open scoped BigOperators Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeNegativeFourMomentum

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinAmbientNorm
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinFiniteObservationTimeTightness
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open ThreeDimensionalIntegerLatticeCriticalKernel
open NativeEndpointVelocityCarrier NativeStressSource NativeMomentumIntegral NativeTimeJetCarrier
open NativeFullOrderTime NativeFullOrderStress NativeStressCurlAlgebra

noncomputable section

def weight (wave : IntegerWavevector) : ℝ := (integerWaveNormSq wave)⁻¹ ^ 2

theorem weight_nonnegative (wave : IntegerWavevector) : 0 ≤ weight wave := sq_nonneg _

theorem weight_le_one (wave : IntegerWavevector) : weight wave ≤ 1 := by
  by_cases nonzero : wave ≠ 0
  · exact (sq_le_one_iff₀ (inv_nonneg.mpr (integerWaveNormSq_nonneg wave))).mpr
      (inv_le_one_of_one_le₀ (one_le_integerWaveNormSq wave nonzero))
  · have atZero : wave = 0 := not_ne_iff.mp nonzero
    subst wave
    simp [weight, integerWaveNormSq]

def weightedVelocity (velocity : WholeRestartVelocityEndpointState) : WholeRestartVelocityEndpointState :=
  ⟨fun wave => weight wave.1 • velocity wave, by
    apply memℓp_gen
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    apply (show Summable fun wave => ‖velocity wave‖ ^ 2 from by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using velocity.2.summable (by norm_num)).of_nonneg_of_le
      (fun _ => sq_nonneg _)
    intro wave
    apply pow_le_pow_left₀ (norm_nonneg _) _
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (weight_nonnegative _)]
    exact mul_le_of_le_one_left (norm_nonneg _) (weight_le_one _)⟩

theorem weightedVelocity_norm_le (velocity : WholeRestartVelocityEndpointState) : ‖weightedVelocity velocity‖ ≤ ‖velocity‖ := by
  apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  intro wave
  change ‖weight wave.1 • velocity wave‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (weight_nonnegative _)]
  exact mul_le_of_le_one_left (norm_nonneg _) (weight_le_one _)

def embed : WholeRestartVelocityEndpointState →L[ℝ] WholeRestartVelocityEndpointState :=
  LinearMap.mkContinuous
    { toFun := weightedVelocity
      map_add' := fun left right => by
        apply lp.ext
        funext wave
        change weight wave.1 • (left wave + right wave) = weight wave.1 • left wave + weight wave.1 • right wave
        exact smul_add _ _ _
      map_smul' := fun scalar value => by
        apply lp.ext
        funext wave
        change weight wave.1 • (scalar • value wave) = scalar • (weight wave.1 • value wave)
        exact smul_comm _ _ _ }
    1 (fun velocity => by
      change ‖weightedVelocity velocity‖ ≤ 1 * ‖velocity‖
      simpa only [one_mul] using weightedVelocity_norm_le velocity)

theorem embed_apply (velocity : WholeRestartVelocityEndpointState) (wave : NonzeroIntegerWavevector) :
    embed velocity wave = weight wave.1 • velocity wave := rfl

theorem embed_reconstruct (velocity : WholeRestartVelocityEndpointState) (wave : NonzeroIntegerWavevector) :
    integerWaveNormSq wave.1 ^ 2 • embed velocity wave = velocity wave := by
  rw [embed_apply, weight, smul_smul, ← mul_pow, mul_inv_cancel₀ (integerWaveNormSq_pos wave.2).ne', one_pow, one_smul]

theorem embed_injective : Function.Injective embed := by
  intro left right same
  apply lp.ext
  funext wave
  rw [← embed_reconstruct left wave, ← embed_reconstruct right wave, same]

def actionCap (nu : Viscosity) (radius : ℝ) : ℝ :=
  6 * Real.pi * radius ^ 2 + nu.coeff * (2 * Real.pi) ^ 2 * radius

theorem actionCap_nonnegative (nu : Viscosity) {radius : ℝ} (nonnegative : 0 ≤ radius) : 0 ≤ actionCap nu radius := by
  have viscosity := nu.coeff_pos.le
  unfold actionCap
  positivity

theorem actionCap_mono (nu : Viscosity) {left right : ℝ} (nonnegative : 0 ≤ left) (bound : left ≤ right) :
    actionCap nu left ≤ actionCap nu right := by
  have viscosity := nu.coeff_pos.le
  unfold actionCap
  gcongr

theorem action_norm_le_wave (nu : Viscosity) (velocity : WholeRestartVelocityEndpointState) (wave : IntegerWavevector) :
    ‖action nu velocity wave‖ ≤ actionCap nu ‖velocity‖ * integerWaveNormSq wave := by
  by_cases nonzero : wave ≠ 0
  · let stress := quadraticFlux (wholeVelocity velocity)
    have waveNonnegative := integerWaveNormSq_nonneg wave
    have stressBound (output input : Coordinate) : Complex.normSq (stress wave output input) ≤ ‖velocity‖ ^ 4 := by
      have source := quadraticFlux_norm_le_mass (wholeVelocity velocity) wave output input
      rw [wholeVelocity_mass] at source
      rw [Complex.normSq_eq_norm_sq]
      exact (pow_le_pow_left₀ (norm_nonneg _) source 2).trans_eq (by ring)
    have total : (∑ output : Coordinate, ∑ input : Coordinate, Complex.normSq (stress wave output input)) ≤ 9 * ‖velocity‖ ^ 4 := by
      have source := Finset.sum_le_sum (s := Finset.univ) fun output _ =>
        Finset.sum_le_sum (s := Finset.univ) fun input _ => stressBound output input
      simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc,
        Nat.cast_ofNat, show (3 : ℝ) * 3 = 9 by norm_num] using source
    have square := ((complexCoordinateVector_norm_sq_le_amplitudeSq
      (transverseProjection wave (nativeFluidStressDivergenceCoefficient stress wave))).trans
      (transverseProjection_amplitudeSq_le wave nonzero _)).trans
        ((divergence_amplitude_le stress wave).trans (mul_le_mul_of_nonneg_left total
          (mul_nonneg (sq_nonneg _) (integerWaveNormSq_nonneg wave))))
    have frequency : integerWaveNormSq wave ≤ integerWaveNormSq wave ^ 2 := by
      nlinarith [one_le_integerWaveNormSq wave nonzero]
    have multiplied := mul_le_mul_of_nonneg_left frequency
      (by positivity : 0 ≤ 9 * (2 * Real.pi) ^ 2 * ‖velocity‖ ^ 4)
    have nonlinear : ‖projectedDivergenceCLM wave (stress wave)‖ ≤ 6 * Real.pi * ‖velocity‖ ^ 2 * integerWaveNormSq wave := by
      apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
      change ‖transverseProjection wave (nativeFluidStressDivergenceCoefficient stress wave)‖ ^ 2 ≤ _
      unfold integerWaveViscousMultiplier at square
      nlinarith
    have rowBound : ‖row velocity wave‖ ≤ ‖velocity‖ :=
      (lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) (wholeVelocity velocity) wave).trans (wholeVelocity_norm_le velocity)
    have viscous := mul_le_mul_of_nonneg_left rowBound (abs_nonneg (nu.coeff * integerWaveViscousMultiplier wave))
    have coefficient : 0 ≤ nu.coeff * integerWaveViscousMultiplier wave :=
      mul_nonneg nu.coeff_pos.le (mul_nonneg (sq_nonneg _) (integerWaveNormSq_nonneg _))
    rw [abs_of_nonneg coefficient] at viscous
    have bound := (norm_sub_le (projectedDivergenceCLM wave (stress wave))
      ((nu.coeff * integerWaveViscousMultiplier wave) • row velocity wave)).trans
        (add_le_add nonlinear (by simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg coefficient] using viscous))
    apply bound.trans_eq
    unfold actionCap integerWaveViscousMultiplier
    ring
  · have atZero : wave = 0 := not_ne_iff.mp nonzero
    subst wave
    simp [action, row, projectedDivergenceCLM_apply, transverseProjection, integerWaveNormSq, integerWaveViscousMultiplier]

def weightedActionRow (nu : Viscosity) (velocity : WholeRestartVelocityEndpointState) (wave : IntegerWavevector) :
    ComplexCoordinateVector := weight wave • action nu velocity wave

theorem weightedActionRow_sq_le (nu : Viscosity) (velocity : WholeRestartVelocityEndpointState) (wave : IntegerWavevector) :
    ‖weightedActionRow nu velocity wave‖ ^ 2 ≤ actionCap nu ‖velocity‖ ^ 2 * integerWaveCriticalKernel wave := by
  by_cases atZero : integerWaveNormSq wave = 0
  · simp [weightedActionRow, weight, integerWaveCriticalKernel, atZero]
  have bound := mul_le_mul_of_nonneg_left (action_norm_le_wave nu velocity wave) (weight_nonnegative wave)
  have scale : weight wave * (actionCap nu ‖velocity‖ * integerWaveNormSq wave) =
      actionCap nu ‖velocity‖ * (integerWaveNormSq wave)⁻¹ := by unfold weight; field_simp
  rw [scale] at bound
  have normBound : ‖weightedActionRow nu velocity wave‖ ≤ actionCap nu ‖velocity‖ * (integerWaveNormSq wave)⁻¹ := by
    simpa only [weightedActionRow, norm_smul, Real.norm_eq_abs, abs_of_nonneg (weight_nonnegative wave)] using bound
  have square := pow_le_pow_left₀ (norm_nonneg _) normBound 2
  simpa only [integerWaveCriticalKernel, mul_pow] using square

def rawAction (nu : Viscosity) (velocity : WholeRestartVelocityEndpointState) : ComplexVorticityHilbertState :=
  ⟨weightedActionRow nu velocity, by
    apply memℓp_gen
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    exact (summable_integerWaveCriticalKernel.mul_left (actionCap nu ‖velocity‖ ^ 2)).of_nonneg_of_le
      (fun _ => sq_nonneg _) (weightedActionRow_sq_le nu velocity)⟩

def actionState (nu : Viscosity) (velocity : WholeRestartVelocityEndpointState) : WholeRestartVelocityEndpointState :=
  puncturedEuclideanize (rawAction nu velocity)

def weightedRowCLM (wave : IntegerWavevector) : ComplexCoordinateVector →L[ℝ] ComplexCoordinateEuclidean :=
  weight wave • (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Coordinate => ℂ)).symm.toContinuousLinearMap

theorem actionState_apply (nu : Viscosity) (velocity : WholeRestartVelocityEndpointState) (wave : NonzeroIntegerWavevector) :
    actionState nu velocity wave = weightedRowCLM wave.1 (action nu velocity wave.1) := rfl

theorem weightedRowCLM_row (velocity : WholeRestartVelocityEndpointState) (wave : NonzeroIntegerWavevector) :
    weightedRowCLM wave.1 (row velocity wave.1) = embed velocity wave := by
  rw [embed_apply]
  change weight wave.1 • WithLp.toLp 2 (wholeVelocity velocity wave.1) = weight wave.1 • velocity wave
  congr 1
  ext coordinate
  exact wholeVelocity_nonzero velocity wave coordinate

theorem actionState_norm_sq_le (nu : Viscosity) (velocity : WholeRestartVelocityEndpointState) :
    ‖actionState nu velocity‖ ^ 2 ≤ 3 * actionCap nu ‖velocity‖ ^ 2 * ∑' wave, integerWaveCriticalKernel wave := by
  have raw : ‖rawAction nu velocity‖ ^ 2 ≤ actionCap nu ‖velocity‖ ^ 2 * ∑' wave, integerWaveCriticalKernel wave := by
    have normEq := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num) (rawAction nu velocity)
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at normEq
    rw [normEq, ← tsum_mul_left]
    apply Summable.tsum_le_tsum (weightedActionRow_sq_le nu velocity)
      ((summable_integerWaveCriticalKernel.mul_left (actionCap nu ‖velocity‖ ^ 2)).of_nonneg_of_le
        (fun _ => sq_nonneg _) (weightedActionRow_sq_le nu velocity))
      (summable_integerWaveCriticalKernel.mul_left _)
  exact (puncturedEuclideanize_norm_sq_le _).trans
    ((mul_le_mul_of_nonneg_left raw (by norm_num)).trans_eq (by ring))

def actionBudget (nu : Viscosity) (radius : ℝ) : ℝ :=
  Real.sqrt (3 * actionCap nu radius ^ 2 * ∑' wave, integerWaveCriticalKernel wave)

theorem actionState_norm_le (nu : Viscosity) (velocity : WholeRestartVelocityEndpointState) (radius : ℝ)
    (bounded : ‖velocity‖ ≤ radius) : ‖actionState nu velocity‖ ≤ actionBudget nu radius := by
  apply Real.le_sqrt_of_sq_le
  apply (actionState_norm_sq_le nu velocity).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (actionCap_nonnegative nu (norm_nonneg _))
        (actionCap_mono nu (norm_nonneg _) bounded) 2) (by norm_num))
    (tsum_nonneg integerWaveCriticalKernel_nonneg)

end
end SaturationMonoid.NavierStokes.NativeNegativeFourMomentum
