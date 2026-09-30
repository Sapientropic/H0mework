import H0mework.NavierStokes.StressWholeH1.Equation
import H0mework.NavierStokes.StressDynamics.ZeroStepAction

set_option autoImplicit false
open scoped Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeNegativeOneInclusion

open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open NativeResolventCompactness NativeWholeResolvent NativeWholeH1Mixed NativeWholeH1Pairing
open NativeNegativeFourMomentum NativeEndpointVelocityCarrier NativeCompleteStressAction

noncomputable section

def lowerWeight (wave : Wave) : ℝ := Real.sqrt (integerWaveViscousMultiplier wave.1) * weight wave.1

theorem lowerWeight_positive (wave : Wave) : 0 < lowerWeight wave := by
  unfold lowerWeight weight
  exact mul_pos (Real.sqrt_pos.mpr (multiplier_positive wave)) (sq_pos_of_pos (inv_pos.mpr (integerWaveNormSq_pos wave.2)))

theorem lowerWeight_bound (wave : Wave) : lowerWeight wave ≤ 2 * Real.pi := by
  have nonnegative := integerWaveNormSq_nonneg wave.1
  have one := one_le_integerWaveNormSq wave.1 wave.2
  have root : Real.sqrt (integerWaveNormSq wave.1) ≤ integerWaveNormSq wave.1 := by
    apply (Real.sqrt_le_left nonnegative).mpr
    nlinarith
  have scalar : Real.sqrt (integerWaveViscousMultiplier wave.1) =
      (2 * Real.pi) * Real.sqrt (integerWaveNormSq wave.1) := by
    rw [integerWaveViscousMultiplier, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  rw [lowerWeight, scalar, weight]
  calc
    _ ≤ ((2 * Real.pi) * integerWaveNormSq wave.1) * (integerWaveNormSq wave.1)⁻¹ ^ 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left root (by positivity)) (sq_nonneg _)
    _ = (2 * Real.pi) * (integerWaveNormSq wave.1)⁻¹ := by
      field_simp
    _ ≤ _ := mul_le_of_le_one_right (by positivity) (inv_le_one_of_one_le₀ one)

def lower (value : State) : State :=
  ⟨fun wave => lowerWeight wave • value wave, by
    apply memℓp_gen
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    have summable : Summable (fun wave => ‖value wave‖ ^ 2) := by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using value.2.summable (by norm_num)
    apply (summable.mul_left ((2 * Real.pi) ^ 2)).of_nonneg_of_le (fun _ => sq_nonneg _)
    intro wave
    have bound := pow_le_pow_left₀ (lowerWeight_positive wave).le (lowerWeight_bound wave) 2
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos (lowerWeight_positive wave), mul_pow] using
      mul_le_mul_of_nonneg_right bound (sq_nonneg ‖value wave‖)⟩

theorem lower_norm (value : State) : ‖lower value‖ ≤ (2 * Real.pi) * ‖value‖ := by
  have dominated : ‖lower value‖ ≤ ‖(2 * Real.pi) • value‖ := by
    apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    intro wave
    change ‖lowerWeight wave • value wave‖ ≤ ‖(2 * Real.pi) • value wave‖
    simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (lowerWeight_positive wave), abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    exact mul_le_mul_of_nonneg_right (lowerWeight_bound wave) (norm_nonneg _)
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 2 * Real.pi)] using dominated

def lowerCLM : State →L[ℝ] State :=
  LinearMap.mkContinuous
    { toFun := lower
      map_add' := fun first last => by
        apply lp.ext
        funext wave
        exact smul_add _ _ _
      map_smul' := fun scalar value => by
        apply lp.ext
        funext wave
        change lowerWeight wave • (scalar • value wave) = scalar • (lowerWeight wave • value wave)
        exact smul_comm _ _ _ }
    (2 * Real.pi) lower_norm

theorem lower_injective : Function.Injective lowerCLM := by
  intro first last same
  apply lp.ext
  funext wave
  have original := congrArg (fun value : State => value wave) same
  change lowerWeight wave • first wave = lowerWeight wave • last wave at original
  have decoded := congrArg (fun vector : ComplexCoordinateEuclidean => (lowerWeight wave)⁻¹ • vector) original
  simpa only [inv_smul_smul₀ (lowerWeight_positive wave).ne'] using decoded

theorem lower_inverseGradient (value : State) : lowerCLM (inverseGradient value) = embed value := by
  apply lp.ext
  funext wave
  change lowerWeight wave • ((Real.sqrt (integerWaveViscousMultiplier wave.1))⁻¹ • value wave) = weight wave.1 • value wave
  rw [smul_smul, lowerWeight, mul_right_comm,
    mul_inv_cancel₀ (Real.sqrt_pos.mpr (multiplier_positive wave)).ne', one_mul]

theorem lower_momentum (nu : Viscosity) (velocity : wholePhysical) (regular : H1 velocity) :
    lowerCLM (negativeAction velocity velocity regular regular - nu.coeff • gradientValue velocity regular) =
      NativeWholeResolventZeroAction.momentumOperator nu velocity.1 velocity.1 := by
  apply lp.ext
  funext wave
  have inverse : lowerWeight wave * (Real.sqrt (integerWaveViscousMultiplier wave.1))⁻¹ = weight wave.1 := by
    rw [lowerWeight, mul_right_comm, mul_inv_cancel₀ (Real.sqrt_pos.mpr (multiplier_positive wave)).ne', one_mul]
  have gradient : lowerWeight wave * Real.sqrt (integerWaveViscousMultiplier wave.1) =
      weight wave.1 * integerWaveViscousMultiplier wave.1 := by
    rw [lowerWeight, mul_right_comm, ← pow_two, Real.sq_sqrt (multiplier_positive wave).le]
    ring
  change lowerWeight wave • (negativeRow velocity velocity wave -
    nu.coeff • (Real.sqrt (integerWaveViscousMultiplier wave.1) • velocity.1 wave)) = _
  rw [smul_sub, negativeRow]
  simp only [smul_smul]
  rw [inverse]
  have viscous : lowerWeight wave * (nu.coeff * Real.sqrt (integerWaveViscousMultiplier wave.1)) =
      weight wave.1 * (nu.coeff * integerWaveViscousMultiplier wave.1) := by
    calc
      _ = nu.coeff * (lowerWeight wave * Real.sqrt (integerWaveViscousMultiplier wave.1)) := by ring
      _ = _ := by rw [gradient]; ring
  rw [viscous]
  unfold NativeWholeResolventZeroAction.momentumOperator
  change _ = (divergenceCLM (NativeCompleteStressBilinear.mixed (wholeVelocity velocity.1) (wholeVelocity velocity.1)) -
    viscousCLM nu velocity.1) wave
  rw [lp.coeFn_sub, Pi.sub_apply, NativeCompleteStressBilinear.mixed, divergenceCLM_source, viscousCLM_source]
  have weighted (vector : ComplexCoordinateVector) : weightedRowCLM wave.1 vector = weight wave.1 • euclideanCLM vector := rfl
  rw [weighted, weighted, map_smul, NativeWholeH1Equation.euclidean_whole_row velocity wave]
  change _ = weight wave.1 • euclideanCoordinateRow (row velocity velocity wave.1) -
    weight wave.1 • ((nu.coeff * integerWaveViscousMultiplier wave.1) • velocity.1 wave)
  simp only [smul_smul]

end
end SaturationMonoid.NavierStokes.NativeNegativeOneInclusion
