import H0mework.NavierStokes.StressTimeControl.DualCurl
import H0mework.NavierStokes.StressResolvent.WholeResolvent

set_option autoImplicit false
open scoped BigOperators Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeNegativeInterpolation

open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open NativeResolventCompactness NativeWholeResolvent NativeEndpointVelocityCarrier
open NativeDualCurlResolvent

noncomputable section

private theorem finite_interpolation {I : Type*} (observed : Finset I) (w a : I → ℝ) :
    (∑ k ∈ observed, w k * a k ^ 2) ^ 4 ≤
      (∑ k ∈ observed, w k ^ 4 * a k ^ 2) * (∑ k ∈ observed, a k ^ 2) ^ 3 := by
  have first := Finset.sum_mul_sq_le_sq_mul_sq observed (fun k => w k * a k) a
  have second := Finset.sum_mul_sq_le_sq_mul_sq observed (fun k => w k ^ 2 * a k) a
  simp only [mul_pow, mul_assoc, ← pow_two, ← pow_mul] at first second
  have squared := pow_le_pow_left₀ (sq_nonneg (∑ k ∈ observed, w k * a k ^ 2)) first 2
  calc
    _ = ((∑ k ∈ observed, w k * a k ^ 2) ^ 2) ^ 2 := by ring
    _ ≤ ((∑ k ∈ observed, w k ^ 2 * a k ^ 2) * ∑ k ∈ observed, a k ^ 2) ^ 2 := squared
    _ = (∑ k ∈ observed, w k ^ 2 * a k ^ 2) ^ 2 * (∑ k ∈ observed, a k ^ 2) ^ 2 := mul_pow _ _ _
    _ ≤ ((∑ k ∈ observed, w k ^ 4 * a k ^ 2) * ∑ k ∈ observed, a k ^ 2) *
        (∑ k ∈ observed, a k ^ 2) ^ 2 :=
      mul_le_mul_of_nonneg_right second (sq_nonneg _)
    _ = _ := by ring

/-- The negative weights are the original writer's Fourier weights. The
unweighted factor is the complete physical L² norm, with no extra budget. -/
theorem observed_interpolation (observed : Finset Wave) (x : State) :
    (∑ k ∈ observed, (integerWaveNormSq k.1)⁻¹ * ‖x k‖ ^ 2) ^ 4 ≤
      ‖NativeNegativeFourMomentum.embed x‖ ^ 2 * ‖x‖ ^ 6 := by
  have energy : (∑ k ∈ observed, ‖x k‖ ^ 2) ≤ ‖x‖ ^ 2 := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      lp.sum_rpow_le_norm_rpow (p := (2 : ℝ≥0∞)) (by norm_num) x observed
  have writer : (∑ k ∈ observed, (integerWaveNormSq k.1)⁻¹ ^ 4 * ‖x k‖ ^ 2) ≤
      ‖NativeNegativeFourMomentum.embed x‖ ^ 2 := by
    have actual := lp.sum_rpow_le_norm_rpow (p := (2 : ℝ≥0∞)) (by norm_num)
      (NativeNegativeFourMomentum.embed x) observed
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, NativeNegativeFourMomentum.embed_apply,
      norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, NativeNegativeFourMomentum.weight, ← pow_mul] using actual
  calc
    _ ≤ (∑ k ∈ observed, (integerWaveNormSq k.1)⁻¹ ^ 4 * ‖x k‖ ^ 2) *
        (∑ k ∈ observed, ‖x k‖ ^ 2) ^ 3 :=
      finite_interpolation observed (fun k => (integerWaveNormSq k.1)⁻¹) (fun k => ‖x k‖)
    _ ≤ ‖NativeNegativeFourMomentum.embed x‖ ^ 2 * (‖x‖ ^ 2) ^ 3 :=
      mul_le_mul writer (pow_le_pow_left₀ (Finset.sum_nonneg fun k _ => sq_nonneg _) energy 3)
        (pow_nonneg (Finset.sum_nonneg fun k _ => sq_nonneg _) 3) (sq_nonneg _)
    _ = _ := by ring

theorem scaled_negativeMass (frequencies : Finset IntegerWavevector) (zeroNotMem : 0 ∉ frequencies)
    (closed : FiniteModeNegClosed frequencies) (x : wholePhysical) :
    (2 * Real.pi) ^ 2 * negativeMass frequencies (restrictCLM frequencies zeroNotMem closed x) =
      ∑ k ∈ frequencies.subtype (fun wave => wave ≠ 0), (integerWaveNormSq k.1)⁻¹ * ‖x.1 k‖ ^ 2 := by
  let f (wave : IntegerWavevector) :=
    (integerWaveNormSq wave)⁻¹ * ‖euclideanCoordinateRow (wholeVelocity x.1 wave)‖ ^ 2
  have full : (2 * Real.pi) ^ 2 * negativeMass frequencies (restrictCLM frequencies zeroNotMem closed x) =
      ∑ wave ∈ frequencies, f wave := by
    rw [negativeMass, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro wave included
    have scalar : (2 * Real.pi) ^ 2 * (integerWaveViscousMultiplier wave)⁻¹ =
        (integerWaveNormSq wave)⁻¹ := by
      rw [integerWaveViscousMultiplier, mul_inv, ← mul_assoc,
        mul_inv_cancel₀ (pow_ne_zero 2 (mul_ne_zero (by norm_num) Real.pi_ne_zero)), one_mul]
    change (2 * Real.pi) ^ 2 * ((integerWaveViscousMultiplier wave)⁻¹ *
      ‖euclideanCoordinateRow (complexSharpSupportProjection frequencies (wholeVelocity x.1) wave)‖ ^ 2) = _
    rw [complexSharpSupportProjection_apply, if_pos included, ← mul_assoc, scalar]
  rw [full, ← Finset.sum_subtype_of_mem f (p := fun wave : IntegerWavevector => wave ≠ 0)
    (fun wave included zero => zeroNotMem (zero ▸ included))]
  apply Finset.sum_congr rfl
  intro wave included
  have row : euclideanCoordinateRow (wholeVelocity x.1 wave.1) = x.1 wave := by
    apply PiLp.ext
    intro coordinate
    exact wholeVelocity_nonzero x.1 wave coordinate
  dsimp only [f]
  rw [row]

theorem negativeMass_interpolation (frequencies : Finset IntegerWavevector) (zeroNotMem : 0 ∉ frequencies)
    (closed : FiniteModeNegClosed frequencies) (x : wholePhysical) :
    ((2 * Real.pi) ^ 2 * negativeMass frequencies (restrictCLM frequencies zeroNotMem closed x)) ^ 4 ≤
      ‖NativeNegativeFourMomentum.embed x.1‖ ^ 2 * ‖x‖ ^ 6 := by
  rw [scaled_negativeMass]
  exact observed_interpolation _ x.1

end
end SaturationMonoid.NavierStokes.NativeNegativeInterpolation
