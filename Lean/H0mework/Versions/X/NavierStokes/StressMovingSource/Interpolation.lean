import H0mework.Versions.X.NavierStokes.StressTimeControl.Interpolation

set_option autoImplicit false
open scoped BigOperators

namespace SaturationMonoid.NavierStokes.NativeMovingSourceInterpolation

open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open NativeFiniteActionResolvent NativeCommonAdvectorAction NativeWholeResolvent
open NativeDualCurlResolvent NativePhysicalPairing NativeNegativeInterpolation

noncomputable section

theorem physical_interpolation (frequencies : Finset IntegerWavevector) (zeroNotMem : 0 ∉ frequencies)
    (closed : FiniteModeNegClosed frequencies) (value : physicalSpace frequencies) :
    ((2 * Real.pi) ^ 2) ^ 4 * ‖puncturedEuclideanize value.1‖ ^ 10 ≤
      ‖NativeNegativeFourMomentum.embed (puncturedEuclideanize value.1)‖ ^ 2 *
        curlPair frequencies value.1 value.1 ^ 4 := by
  have interpolation := negativeMass_interpolation frequencies zeroNotMem closed
    (includeCLM frequencies closed value)
  rw [restrict_include, include_norm frequencies zeroNotMem closed] at interpolation
  have paired := pairing_le frequencies zeroNotMem value value
  change inner ℝ (coefficients frequencies value) (coefficients frequencies value) ≤ _ at paired
  rw [real_inner_self_eq_norm_sq] at paired
  have squared := pow_le_pow_left₀ (sq_nonneg ‖coefficients frequencies value‖) paired 2
  have nonnegativeMass : 0 ≤ negativeMass frequencies value := by
    rw [← negative_norm_sq frequencies zeroNotMem value]
    exact sq_nonneg _
  have nonnegativeCurl : 0 ≤ curlPair frequencies value.1 value.1 := by
    rw [← gradient_norm_sq frequencies zeroNotMem value]
    exact sq_nonneg _
  rw [mul_pow, Real.sq_sqrt nonnegativeMass, Real.sq_sqrt nonnegativeCurl] at squared
  have powered := pow_le_pow_left₀ (sq_nonneg (‖coefficients frequencies value‖ ^ 2)) squared 4
  rw [physical_norm frequencies zeroNotMem]
  by_cases zero : ‖coefficients frequencies value‖ = 0
  · simp only [zero, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_zero]
    positivity
  apply (mul_le_mul_iff_left₀ (pow_pos (lt_of_le_of_ne (norm_nonneg _) (Ne.symm zero)) 6)).mp
  calc
    _ = ((2 * Real.pi) ^ 2) ^ 4 * ((‖coefficients frequencies value‖ ^ 2) ^ 2) ^ 4 := by ring
    _ ≤ ((2 * Real.pi) ^ 2) ^ 4 *
        (negativeMass frequencies value * curlPair frequencies value.1 value.1) ^ 4 :=
      mul_le_mul_of_nonneg_left powered (by positivity)
    _ = ((2 * Real.pi) ^ 2 * negativeMass frequencies value) ^ 4 *
        curlPair frequencies value.1 value.1 ^ 4 := by ring
    _ ≤ (‖NativeNegativeFourMomentum.embed (puncturedEuclideanize value.1)‖ ^ 2 *
        ‖coefficients frequencies value‖ ^ 6) * curlPair frequencies value.1 value.1 ^ 4 :=
      mul_le_mul_of_nonneg_right interpolation (pow_nonneg nonnegativeCurl 4)
    _ = _ := by ring

end
end SaturationMonoid.NavierStokes.NativeMovingSourceInterpolation
