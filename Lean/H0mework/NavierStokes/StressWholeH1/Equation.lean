import H0mework.NavierStokes.StressWholeH1.Pairing
import H0mework.NavierStokes.StressWholeH1.Approximation
import H0mework.NavierStokes.StressWholeH1.Cancellation

set_option autoImplicit false
open scoped BigOperators Topology

namespace SaturationMonoid.NavierStokes.NativeWholeH1Equation

open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open NativeResolventCompactness NativeWholeResolvent NativeEndpointVelocityCarrier
open NativeWholeH1Mixed NativeWholeH1Pairing NativeWholeH1Approximation

noncomputable section

theorem euclidean_whole_row (value : wholePhysical) (wave : Wave) :
    NativeCompleteStressAction.euclideanCLM (wholeVelocity value.1 wave.1) = value.1 wave := by
  apply PiLp.ext
  intro coordinate
  exact wholeVelocity_nonzero value.1 wave coordinate

theorem inverse_weight_multiplier (wave : Wave) :
    (Real.sqrt (integerWaveViscousMultiplier wave.1))⁻¹ * integerWaveViscousMultiplier wave.1 =
      Real.sqrt (integerWaveViscousMultiplier wave.1) := by
  conv_lhs => rhs; rw [← Real.sq_sqrt (multiplier_positive wave).le]
  rw [pow_two, ← mul_assoc, inv_mul_cancel₀ (Real.sqrt_pos.mpr (multiplier_positive wave)).ne', one_mul]

theorem equation_state (nu : Viscosity) (U x value : wholePhysical) (uH1 : H1 U) (valueH1 : H1 value)
    (step : ℝ) (equation : ∀ wave : Wave,
      wholeVelocity value.1 wave.1 - step • (row U value wave.1 -
        (nu.coeff * integerWaveViscousMultiplier wave.1) • wholeVelocity value.1 wave.1) =
          wholeVelocity x.1 wave.1) :
    inverseGradient value.1 - step • (negativeAction U value uH1 valueH1 - nu.coeff • gradientValue value valueH1) =
      inverseGradient x.1 := by
  apply lp.ext
  funext wave
  have original := congrArg NativeCompleteStressAction.euclideanCLM (equation wave)
  rw [map_sub, map_smul, map_sub, map_smul,
    euclidean_whole_row value wave, euclidean_whole_row x wave] at original
  let a := (Real.sqrt (integerWaveViscousMultiplier wave.1))⁻¹
  have scale : a * (nu.coeff * integerWaveViscousMultiplier wave.1) =
      nu.coeff * Real.sqrt (integerWaveViscousMultiplier wave.1) := by
    calc
      _ = nu.coeff * (a * integerWaveViscousMultiplier wave.1) := by ring
      _ = _ := by rw [inverse_weight_multiplier]
  have weighted := congrArg (fun vector : ComplexCoordinateEuclidean => a • vector) original
  rw [smul_sub, smul_comm a step, smul_sub, smul_smul, scale] at weighted
  change a • value.1 wave - step •
    (a • NativeCompleteStressAction.euclideanCLM (row U value wave.1) -
      nu.coeff • (Real.sqrt (integerWaveViscousMultiplier wave.1) • value.1 wave)) = a • x.1 wave
  simpa only [smul_smul] using weighted

theorem homogeneous_zero (nu : Viscosity) (U value : wholePhysical) (uH1 : H1 U) (valueH1 : H1 value)
    (step : ℝ) (nonnegative : 0 ≤ step) (equation : ∀ wave : Wave,
      wholeVelocity value.1 wave.1 - step • (row U value wave.1 -
        (nu.coeff * integerWaveViscousMultiplier wave.1) • wholeVelocity value.1 wave.1) = 0) :
    value = 0 := by
  have zeroWhole : wholeVelocity (0 : State) = 0 := wholeVelocityCLM.map_zero
  have original := equation_state nu U 0 value uH1 valueH1 step (fun wave => by
    simpa only [Submodule.coe_zero, zeroWhole, lp.coeFn_zero, Pi.zero_apply] using equation wave)
  have zero : inverseGradient (0 : State) = 0 := by
    apply lp.ext
    funext wave
    change (Real.sqrt (integerWaveViscousMultiplier wave.1))⁻¹ • (0 : ComplexCoordinateEuclidean) = 0
    exact smul_zero _
  rw [Submodule.coe_zero, zero] at original
  have paired := congrArg (fun input : State => inner ℝ input (gradientValue value valueH1)) original
  rw [inner_sub_left, real_inner_smul_left, inner_sub_left, real_inner_smul_left,
    inverse_gradient_pairing, NativeWholeH1Cancellation.whole_cancellation nu U value uH1 valueH1,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, inner_zero_left] at paired
  have cost := mul_nonneg (mul_nonneg nonnegative nu.coeff_pos.le)
    (sq_nonneg ‖gradientValue value valueH1‖)
  apply Subtype.ext
  apply norm_eq_zero.mp
  nlinarith only [paired, cost, norm_nonneg value.1]

theorem whole_resolvent_unique (nu : Viscosity) (U x first last : wholePhysical)
    (uH1 : H1 U) (firstH1 : H1 first) (lastH1 : H1 last) (step : ℝ) (nonnegative : 0 ≤ step)
    (firstEquation : ∀ wave : Wave,
      wholeVelocity first.1 wave.1 - step • (row U first wave.1 -
        (nu.coeff * integerWaveViscousMultiplier wave.1) • wholeVelocity first.1 wave.1) =
          wholeVelocity x.1 wave.1)
    (lastEquation : ∀ wave : Wave,
      wholeVelocity last.1 wave.1 - step • (row U last wave.1 -
        (nu.coeff * integerWaveViscousMultiplier wave.1) • wholeVelocity last.1 wave.1) =
          wholeVelocity x.1 wave.1) : first = last := by
  apply sub_eq_zero.mp
  apply homogeneous_zero nu U (first - last) uH1 (H1_sub first last firstH1 lastH1) step nonnegative
  intro wave
  have difference : wholeVelocity (first - last).1 = wholeVelocity first.1 - wholeVelocity last.1 :=
    wholeVelocityCLM.map_sub first.1 last.1
  rw [difference, row_sub_right]
  change (wholeVelocity first.1 wave.1 - wholeVelocity last.1 wave.1) - step •
    ((row U first wave.1 - row U last wave.1) - (nu.coeff * integerWaveViscousMultiplier wave.1) •
      (wholeVelocity first.1 wave.1 - wholeVelocity last.1 wave.1)) = 0
  calc
    _ = (wholeVelocity first.1 wave.1 - step • (row U first wave.1 -
        (nu.coeff * integerWaveViscousMultiplier wave.1) • wholeVelocity first.1 wave.1)) -
      (wholeVelocity last.1 wave.1 - step • (row U last wave.1 -
        (nu.coeff * integerWaveViscousMultiplier wave.1) • wholeVelocity last.1 wave.1)) := by
      simp only [smul_sub]
      abel
    _ = 0 := by rw [firstEquation wave, lastEquation wave, sub_self]

end
end SaturationMonoid.NavierStokes.NativeWholeH1Equation
