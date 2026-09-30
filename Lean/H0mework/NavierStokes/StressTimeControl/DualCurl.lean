import H0mework.NavierStokes.StressWeakInput.FiniteAdjoint
import H0mework.NavierStokes.StressWeakInput.PhysicalPairing

set_option autoImplicit false
open scoped BigOperators

namespace SaturationMonoid.NavierStokes.NativeDualCurlResolvent

open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open NativeFiniteActionResolvent NativeCommonAdvectorAction NativeResolventAdjoint

noncomputable section

def negativeMass (frequencies : Finset IntegerWavevector) (value : physicalSpace frequencies) : ℝ :=
  ∑ wave ∈ frequencies, (integerWaveViscousMultiplier wave)⁻¹ * ‖euclideanCoordinateRow (value.1 wave)‖ ^ 2

def weightedCoefficients (frequencies : Finset IntegerWavevector) (weight : IntegerWavevector → ℝ)
    (value : physicalSpace frequencies) : EuclideanSpace ℂ (frequencies × Coordinate) :=
  WithLp.toLp 2 (fun entry => weight entry.1.1 • value.1 entry.1.1 entry.2)

theorem weighted_norm_sq (frequencies : Finset IntegerWavevector) (weight : IntegerWavevector → ℝ)
    (value : physicalSpace frequencies) :
    ‖weightedCoefficients frequencies weight value‖ ^ 2 =
      ∑ wave ∈ frequencies, weight wave ^ 2 * ‖euclideanCoordinateRow (value.1 wave)‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  calc
    _ = ∑ wave : frequencies, weight wave.1 ^ 2 * ‖euclideanCoordinateRow (value.1 wave.1)‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro wave included
      rw [EuclideanSpace.norm_sq_eq, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro coordinate coordinateMem
      simp only [weightedCoefficients, PiLp.toLp_apply, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
        euclideanCoordinateRow_apply]
    _ = _ := Finset.sum_coe_sort frequencies
      (fun wave => weight wave ^ 2 * ‖euclideanCoordinateRow (value.1 wave)‖ ^ 2)

theorem multiplier_pos (frequencies : Finset IntegerWavevector) (zeroNotMem : 0 ∉ frequencies)
    (wave : IntegerWavevector) (included : wave ∈ frequencies) : 0 < integerWaveViscousMultiplier wave :=
  integerWaveViscousMultiplier_pos ⟨wave, fun zero => zeroNotMem (zero ▸ included)⟩

theorem negative_norm_sq (frequencies : Finset IntegerWavevector) (zeroNotMem : 0 ∉ frequencies)
    (value : physicalSpace frequencies) :
    ‖weightedCoefficients frequencies (fun wave => (Real.sqrt (integerWaveViscousMultiplier wave))⁻¹) value‖ ^ 2 =
      negativeMass frequencies value := by
  rw [weighted_norm_sq]
  apply Finset.sum_congr rfl
  intro wave included
  rw [inv_pow, Real.sq_sqrt (multiplier_pos frequencies zeroNotMem wave included).le]

theorem gradient_norm_sq (frequencies : Finset IntegerWavevector) (zeroNotMem : 0 ∉ frequencies)
    (value : physicalSpace frequencies) :
    ‖weightedCoefficients frequencies (fun wave => Real.sqrt (integerWaveViscousMultiplier wave)) value‖ ^ 2 =
      curlPair frequencies value.1 value.1 := by
  rw [weighted_norm_sq]
  apply Finset.sum_congr rfl
  intro wave included
  rw [Real.sq_sqrt (multiplier_pos frequencies zeroNotMem wave included).le,
    ← curl_pair_row wave (fun zero => zeroNotMem (zero ▸ included)) _ _
      (physical_transverse value wave included) (physical_transverse value wave included),
    complexCoordinateRealInner_self, euclideanCoordinateRow_norm_sq,
    complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]

theorem weighted_pairing (frequencies : Finset IntegerWavevector) (zeroNotMem : 0 ∉ frequencies)
    (load value : physicalSpace frequencies) :
    pairing frequencies load value =
      inner ℝ (weightedCoefficients frequencies (fun wave => (Real.sqrt (integerWaveViscousMultiplier wave))⁻¹) load)
        (weightedCoefficients frequencies (fun wave => Real.sqrt (integerWaveViscousMultiplier wave)) value) := by
  change inner ℝ (coefficients frequencies load) (coefficients frequencies value) = _
  rw [PiLp.inner_apply, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro entry included
  change inner ℝ (load.1 entry.1.1 entry.2) (value.1 entry.1.1 entry.2) =
    inner ℝ ((Real.sqrt (integerWaveViscousMultiplier entry.1.1))⁻¹ • load.1 entry.1.1 entry.2)
      (Real.sqrt (integerWaveViscousMultiplier entry.1.1) • value.1 entry.1.1 entry.2)
  rw [real_inner_smul_left, real_inner_smul_right, ← mul_assoc,
    inv_mul_cancel₀ (Real.sqrt_pos.2 (multiplier_pos frequencies zeroNotMem entry.1.1 entry.1.2)).ne', one_mul]

theorem pairing_le (frequencies : Finset IntegerWavevector) (zeroNotMem : 0 ∉ frequencies)
    (load value : physicalSpace frequencies) :
    pairing frequencies load value ≤ Real.sqrt (negativeMass frequencies load) *
      Real.sqrt (curlPair frequencies value.1 value.1) := by
  rw [weighted_pairing frequencies zeroNotMem]
  have first := negative_norm_sq frequencies zeroNotMem load
  have last := gradient_norm_sq frequencies zeroNotMem value
  rw [← first, ← last, Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  exact real_inner_le_norm _ _

theorem resolver_energy (frequencies : Finset IntegerWavevector) (zeroNotMem : 0 ∉ frequencies)
    (closed : FiniteModeNegClosed frequencies) (nu : Viscosity) (advector : ComplexVorticityHilbertState)
    (reality : FiniteStateFourierReality advector) (step : ℝ) (nonnegative : 0 ≤ step)
    (load : physicalSpace frequencies) :
    let value := physicalResolver frequencies zeroNotMem closed nu advector reality step nonnegative load
    ‖coefficients frequencies value‖ ^ 2 + step * nu.coeff * curlPair frequencies value.1 value.1 =
      pairing frequencies load value := by
  dsimp only
  let value := physicalResolver frequencies zeroNotMem closed nu advector reality step nonnegative load
  have written := resolver_write (physicalOperator frequencies zeroNotMem closed nu advector reality)
    (pairing frequencies) (pairing_faithful frequencies) (physicalOperator_dissipative _ _ _ _ _ _)
    step nonnegative load
  have read := congrArg (pairing frequencies value) written
  change pairing frequencies value (value - step • physicalOperator frequencies zeroNotMem closed nu advector reality value) =
    pairing frequencies value load at read
  rw [map_sub, map_smul, smul_eq_mul, physicalOperator_pairing, pairing_symmetric frequencies value load] at read
  have self : pairing frequencies value value = ‖coefficients frequencies value‖ ^ 2 := by
    exact real_inner_self_eq_norm_sq (coefficients frequencies value)
  rw [self] at read
  change ‖coefficients frequencies value‖ ^ 2 + step * nu.coeff * curlPair frequencies value.1 value.1 = _
  nlinarith

theorem resolver_curl_bound (frequencies : Finset IntegerWavevector) (zeroNotMem : 0 ∉ frequencies)
    (closed : FiniteModeNegClosed frequencies) (nu : Viscosity) (advector : ComplexVorticityHilbertState)
    (reality : FiniteStateFourierReality advector) (step : ℝ) (positive : 0 < step)
    (load : physicalSpace frequencies) :
    let value := physicalResolver frequencies zeroNotMem closed nu advector reality step positive.le load
    curlPair frequencies value.1 value.1 ≤ negativeMass frequencies load / (step * nu.coeff) ^ 2 := by
  dsimp only
  let value := physicalResolver frequencies zeroNotMem closed nu advector reality step positive.le load
  have energy := resolver_energy frequencies zeroNotMem closed nu advector reality step positive.le load
  have paired := pairing_le frequencies zeroNotMem load value
  have curl_nonnegative : 0 ≤ curlPair frequencies value.1 value.1 := by
    rw [← gradient_norm_sq frequencies zeroNotMem value]
    exact sq_nonneg _
  have load_nonnegative : 0 ≤ negativeMass frequencies load := by
    rw [← negative_norm_sq frequencies zeroNotMem load]
    exact sq_nonneg _
  have scalePositive : 0 < step * nu.coeff := mul_pos positive nu.coeff_pos
  change curlPair frequencies value.1 value.1 ≤ _
  by_cases zero : curlPair frequencies value.1 value.1 = 0
  · rw [zero]
    exact div_nonneg load_nonnegative (sq_nonneg _)
  have curlPositive := lt_of_le_of_ne curl_nonnegative (Ne.symm zero)
  have rootBound : (step * nu.coeff) * Real.sqrt (curlPair frequencies value.1 value.1) ≤
      Real.sqrt (negativeMass frequencies load) := by
    by_contra larger
    have obstruction := mul_pos (sub_pos.mpr (lt_of_not_ge larger)) (Real.sqrt_pos.2 curlPositive)
    have square := Real.sq_sqrt curl_nonnegative
    change ‖coefficients frequencies value‖ ^ 2 + step * nu.coeff * curlPair frequencies value.1 value.1 = _ at energy
    nlinarith [sq_nonneg ‖coefficients frequencies value‖]
  have squared := pow_le_pow_left₀ (mul_nonneg scalePositive.le (Real.sqrt_nonneg _)) rootBound 2
  rw [mul_pow, Real.sq_sqrt curl_nonnegative, Real.sq_sqrt load_nonnegative] at squared
  apply (le_div_iff₀ (sq_pos_of_pos scalePositive)).mpr
  simpa only [mul_comm] using squared

theorem resolver_norm_bound (frequencies : Finset IntegerWavevector) (zeroNotMem : 0 ∉ frequencies)
    (closed : FiniteModeNegClosed frequencies) (nu : Viscosity) (advector : ComplexVorticityHilbertState)
    (reality : FiniteStateFourierReality advector) (step : ℝ) (positive : 0 < step)
    (load : physicalSpace frequencies) :
    let value := physicalResolver frequencies zeroNotMem closed nu advector reality step positive.le load
    ‖coefficients frequencies value‖ ^ 2 ≤ negativeMass frequencies load / (4 * step * nu.coeff) := by
  dsimp only
  let value := physicalResolver frequencies zeroNotMem closed nu advector reality step positive.le load
  have paid : ‖coefficients frequencies value‖ ^ 2 + step * nu.coeff * curlPair frequencies value.1 value.1 ≤
      Real.sqrt (negativeMass frequencies load) * Real.sqrt (curlPair frequencies value.1 value.1) :=
    (resolver_energy frequencies zeroNotMem closed nu advector reality step positive.le load).le.trans
      (pairing_le frequencies zeroNotMem load value)
  have curlRoot : Real.sqrt (curlPair frequencies value.1 value.1) ^ 2 = curlPair frequencies value.1 value.1 := by
    apply Real.sq_sqrt
    rw [← gradient_norm_sq frequencies zeroNotMem value]
    exact sq_nonneg _
  have loadRoot : Real.sqrt (negativeMass frequencies load) ^ 2 = negativeMass frequencies load := by
    apply Real.sq_sqrt
    rw [← negative_norm_sq frequencies zeroNotMem load]
    exact sq_nonneg _
  have scalePositive : 0 < 4 * step * nu.coeff := mul_pos (mul_pos (by norm_num) positive) nu.coeff_pos
  have scaled := mul_le_mul_of_nonneg_left paid scalePositive.le
  have young := sq_nonneg (Real.sqrt (negativeMass frequencies load) -
    (2 * step * nu.coeff) * Real.sqrt (curlPair frequencies value.1 value.1))
  rw [sub_sq, mul_pow, loadRoot, curlRoot] at young
  change ‖coefficients frequencies value‖ ^ 2 ≤ _
  apply (le_div_iff₀ scalePositive).mpr
  nlinarith only [scaled, young]

end
end SaturationMonoid.NavierStokes.NativeDualCurlResolvent
