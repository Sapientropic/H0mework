import H0mework.NavierStokes.StressMovingSource.ProductWeights
import H0mework.NavierStokes.StressTimeControl.DualCurl
import H0mework.NavierStokes.StressDynamics.ConvectionFlux
import H0mework.NavierStokes.StressMovingSource.Interpolation
import H0mework.NavierStokes.VelocityGalerkin.FiniteObservationTimeTightness

set_option autoImplicit false
open scoped BigOperators

namespace SaturationMonoid.NavierStokes.NativeMovingCriticalProduct

open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportPhysicalInvariantTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientFiniteGalerkinNonlinearNegativeSobolev
open ThreeDimensionalVorticityCoefficientWholeVelocityFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinFiniteObservationTimeTightness
open NativeFiniteActionResolvent NativeTimeJetCarrier NativeHigherTimeJets NativeDualCurlResolvent
open NativeCommonAdvectorAction NativeWholeResolvent
open NativeMovingCriticalProductScalar

noncomputable section

def amplitude (value : ComplexVorticityHilbertState) (wave : IntegerWavevector) : ℝ :=
  ‖euclideanCoordinateRow (value wave)‖

theorem pair_bound (F : Finset IntegerWavevector) (d w : physicalSpace F)
    (k p : IntegerWavevector) (inside : p ∈ F) :
    ‖euclideanCoordinateRow (wholeStateVelocityBilinearPairContribution d.1 w.1 (p, k - p))‖ ≤
      Real.sqrt (integerWaveViscousMultiplier k) * amplitude d.1 p * amplitude w.1 (k - p) := by
  have dotSame : complexWavevector (k - p) ⬝ᵥ d.1 p = complexWavevector k ⬝ᵥ d.1 p := by
    have vectors : complexWavevector k = complexWavevector p + complexWavevector (k - p) := by
      funext coordinate
      simp [complexWavevector]
    rw [vectors, add_dotProduct, physical_transverse d p inside, zero_add]
  have dotBound := complexWavevector_dot_normSq_le k (d.1 p)
  rw [← dotSame] at dotBound
  have squared : ‖euclideanCoordinateRow (wholeStateVelocityBilinearPairContribution d.1 w.1 (p, k - p))‖ ^ 2 ≤
      integerWaveViscousMultiplier k * amplitude d.1 p ^ 2 * amplitude w.1 (k - p) ^ 2 := by
    simp only [amplitude, euclideanCoordinateRow_norm_sq]
    rw [wholeStateVelocityBilinearPairContribution,
      complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq, complexCoordinateVectorNormSq_smul]
    simp only [Complex.normSq_neg, Complex.normSq_mul, Complex.normSq_I, Complex.normSq_ofReal, one_mul]
    have bound := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left dotBound (sq_nonneg (2 * Real.pi)))
      (complexCoordinateVectorNormSq_nonneg (w.1 (k - p)))
    simpa only [complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq, integerWaveViscousMultiplier,
      pow_two, mul_assoc] using bound
  have nonnegative : 0 ≤ integerWaveViscousMultiplier k := by
    exact mul_nonneg (sq_nonneg _) (integerWaveNormSq_nonneg k)
  apply (sq_le_sq₀ (norm_nonneg _) (by dsimp [amplitude]; positivity)).mp
  simpa only [mul_pow, Real.sq_sqrt nonnegative] using squared

theorem row_bound (F : Finset IntegerWavevector) (d w : physicalSpace F)
    (k : IntegerWavevector) :
    ‖euclideanCoordinateRow (wholeStateVelocityBilinearCoefficientAt d.1 w.1 k)‖ ≤
      Real.sqrt (integerWaveViscousMultiplier k) * convolution F (amplitude d.1) (amplitude w.1) k := by
  rw [wholeStateVelocityBilinearCoefficientAt,
    tsum_eq_sum (s := F) (fun p outside => by
      simp [wholeStateVelocityBilinearPairContribution, physical_supported d p outside])]
  rw [euclideanCoordinateRow, WithLp.toLp_sum]
  calc
    _ ≤ ∑ p ∈ F, ‖euclideanCoordinateRow (wholeStateVelocityBilinearPairContribution d.1 w.1 (p, k - p))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ p ∈ F, Real.sqrt (integerWaveViscousMultiplier k) *
        (if k - p ∈ F then amplitude d.1 p * amplitude w.1 (k - p) else 0) := by
      apply Finset.sum_le_sum
      intro p inside
      by_cases second : k - p ∈ F
      · simpa only [if_pos second, mul_assoc] using pair_bound F d w k p inside
      · simp [second, wholeStateVelocityBilinearPairContribution, physical_supported w (k - p) second,
          euclideanCoordinateRow]
    _ = _ := (Finset.mul_sum ..).symm

theorem projected_row_bound (F : Finset IntegerWavevector) (zero : 0 ∉ F)
    (d w : physicalSpace F) (k : IntegerWavevector) (inside : k ∈ F) :
    (integerWaveViscousMultiplier k)⁻¹ *
      ‖euclideanCoordinateRow (projectedDivergenceCLM k (mixedFlux d.1 w.1 k))‖ ^ 2 ≤
      convolution F (amplitude d.1) (amplitude w.1) k ^ 2 := by
  have nonzero : k ≠ 0 := fun same => zero (same ▸ inside)
  have rowSame : projectedDivergenceCLM k (mixedFlux d.1 w.1 k) =
      transverseProjection k (wholeStateVelocityBilinearCoefficientAt d.1 w.1 k) := by
    change transverseProjection k (ThreeDimensionalVorticityCoefficientNativeFluidMedium.nativeFluidStressDivergenceCoefficient _ _) = _
    rw [NativeConvectionFlux.mixed_divergence d.1 w.1
      (fun wave => finiteTransverseSupportProjection_fixed_transverse d.2.1 wave)]
  have projected := transverseProjection_amplitudeSq_le k nonzero
    (wholeStateVelocityBilinearCoefficientAt d.1 w.1 k)
  rw [← euclideanCoordinateRow_norm_sq, ← euclideanCoordinateRow_norm_sq, ← rowSame] at projected
  have squared := pow_le_pow_left₀ (norm_nonneg _) (row_bound F d w k) 2
  have positive := multiplier_pos F zero k inside
  rw [mul_pow, Real.sq_sqrt positive.le] at squared
  calc
    _ ≤ (integerWaveViscousMultiplier k)⁻¹ *
        (integerWaveViscousMultiplier k * convolution F (amplitude d.1) (amplitude w.1) k ^ 2) :=
      mul_le_mul_of_nonneg_left (projected.trans squared) (inv_nonneg.mpr positive.le)
    _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ positive.ne', one_mul]

theorem negative_mass_bound (F : Finset IntegerWavevector) (zero : 0 ∉ F)
    (d w force : physicalSpace F)
    (actual : ∀ k ∈ F, force.1 k = projectedDivergenceCLM k (mixedFlux d.1 w.1 k)) :
    negativeMass F force ≤ NativeMovingCriticalProductWeights.constant *
      mass F NativeMovingCriticalProductWeights.weight (amplitude d.1) *
      mass F NativeMovingCriticalProductWeights.weight (amplitude w.1) := by
  calc
    _ ≤ ∑ k ∈ F, convolution F (amplitude d.1) (amplitude w.1) k ^ 2 := by
      apply Finset.sum_le_sum
      intro k inside
      rw [actual k inside]
      exact projected_row_bound F zero d w k inside
    _ ≤ _ := NativeMovingCriticalProductWeights.convolution_control F zero _ _

theorem amplitude_mass (F : Finset IntegerWavevector) (zero : 0 ∉ F) (value : physicalSpace F) :
    (∑ k ∈ F, amplitude value.1 k ^ 2) = ‖puncturedEuclideanize value.1‖ ^ 2 := by
  rw [physical_norm F zero]
  have same : weightedCoefficients F (fun _ => 1) value = coefficients F value := by
    ext entry
    change (1 : ℝ) • value.1 entry.1.1 entry.2 = value.1 entry.1.1 entry.2
    exact one_smul ℝ _
  have normed := weighted_norm_sq F (fun _ => 1) value
  rw [same] at normed
  simpa only [amplitude, one_pow, one_mul] using normed.symm

theorem gradient_mass (F : Finset IntegerWavevector) (zero : 0 ∉ F) (value : physicalSpace F) :
    (2 * Real.pi) ^ 2 * mass F integerWaveNormSq (amplitude value.1) = curlPair F value.1 value.1 := by
  rw [← gradient_norm_sq F zero, weighted_norm_sq, mass, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k inside
  rw [Real.sq_sqrt (multiplier_pos F zero k inside).le]
  simp only [integerWaveViscousMultiplier, amplitude, mul_assoc]

theorem fractional_mass_le_gradient (F : Finset IntegerWavevector) (zero : 0 ∉ F)
    (value : physicalSpace F) :
    mass F NativeMovingCriticalProductWeights.weight (amplitude value.1) ≤
      mass F integerWaveNormSq (amplitude value.1) := by
  apply Finset.sum_le_sum
  intro k inside
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact Real.rpow_le_self_of_one_le
    (ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity.one_le_integerWaveNormSq k
      (fun same => zero (same ▸ inside))) (by norm_num : (7 / 8 : ℝ) ≤ 1)

theorem physical_product_eighth (F : Finset IntegerWavevector) (zero : 0 ∉ F)
    (d w force : physicalSpace F)
    (actual : ∀ k ∈ F, force.1 k = projectedDivergenceCLM k (mixedFlux d.1 w.1 k)) :
    ((2 * Real.pi) ^ 2) ^ 15 * negativeMass F force ^ 8 ≤
      NativeMovingCriticalProductWeights.constant ^ 8 * ‖puncturedEuclideanize d.1‖ ^ 2 *
        curlPair F d.1 d.1 ^ 7 * curlPair F w.1 w.1 ^ 8 := by
  let md := mass F NativeMovingCriticalProductWeights.weight (amplitude d.1)
  let mw := mass F NativeMovingCriticalProductWeights.weight (amplitude w.1)
  let gd := mass F integerWaveNormSq (amplitude d.1)
  let gw := mass F integerWaveNormSq (amplitude w.1)
  have mw0 : 0 ≤ mw := Finset.sum_nonneg fun k _ =>
    mul_nonneg (NativeMovingCriticalProductWeights.weight_nonnegative k) (sq_nonneg _)
  have gd0 : 0 ≤ gd := Finset.sum_nonneg fun k _ => mul_nonneg (integerWaveNormSq_nonneg k) (sq_nonneg _)
  have norm0 : 0 ≤ negativeMass F force := by
    rw [← negative_norm_sq F zero force]
    exact sq_nonneg _
  have bound := pow_le_pow_left₀ norm0 (negative_mass_bound F zero d w force actual) 8
  rw [mul_pow, mul_pow] at bound
  have interp : md ^ 8 ≤ ‖puncturedEuclideanize d.1‖ ^ 2 * gd ^ 7 := by
    simpa only [amplitude_mass F zero] using NativeMovingCriticalProductWeights.mass_interpolation F (amplitude d.1)
  have transported : mw ^ 8 ≤ gw ^ 8 := pow_le_pow_left₀ mw0 (fractional_mass_le_gradient F zero w) 8
  have combined : negativeMass F force ^ 8 ≤ NativeMovingCriticalProductWeights.constant ^ 8 *
      (‖puncturedEuclideanize d.1‖ ^ 2 * gd ^ 7) * gw ^ 8 := by
    refine bound.trans ?_
    exact mul_le_mul (mul_le_mul_of_nonneg_left interp (pow_nonneg NativeMovingCriticalProductWeights.constant_nonnegative _))
      transported (pow_nonneg mw0 _) (by positivity)
  calc
    _ ≤ ((2 * Real.pi) ^ 2) ^ 15 * (NativeMovingCriticalProductWeights.constant ^ 8 *
        (‖puncturedEuclideanize d.1‖ ^ 2 * gd ^ 7) * gw ^ 8) :=
      mul_le_mul_of_nonneg_left combined (by positivity)
    _ = NativeMovingCriticalProductWeights.constant ^ 8 * ‖puncturedEuclideanize d.1‖ ^ 2 *
        ((2 * Real.pi) ^ 2 * gd) ^ 7 * ((2 * Real.pi) ^ 2 * gw) ^ 8 := by ring
    _ = _ := by rw [gradient_mass F zero d, gradient_mass F zero w]

theorem negative_mass_interpolation (F : Finset IntegerWavevector) (zero : 0 ∉ F)
    (closed : ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger.FiniteModeNegClosed F)
    (d w force : physicalSpace F)
    (actual : ∀ k ∈ F, force.1 k = projectedDivergenceCLM k (mixedFlux d.1 w.1 k)) :
    ((2 * Real.pi) ^ 2) ^ 79 * negativeMass F force ^ 40 ≤
      NativeMovingCriticalProductWeights.constant ^ 40 *
        ‖NativeNegativeFourMomentum.embed (puncturedEuclideanize d.1)‖ ^ 2 *
        curlPair F d.1 d.1 ^ 39 * curlPair F w.1 w.1 ^ 40 := by
  have eighth := physical_product_eighth F zero d w force actual
  have powered := pow_le_pow_left₀ (by positivity : 0 ≤ ((2 * Real.pi) ^ 2) ^ 15 * negativeMass F force ^ 8) eighth 5
  have interpolation := NativeMovingSourceInterpolation.physical_interpolation F zero closed d
  have curlNonnegative (value : physicalSpace F) : 0 ≤ curlPair F value.1 value.1 := by
    rw [← gradient_norm_sq F zero value]
    exact sq_nonneg _
  calc
    _ = ((2 * Real.pi) ^ 2) ^ 4 * (((2 * Real.pi) ^ 2) ^ 15 * negativeMass F force ^ 8) ^ 5 := by ring
    _ ≤ ((2 * Real.pi) ^ 2) ^ 4 *
        (NativeMovingCriticalProductWeights.constant ^ 8 * ‖puncturedEuclideanize d.1‖ ^ 2 *
          curlPair F d.1 d.1 ^ 7 * curlPair F w.1 w.1 ^ 8) ^ 5 :=
      mul_le_mul_of_nonneg_left powered (by positivity)
    _ = NativeMovingCriticalProductWeights.constant ^ 40 *
        (((2 * Real.pi) ^ 2) ^ 4 * ‖puncturedEuclideanize d.1‖ ^ 10) *
          curlPair F d.1 d.1 ^ 35 * curlPair F w.1 w.1 ^ 40 := by ring
    _ ≤ NativeMovingCriticalProductWeights.constant ^ 40 *
        (‖NativeNegativeFourMomentum.embed (puncturedEuclideanize d.1)‖ ^ 2 * curlPair F d.1 d.1 ^ 4) *
          curlPair F d.1 d.1 ^ 35 * curlPair F w.1 w.1 ^ 40 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left interpolation (by positivity))
          (pow_nonneg (curlNonnegative d) _)) (pow_nonneg (curlNonnegative w) _)
    _ = _ := by ring

end
end SaturationMonoid.NavierStokes.NativeMovingCriticalProduct
