import H0mework.Versions.X.NavierStokes.SourceUnheated.GlobalGradient
import H0mework.Versions.X.NavierStokes.SourceUnheated.WindowJensen

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeUnheatedWindowGradient
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open NativeEndpointVelocityCarrier
open NativeForwardWindowJets NativeUnheatedBandGradient NativeUnheatedGlobalGradient NativeUnheatedWindowJensen
noncomputable section
variable {nu : Viscosity}

def kernelCeiling (order : ℕ) : ℝ :=
  max (sSup ((fun shift => kernelJet order shift ^ 2) '' Icc (-2 : ℝ) (-1))) 0

theorem kernelCeiling_nonnegative (order : ℕ) : 0 ≤ kernelCeiling order := le_max_right _ _

theorem kernel_square_le (order : ℕ) (shift : ℝ) (inside : shift ∈ Icc (-2 : ℝ) (-1)) :
    kernelJet order shift ^ 2 ≤ kernelCeiling order :=
  (le_csSup (isCompact_Icc.image ((kernelJet_smooth order).continuous.pow 2)).bddAbove ⟨shift, inside, rfl⟩).trans
    (le_max_left _ _)

def gradientBudget (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ) : ℝ :=
  kernelCeiling order * NativeUnheatedGlobalGradient.budget (NativeEventualTailControl.terminal seed) (time + 2)

theorem gradientBudget_nonnegative (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ)
    (valid : -1 ≤ time) : 0 ≤ gradientBudget seed order time :=
  mul_nonneg (kernelCeiling_nonnegative order)
    (NativeUnheatedGlobalGradient.budget_nonnegative _ _ (by linarith))

theorem shifted_band_continuous (seed : GeneratedWholeRestartCurrent nu) (waves : Finset NonzeroIntegerWavevector) (time : ℝ) :
    Continuous (fun shift => band waves (NativeAbsoluteEventualControl.velocity seed (time - shift))) :=
  (band_curve_continuous (NativeFiniteMacroGlobal.coordinate_continuous (NativeEventualTailControl.terminal seed)) waves).comp
    (continuous_const.sub continuous_id)

theorem shifted_band_integral_bound (seed : GeneratedWholeRestartCurrent nu) (waves : Finset NonzeroIntegerWavevector)
    (time : ℝ) (valid : -1 ≤ time) :
    (∫ shift, band waves (NativeAbsoluteEventualControl.velocity seed (time - shift)) ∂shiftMeasure) ≤
      NativeUnheatedGlobalGradient.budget (NativeEventualTailControl.terminal seed) (time + 2) := by
  change (∫ shift in Icc (-2 : ℝ) (-1), band waves (NativeAbsoluteEventualControl.velocity seed (time - shift))) ≤ _
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (-2 : ℝ) ≤ -1)]
  rw [intervalIntegral.integral_comp_sub_left (f := fun sample => band waves (NativeAbsoluteEventualControl.velocity seed sample))]
  have first : time - (-1 : ℝ) = time + 1 := by ring
  have last : time - (-2 : ℝ) = time + 2 := by ring
  rw [first, last]
  exact source_interval_bound seed _ _ (by linarith) (by linarith) waves


theorem finite_gradient_bound (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ)
    (valid : -1 ≤ time) (waves : Finset NonzeroIntegerWavevector) :
    band waves (NativeForwardWindowEvolution.velocityJet seed order time) ≤ gradientBudget seed order time := by
  have continuous := shifted_band_continuous seed waves time
  have paid := integral_mono_ae
    ((((kernelJet_smooth order).continuous.pow 2).mul continuous).integrableOn_Icc)
    ((continuous.const_mul (kernelCeiling order)).integrableOn_Icc) (by
      filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Icc] with shift inside
      exact mul_le_mul_of_nonneg_right (kernel_square_le order shift inside)
        (band_nonnegative waves (NativeAbsoluteEventualControl.velocity seed (time - shift))))
  rw [integral_const_mul] at paid
  exact (NativeUnheatedWindowJensen.band_bound seed order time waves).trans
    (paid.trans (mul_le_mul_of_nonneg_left (shifted_band_integral_bound seed waves time valid)
      (kernelCeiling_nonnegative order)))

theorem gradient_summable (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ)
    (valid : -1 ≤ time) :
    Summable (fun wave : NonzeroIntegerWavevector => integerWaveNormSq wave.1 *
      ‖NativeForwardWindowEvolution.velocityJet seed order time wave‖ ^ 2) :=
  summable_of_sum_le (fun wave => mul_nonneg (integerWaveNormSq_nonneg wave.1) (sq_nonneg _))
    (finite_gradient_bound seed order time valid)

theorem gradient_mass_bound (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ)
    (valid : -1 ≤ time) :
    (∑' wave : NonzeroIntegerWavevector, integerWaveNormSq wave.1 *
      ‖NativeForwardWindowEvolution.velocityJet seed order time wave‖ ^ 2) ≤ gradientBudget seed order time :=
  (gradient_summable seed order time valid).tsum_le_of_sum_le (finite_gradient_bound seed order time valid)


theorem whole_row_mass (value : WholeRestartVelocityEndpointState) (wave : NonzeroIntegerWavevector) :
    complexCoordinateAmplitudeSq (wholeVelocity value wave.1) = ‖value wave‖ ^ 2 := by
  have same : euclideanCoordinateRow (wholeVelocity value wave.1) = value wave := by
    apply PiLp.ext
    intro coordinate
    exact wholeVelocity_nonzero value wave coordinate
  rw [← euclideanCoordinateRow_norm_sq, same]

theorem whole_gradient_summable (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ)
    (valid : -1 ≤ time) :
    Summable (fun wave => integerWaveNormSq wave * complexCoordinateAmplitudeSq
      (wholeVelocity (NativeForwardWindowEvolution.velocityJet seed order time) wave)) := by
  let density := fun wave => integerWaveNormSq wave * complexCoordinateAmplitudeSq
    (wholeVelocity (NativeForwardWindowEvolution.velocityJet seed order time) wave)
  have punctured : Summable (fun wave : NonzeroIntegerWavevector => density wave.1) := by
    simpa only [density, whole_row_mass] using gradient_summable seed order time valid
  have supported : Function.support density ⊆ {wave | wave ≠ 0} := by
    intro wave included
    by_contra zero
    have atZero : wave = 0 := not_ne_iff.mp zero
    subst wave
    simp [density, integerWaveNormSq] at included
  exact ((hasSum_subtype_iff_of_support_subset supported).mp punctured.hasSum).summable

theorem whole_gradient_mass_bound (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ)
    (valid : -1 ≤ time) :
    (∑' wave, integerWaveNormSq wave * complexCoordinateAmplitudeSq
      (wholeVelocity (NativeForwardWindowEvolution.velocityJet seed order time) wave)) ≤ gradientBudget seed order time := by
  let density := fun wave => integerWaveNormSq wave * complexCoordinateAmplitudeSq
    (wholeVelocity (NativeForwardWindowEvolution.velocityJet seed order time) wave)
  have supported : Function.support density ⊆ {wave | wave ≠ 0} := by
    intro wave included
    by_contra zero
    have atZero : wave = 0 := not_ne_iff.mp zero
    subst wave
    simp [density, integerWaveNormSq] at included
  change (∑' wave, density wave) ≤ _
  rw [← tsum_subtype_eq_of_support_subset supported]
  simpa only [density, whole_row_mass] using gradient_mass_bound seed order time valid

end
end SaturationMonoid.NavierStokes.NativeUnheatedWindowGradient
