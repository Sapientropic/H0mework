import H0mework.Versions.X.NavierStokes.SourceUnheated.StressProduct
import H0mework.Versions.X.NavierStokes.SourceUnheated.WindowGradient

set_option autoImplicit false
open scoped BigOperators Topology ENNReal Convolution
namespace SaturationMonoid.NavierStokes.NativeUnheatedWindowStress
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageHilbertCompletion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open NativeCompleteStressCarrier NativeCompleteStressAction NativeEndpointVelocityCarrier
open NativeHigherTimeJets NativeUnheatedStressProduct NativeForwardWindowJets
open NativeUnheatedWindowJensen
noncomputable section
variable {nu : Viscosity}

def projection (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (time : ℝ) :=
  complexSharpSupportProjection F (wholeVelocity (NativeAbsoluteEventualControl.velocity seed time))

theorem projection_continuous (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) :
    Continuous (projection seed F) := by
  have row (wave : IntegerWavevector) : Continuous (fun time => wholeVelocity (NativeAbsoluteEventualControl.velocity seed time) wave) := by
    by_cases zero : wave = 0
    · subst wave; simp only [wholeVelocity_zero]; exact continuous_const
    · apply continuous_pi
      intro coordinate
      simp only [wholeVelocity_nonzero _ ⟨wave, zero⟩ coordinate]
      exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Coordinate => ℂ) coordinate).continuous.comp
        (NativeFiniteMacroGlobal.coordinate_continuous (NativeEventualTailControl.terminal seed) ⟨wave, zero⟩)
  have same : projection seed F = fun time => ∑ wave ∈ F,
      lp.single 2 wave (wholeVelocity (NativeAbsoluteEventualControl.velocity seed time) wave) :=
    funext fun _ => (sum_single_eq_complexSharpSupportProjection _ _).symm
  rw [same]
  exact continuous_finsetSum _ fun wave _ =>
    (lp.singleContinuousLinearMap ℝ (fun _ : IntegerWavevector => ComplexCoordinateVector) 2 wave).continuous.comp (row wave)

theorem mass_band (F : Finset IntegerWavevector) (value : WholeRestartVelocityEndpointState) :
    gradientMass (complexSharpSupportProjection F (wholeVelocity value)) =
      NativeUnheatedBandGradient.band (F.subtype (fun wave => wave ≠ 0)) value := by
  classical
  rw [projection_mass, NativeUnheatedBandGradient.band]
  have same (wave : NonzeroIntegerWavevector) : density (wholeVelocity value) wave.1 = integerWaveNormSq wave.1 * ‖value wave‖ ^ 2 := by
    rw [density, amplitude, euclideanCoordinateRow_norm_sq, NativeUnheatedWindowGradient.whole_row_mass]
  simp_rw [← same]
  calc
    _ = ∑ wave ∈ F with wave ≠ 0, density (wholeVelocity value) wave := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro wave _
      by_cases zero : wave = 0
      · subst wave; simp [density, integerWaveNormSq]
      · simp [zero]
    _ = _ := by
      simpa only using! (Finset.sum_subtype_eq_sum_filter (s := F) (p := fun wave : IntegerWavevector => wave ≠ 0)
        (density (wholeVelocity value))).symm

def finiteStress (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (time : ℝ) : Space :=
  NativeCompleteStressBilinear.mixed (projection seed F time) (projection seed F time)

theorem finiteStress_continuous (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) :
    Continuous (finiteStress seed F) :=
  (NativeCompleteStressBilinear.mixedCLM.continuous.comp (projection_continuous seed F)).clm_apply (projection_continuous seed F)

theorem finiteStress_bound (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (time : ℝ) :
    ‖finiteStress seed F time‖ ≤ NativeCompleteStressBilinear.mixedBound * ‖puncturedWholeVelocityEuclideanState seed.initialState‖ ^ 2 := by
  have bounded : ‖projection seed F time‖ ≤ ‖puncturedWholeVelocityEuclideanState seed.initialState‖ :=
    (complexSharpSupportProjection_norm_le F _).trans ((wholeVelocity_norm_le _).trans (NativeAbsoluteEventualControl.velocity_norm_le seed time))
  apply (NativeCompleteStressBilinear.mixed_norm_le _ _).trans
  rw [pow_two, mul_assoc]
  exact mul_le_mul_of_nonneg_left (mul_self_le_mul_self (norm_nonneg _) bounded) (by unfold NativeCompleteStressBilinear.mixedBound; positivity)

theorem observed_finite_bound (seed : GeneratedWholeRestartCurrent nu) (F observed : Finset IntegerWavevector) (time : ℝ) :
    ‖observeCLM observed (finiteStress seed F time)‖ ≤ 3 * Real.sqrt constant *
      NativeUnheatedBandGradient.band (F.subtype (fun wave => wave ≠ 0)) (NativeAbsoluteEventualControl.velocity seed time) := by
  rw [observeCLM_apply, finiteStress, NativeCompleteStressBilinear.mixed_read]
  have paid := observe_bound observed (projection seed F time)
    (projection_zero F _ (wholeVelocity_zero _)) (projection_H1 F _)
  simpa only [projection, mass_band] using paid

def stress (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ) : NativeFluidStressFourierState :=
  read (jet seed order time).snd

theorem observed_average (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ) (observed : Finset IntegerWavevector) :
    observe observed (stress seed order time) =
      ∫ shift, kernelJet order shift • observeCLM observed (NativeUnifiedCompleteSource.source seed (time-shift)).snd ∂shiftMeasure := by
  let view : FullSpace →L[ℝ] EuclideanSpace ℂ (observed × (Coordinate × Coordinate)) :=
    (observeCLM observed).comp (WithLp.sndL 2 ℝ WholeRestartVelocityEndpointState Space)
  have integrable : Integrable (fun shift : ℝ => kernelJet order shift • NativeUnifiedCompleteSource.source seed (time-shift)) :=
    (kernelJet_compact order).convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ)
      (kernelJet_smooth order).continuous (NativeForwardWindowSource.original_locallyIntegrable seed) time
  change view (∫ shift : ℝ, kernelJet order shift • NativeUnifiedCompleteSource.source seed (time-shift)) = _
  rw [← view.integral_comp_comm integrable]
  simp only [map_smul]
  change (∫ shift : ℝ, kernelJet order shift • observeCLM observed (NativeUnifiedCompleteSource.source seed (time-shift)).snd) = _
  rw [shiftMeasure, ← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards with shift
  by_cases inside : shift ∈ Icc (-2 : ℝ) (-1)
  · simp only [indicator_of_mem inside]
  · have zero : kernelJet order shift = 0 := by
      by_contra nonzero
      exact inside (kernel_support order shift nonzero)
    simp only [indicator_of_notMem inside, zero, zero_smul]

def integrand (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ)
    (F observed : Finset IntegerWavevector) (shift : ℝ) :=
  kernelJet order shift • observeCLM observed (finiteStress seed F (time-shift))

theorem integrand_continuous (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ) (F observed : Finset IntegerWavevector) :
    Continuous (integrand seed order time F observed) :=
  (kernelJet_smooth order).continuous.smul ((observeCLM observed).continuous.comp
    ((finiteStress_continuous seed F).comp (continuous_const.sub continuous_id)))

theorem integral_tendsto (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ) (observed : Finset IntegerWavevector) :
    Tendsto (fun radius => ∫ shift, integrand seed order time (integerWaveFrequencyCube radius) observed shift ∂shiftMeasure)
      atTop (𝓝 (observe observed (stress seed order time))) := by
  rw [observed_average]
  let ceiling := ‖observeCLM observed‖ * (NativeCompleteStressBilinear.mixedBound * ‖puncturedWholeVelocityEuclideanState seed.initialState‖ ^ 2)
  apply tendsto_integral_of_dominated_convergence (fun shift => ‖kernelJet order shift‖ * ceiling)
  · intro radius
    exact (integrand_continuous seed order time _ observed).aestronglyMeasurable
  · exact (((kernelJet_smooth order).continuous.norm).mul_const ceiling).integrableOn_Icc
  · intro radius
    filter_upwards with shift
    rw [integrand, norm_smul]
    exact mul_le_mul_of_nonneg_left (((observeCLM observed).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (finiteStress_bound seed _ _) (norm_nonneg _))) (norm_nonneg _)
  · have sourceSame := (Measure.measurePreserving_sub_left (volume : Measure ℝ) time).quasiMeasurePreserving.ae
      (NativeUnifiedGlobalStressSource.stress_ae seed)
    filter_upwards [ae_restrict_of_ae sourceSame] with shift same
    have field := complexSharpSupportProjection_frequencyCube_tendsto
      (wholeVelocity (NativeAbsoluteEventualControl.velocity seed (time-shift)))
    have continuous : Continuous (fun value : ComplexVorticityHilbertState =>
        kernelJet order shift • observeCLM observed (NativeCompleteStressBilinear.mixed value value)) := by
      exact (continuous_const (y := kernelJet order shift)).smul ((observeCLM observed).continuous.comp
        ((NativeCompleteStressBilinear.mixedCLM.continuous.comp continuous_id).clm_apply continuous_id))
    have equal : NativeCompleteStressBilinear.mixed (wholeVelocity (NativeAbsoluteEventualControl.velocity seed (time-shift)))
        (wholeVelocity (NativeAbsoluteEventualControl.velocity seed (time-shift))) = (NativeUnifiedCompleteSource.source seed (time-shift)).snd := by
      apply read_injective
      rw [NativeCompleteStressBilinear.mixed_read, mixedFlux_diagonal, NativeUnifiedCompleteSource.stress_read, same]
    have actual := continuous.tendsto _ |>.comp field
    simpa only [Function.comp_def, integrand, finiteStress, projection, equal] using actual


def budget (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ) : ℝ :=
  3 * Real.sqrt constant * Real.sqrt (NativeUnheatedWindowGradient.kernelCeiling order) *
    NativeUnheatedGlobalGradient.budget (NativeEventualTailControl.terminal seed) (time+2)

theorem finite_integral_bound (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ) (valid : -1 ≤ time)
    (F observed : Finset IntegerWavevector) :
    ‖∫ shift, integrand seed order time F observed shift ∂shiftMeasure‖ ≤ budget seed order time := by
  let factor := 3 * Real.sqrt constant * Real.sqrt (NativeUnheatedWindowGradient.kernelCeiling order)
  have continuous := NativeUnheatedWindowGradient.shifted_band_continuous seed (F.subtype (fun wave => wave ≠ 0)) time
  have paid := norm_integral_le_of_norm_le (f := integrand seed order time F observed)
    ((continuous.const_mul factor).integrableOn_Icc) (by
    filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Icc] with shift inside
    rw [integrand, norm_smul]
    have kernel : ‖kernelJet order shift‖ ≤ Real.sqrt (NativeUnheatedWindowGradient.kernelCeiling order) :=
      Real.le_sqrt_of_sq_le (by simpa only [Real.norm_eq_abs, sq_abs] using
        NativeUnheatedWindowGradient.kernel_square_le order shift inside)
    have both := mul_le_mul kernel (observed_finite_bound seed F observed (time-shift)) (norm_nonneg _) (Real.sqrt_nonneg _)
    exact both.trans_eq (by dsimp [factor]; ring))
  rw [integral_const_mul] at paid
  exact paid.trans (mul_le_mul_of_nonneg_left
    (NativeUnheatedWindowGradient.shifted_band_integral_bound seed _ time valid) (by dsimp [factor]; positivity))

theorem observed_bound (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ) (valid : -1 ≤ time)
    (observed : Finset IntegerWavevector) :
    ‖observe observed (stress seed order time)‖ ≤ budget seed order time :=
  le_of_tendsto (integral_tendsto seed order time observed).norm
    (Eventually.of_forall fun radius => finite_integral_bound seed order time valid (integerWaveFrequencyCube radius) observed)

theorem stress_summable (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ) (valid : -1 ≤ time) :
    Summable (fun wave => ‖tensor (stress seed order time wave)‖ ^ 2) := by
  apply summable_of_sum_le (fun _ => sq_nonneg _) (c := budget seed order time ^ 2)
  intro observed
  rw [← observe_norm_sq]
  exact pow_le_pow_left₀ (norm_nonneg _) (observed_bound seed order time valid observed) 2

def state (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ) (valid : -1 ≤ time) : Space :=
  ⟨fun wave => tensor (stress seed order time wave), by
    apply memℓp_gen
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using stress_summable seed order time valid⟩

theorem state_row (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ) (valid : -1 ≤ time)
    (wave : IntegerWavevector) (output input : Coordinate) :
    state seed order time valid wave (output, input) = read (jet seed order time).snd wave output input := rfl

theorem state_bound (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ) (valid : -1 ≤ time) :
    ‖state seed order time valid‖ ≤ budget seed order time := by
  have nonnegative : 0 ≤ budget seed order time := (norm_nonneg _).trans (observed_bound seed order time valid ∅)
  apply (sq_le_sq₀ (norm_nonneg _) nonnegative).mp
  have normed := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num) (state seed order time valid)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at normed
  rw [normed]
  apply (stress_summable seed order time valid).tsum_le_of_sum_le
  intro observed
  rw [← observe_norm_sq]
  exact pow_le_pow_left₀ (norm_nonneg _) (observed_bound seed order time valid observed) 2

end
end SaturationMonoid.NavierStokes.NativeUnheatedWindowStress
