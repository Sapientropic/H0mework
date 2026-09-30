import H0mework.Versions.X.NavierStokes.WindowEnergyHighPressure.Current
import H0mework.Versions.X.NavierStokes.WindowEnergyHighTransport.Resolvent

set_option autoImplicit false
open scoped BigOperators Topology ENNReal Convolution
namespace SaturationMonoid.NavierStokes.NativeWindowHighPressureResolvent
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open SourceGeneratedNativeResponseDisposition
open NativeWindowHighPressureCurrent
open NativeWindowHighTransportProduct (Z)
open NativeWindowHighTransportSource (Current)
noncomputable section
variable {nu : Viscosity}

def payment (seed : GeneratedWholeRestartCurrent nu) (radius : ℕ) (horizon : ℝ) : ℝ :=
  cap seed*∫ time in Icc 0 horizon,NativeWindowPressureLowInputs.gradientTail seed (integerWaveFrequencyCube radius) time

theorem integral_bound (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (horizon : ℝ) (nonnegative : 0 ≤ horizon) : (∫ time in Icc 0 horizon,‖current seed F radius time‖) ≤ payment seed radius horizon := by
  rw [payment,← integral_const_mul]
  apply integral_mono_ae (current_integrable seed F radius 0 horizon).norm
    ((NativeWindowPressureLowInputs.gradientTail_integrable seed horizon nonnegative (integerWaveFrequencyCube radius)).const_mul (cap seed))
  filter_upwards [ae_restrict_of_ae (current_bound_ae seed),ae_restrict_mem measurableSet_Icc] with time paid inside
  exact paid inside.1 F radius

theorem payment_tendsto (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    Tendsto (fun radius => payment seed radius horizon) atTop (𝓝 0) := by
  simpa only [payment,mul_zero] using (NativeWindowPressureLowInputs.gradientTail_integral_tendsto seed horizon nonnegative).const_mul (cap seed)

def window (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius order : ℕ) (time : ℝ) : Current :=
  ∫ shift,NativeForwardWindowJets.kernelJet order shift • current seed F radius (time-shift)

theorem window_integrable (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius order : ℕ) (time : ℝ) :
    Integrable (fun shift => NativeForwardWindowJets.kernelJet order shift • current seed F radius (time-shift)) :=
  (NativeForwardWindowJets.kernelJet_compact order).convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (NativeForwardWindowJets.kernelJet_smooth order).continuous (current_locallyIntegrable seed F radius) time

theorem window_bound (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius order : ℕ)
    (time horizon : ℝ) (inside : time ∈ Icc 0 horizon) : ‖window seed F radius order time‖ ≤
      NativeWindowFiniteStressUniform.kernelBound order*payment seed radius (horizon+2) := by
  have h0 : 0 ≤ horizon+2 := by linarith [inside.1,inside.2]
  rw [window,← NativeWindowFiniteStressUniform.average_original order time horizon inside]
  apply (norm_integral_le_integral_norm _).trans
  have paid := current_integrable seed F radius 0 (horizon+2)
  have weighted := NativeWindowFiniteStressUniform.average_integrable order time horizon paid
  apply (integral_mono_ae weighted.norm (paid.norm.const_mul (NativeWindowFiniteStressUniform.kernelBound order))
    (Eventually.of_forall fun sample => by
      dsimp only
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (NativeWindowFiniteStressUniform.kernel_bounded order (time-sample)) (norm_nonneg _))).trans
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left (integral_bound seed F radius (horizon+2) h0)
    (NativeWindowFiniteStressUniform.kernelBound_positive order).le

theorem window_small (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (horizon : ℝ) (nonnegative : 0 ≤ horizon)
    (epsilon : ℝ) (positive : 0 < epsilon) : ∃ low : ℕ,∀ radius ≥ low,∀ F time,time ∈ Icc 0 horizon →
      ‖window seed F radius order time‖ < epsilon := by
  have limit := (payment_tendsto seed (horizon+2) (by linarith)).const_mul (NativeWindowFiniteStressUniform.kernelBound order)
  simp only [mul_zero] at limit
  obtain ⟨low,small⟩ := eventually_atTop.mp (limit.eventually (Iio_mem_nhds positive))
  exact ⟨low,fun radius above F time inside => (window_bound seed F radius order time horizon inside).trans_lt (small radius above)⟩

theorem window_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius order : ℕ) (time : ℝ) :
    HasDerivAt (window seed F radius order) (window seed F radius (order+1) time) time := by
  have : SecondCountableTopologyEither ℝ Current := ⟨Or.inl inferInstance⟩
  have source := (NativeForwardWindowJets.kernelJet_compact order).hasDerivAt_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) ((NativeForwardWindowJets.kernelJet_smooth order).of_le (by simp))
    (current_locallyIntegrable seed F radius) time
  simpa only [window,NativeForwardWindowJets.kernelJet,iteratedDeriv_succ] using! source

def primitive (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius order : ℕ)
    (time : ℝ) (output input : Coordinate) : Z :=
  NativeWindowHighTransportResolvent.resolve nu output input (window seed F radius order time)

theorem primitive_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius order : ℕ)
    (time : ℝ) (output input : Coordinate) :
    HasDerivAt (fun t => primitive seed F radius order t output input) (primitive seed F radius (order+1) time output input) time :=
  ((NativeWindowHighTransportResolvent.resolve nu output input).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt time
    (window_hasDerivAt seed F radius order time)

theorem primitive_small (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (horizon : ℝ) (nonnegative : 0 ≤ horizon)
    (epsilon : ℝ) (positive : 0 < epsilon) : ∃ low : ℕ,∀ radius ≥ low,∀ F time,time ∈ Icc 0 horizon →∀ output input,
      ‖primitive seed F radius order time output input‖ < epsilon := by
  obtain ⟨low,small⟩ := window_small seed order horizon nonnegative
    (epsilon/(3*NativeWindowHighTransportResolvent.cap nu)) (by positivity [NativeWindowHighTransportResolvent.cap_positive nu])
  refine ⟨low,fun radius above F time inside output input => ?_⟩
  apply (NativeWindowHighTransportResolvent.resolve_bound nu output input _).trans_lt
  exact (mul_lt_mul_of_pos_left (small radius above F time inside) (by positivity [NativeWindowHighTransportResolvent.cap_positive nu])).trans_eq
    (by field_simp [(NativeWindowHighTransportResolvent.cap_positive nu).ne'])

theorem primitive_equation (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius order : ℕ)
    (time : ℝ) (output input : Coordinate) (k : IntegerWavevector) :
    (nu.coeff*integerWaveViscousMultiplier k : ℝ) • primitive seed F radius order time output input k =
      ∫ shift,NativeForwardWindowJets.kernelJet order shift •
        (tensorRow (value seed radius (time-shift)) F k output input-strainRow (value seed radius (time-shift)) F k output input) := by
  let observed : Current →L[ℝ] ℂ := (nu.coeff*integerWaveViscousMultiplier k) •
    (lp.evalCLM ℝ (fun _ : IntegerWavevector => ℂ) 2 k).comp ((NativeWindowHighTransportResolvent.resolve nu output input).restrictScalars ℝ)
  change observed (window seed F radius order time) = _
  rw [window,← observed.integral_comp_comm (window_integrable seed F radius order time)]
  apply integral_congr_ae
  filter_upwards with shift
  rw [map_smul]
  congr 1
  change (nu.coeff*integerWaveViscousMultiplier k : ℝ) •
    NativeWindowHighTransportResolvent.resolve nu output input (current seed F radius (time-shift)) k = _
  rw [NativeWindowHighTransportResolvent.viscous_row]
  exact eq_sub_of_add_eq (pressure_decomposition (value seed radius (time-shift)) F k output input).symm

theorem window_next (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius order : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0 ≤ time) :
    window seed F radius order (step.2.clockAdvance+time)=window step.1 F radius order time := by
  unfold window
  apply integral_congr_ae
  filter_upwards with shift
  by_cases zero : NativeForwardWindowJets.kernelJet order shift=0
  · rw [zero,zero_smul,zero_smul]
  · have support := NativeUnheatedWindowJensen.kernel_support order shift zero
    rw [add_sub_assoc,current_next seed step generated F radius (time-shift) (by linarith [support.2])]

theorem primitive_next (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius order : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0 ≤ time) :
    primitive seed F radius order (step.2.clockAdvance+time)=primitive step.1 F radius order time := by
  unfold primitive
  rw [window_next seed F radius order step generated time nonnegative]

end
end SaturationMonoid.NavierStokes.NativeWindowHighPressureResolvent
