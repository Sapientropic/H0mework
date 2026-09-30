import H0mework.Versions.X.NavierStokes.WindowEnergyConvection.CutoffCurrent
import H0mework.Versions.X.NavierStokes.WindowEnergyConvection.CutoffPhysical

set_option autoImplicit false
open scoped BigOperators Topology ENNReal Convolution Pointwise
namespace SaturationMonoid.NavierStokes.NativeWindowConvectionCutoffWindow
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open SourceGeneratedNativeResponseDisposition
open NativeWindowHighTransportProduct (Z)
open NativeWindowHighTransportSource (Current read)
open NativeWindowConvectionCutoffCurrent
open NativeWindowHighTransportResolvent (resolve resolve_bound)
noncomputable section
variable {nu : Viscosity}

def window (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (order : ℕ) (time : ℝ) : Current :=
  ∫ shift,NativeForwardWindowJets.kernelJet order shift • current seed F (time-shift)

theorem window_integrable (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (order : ℕ) (time : ℝ) :
    Integrable (fun shift => NativeForwardWindowJets.kernelJet order shift • current seed F (time-shift)) (volume : Measure ℝ) := by
  have : SecondCountableTopologyEither ℝ Current := ⟨Or.inl inferInstance⟩
  exact (NativeForwardWindowJets.kernelJet_compact order).convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (NativeForwardWindowJets.kernelJet_smooth order).continuous (current_locallyIntegrable seed F) time

theorem window_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (order : ℕ) (time : ℝ) :
    HasDerivAt (window seed F order) (window seed F (order+1) time) time := by
  have : SecondCountableTopologyEither ℝ Current := ⟨Or.inl inferInstance⟩
  have source := (NativeForwardWindowJets.kernelJet_compact order).hasDerivAt_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) ((NativeForwardWindowJets.kernelJet_smooth order).of_le (by simp))
    (current_locallyIntegrable seed F) time
  simpa only [window,NativeForwardWindowJets.kernelJet,iteratedDeriv_succ] using! source

theorem window_bound (seed : GeneratedWholeRestartCurrent nu) (radius order : ℕ)
    (time horizon : ℝ) (inside : time∈Icc 0 horizon) : ‖window seed (integerWaveFrequencyCube radius) order time‖ ≤
      NativeWindowFiniteStressUniform.kernelBound order*payment seed radius (horizon+2) := by
  rw [window,← NativeWindowFiniteStressUniform.average_original order time horizon inside]
  apply (norm_integral_le_integral_norm _).trans
  have paid := current_integrable seed (integerWaveFrequencyCube radius) 0 (horizon+2)
  have weighted := NativeWindowFiniteStressUniform.average_integrable order time horizon paid
  apply (integral_mono_ae weighted.norm (paid.norm.const_mul (NativeWindowFiniteStressUniform.kernelBound order))
    (Eventually.of_forall fun sample => by
      dsimp only
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (NativeWindowFiniteStressUniform.kernel_bounded order (time-sample)) (norm_nonneg _))).trans
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left (integral_bound seed radius (horizon+2)) (NativeWindowFiniteStressUniform.kernelBound_positive order).le

theorem exists_uniform_small (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (horizon : ℝ) (nonnegative : 0 ≤ horizon)
    (epsilon : ℝ) (positive : 0 < epsilon) : ∃ low : ℕ,∀ radius ≥ low,∀ time,time∈Icc 0 horizon →
      ‖window seed (integerWaveFrequencyCube radius) order time‖<epsilon := by
  have limit := (payment_tendsto seed (horizon+2) (by linarith)).const_mul (NativeWindowFiniteStressUniform.kernelBound order)
  simp only [mul_zero] at limit
  obtain ⟨low,small⟩ := eventually_atTop.mp (limit.eventually (Iio_mem_nhds positive))
  exact ⟨low,fun radius above time inside => (window_bound seed radius order time horizon inside).trans_lt (small radius above)⟩

def primitive (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (order : ℕ)
    (time : ℝ) (output input : Coordinate) : Z := resolve nu output input (window seed F order time)

theorem primitive_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (order : ℕ)
    (time : ℝ) (output input : Coordinate) : HasDerivAt (fun t => primitive seed F order t output input)
      (primitive seed F (order+1) time output input) time :=
  ((resolve nu output input).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt time (window_hasDerivAt seed F order time)

theorem primitive_small (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (horizon : ℝ) (nonnegative : 0 ≤ horizon)
    (epsilon : ℝ) (positive : 0 < epsilon) : ∃ low : ℕ,∀ radius ≥ low,∀ time,time∈Icc 0 horizon →∀ output input,
      ‖primitive seed (integerWaveFrequencyCube radius) order time output input‖<epsilon := by
  obtain ⟨low,small⟩ := exists_uniform_small seed order horizon nonnegative
    (epsilon/(3*NativeWindowHighTransportResolvent.cap nu)) (by positivity [NativeWindowHighTransportResolvent.cap_positive nu])
  refine ⟨low,fun radius above time inside output input => ?_⟩
  apply (resolve_bound nu output input _).trans_lt
  exact (mul_lt_mul_of_pos_left (small radius above time inside)
    (by positivity [NativeWindowHighTransportResolvent.cap_positive nu])).trans_eq (by field_simp [(NativeWindowHighTransportResolvent.cap_positive nu).ne'])

theorem window_fourier (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (closed : ∀ k,k∈F →waveNeg k∈F) (order : ℕ) (time horizon : ℝ) (inside : time∈Icc 0 horizon)
    (j output input : Coordinate) (k : IntegerWavevector) : window seed F order time j output input k=
      ∫ sample in Icc 0 (horizon+2),NativeForwardWindowJets.kernelJet order (time-sample) •
        ((NativeUnheatedSexticLatticePower.density 2 k : ℂ)*NativeWindowFiniteGramFourier.fourierRead k
          (NativeWindowConvectionCutoffPhysical.current seed F sample j output input)) := by
  have paid := NativeWindowFiniteStressUniform.average_integrable order time horizon (current_integrable seed F 0 (horizon+2))
  change read j output input k (window seed F order time)=_
  rw [window,← NativeWindowFiniteStressUniform.average_original order time horizon inside,
    NativeWindowFiniteStressUniform.average,← (read j output input k).integral_comp_comm paid]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (NativeWindowConvectionCutoffPhysical.current_fourier_ae seed F closed),
    ae_restrict_mem measurableSet_Icc] with sample original member
  rw [map_smul]
  exact congrArg (fun value : ℂ => NativeForwardWindowJets.kernelJet order (time-sample) • value)
    (original member.1 j output input k)

theorem raw_viscous_original_ae (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (closed : ∀ k,k∈F →waveNeg k∈F) : ∀ᵐ sample : ℝ,0 ≤ sample →∀ output input k,
    (nu.coeff*integerWaveViscousMultiplier k : ℝ) • resolve nu output input (current seed F sample) k=
      NativeWindowFiniteGramFourier.fourierRead k (NativeWindowRetainedAction.convectionPair seed F output input sample+
        NativeWindowConvectionCutoffPhysical.strain seed F sample output input) := by
  filter_upwards [NativeWindowConvectionCutoffPhysical.current_fourier_ae seed F closed]
    with sample original nonnegative output input k
  rw [NativeWindowHighTransportResolvent.viscous_row,
    NativeWindowConvectionCutoffPhysical.convection_pair seed F sample nonnegative output input,sub_add_cancel,map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [original nonnegative j output input k,NativeWindowConvectionCutoffPhysical.currentGradient_fourier]
  have restore : ((NativeUnheatedSexticLatticePower.radical k^2 : ℝ) : ℂ)*
      (NativeUnheatedSexticLatticePower.density 2 k : ℂ)=1 := by
    rw [← Complex.ofReal_mul]
    norm_cast
    exact mul_inv_cancel₀ (pow_ne_zero 2 (NativeUnheatedSexticLatticePower.radical_positive k).ne')
  calc
    _ = NativePhysicalGradient.multiplier k j*
        (((NativeUnheatedSexticLatticePower.radical k^2 : ℝ) : ℂ)*(NativeUnheatedSexticLatticePower.density 2 k : ℂ))*
          NativeWindowFiniteGramFourier.fourierRead k (NativeWindowConvectionCutoffPhysical.current seed F sample j output input) := by ring
    _ = _ := by rw [restore,mul_one]

theorem primitive_source (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (closed : ∀ k,k∈F →waveNeg k∈F) (order : ℕ) (time horizon : ℝ) (inside : time∈Icc 0 horizon)
    (output input : Coordinate) (k : IntegerWavevector) :
    (nu.coeff*integerWaveViscousMultiplier k : ℝ) • primitive seed F order time output input k=
      ∫ sample in Icc 0 (horizon+2),NativeForwardWindowJets.kernelJet order (time-sample) •
        NativeWindowFiniteGramFourier.fourierRead k (NativeWindowRetainedAction.convectionPair seed F output input sample+
          NativeWindowConvectionCutoffPhysical.strain seed F sample output input) := by
  let observer : Current →L[ℝ] ℂ := (nu.coeff*integerWaveViscousMultiplier k) •
    (lp.evalCLM ℝ (fun _ : IntegerWavevector => ℂ) 2 k).comp ((resolve nu output input).restrictScalars ℝ)
  have paid := NativeWindowFiniteStressUniform.average_integrable order time horizon (current_integrable seed F 0 (horizon+2))
  change observer (window seed F order time)=_
  rw [window,← NativeWindowFiniteStressUniform.average_original order time horizon inside,
    NativeWindowFiniteStressUniform.average,← observer.integral_comp_comm paid]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (raw_viscous_original_ae seed F closed),ae_restrict_mem measurableSet_Icc] with sample original member
  rw [map_smul]
  exact congrArg (fun value : ℂ => NativeForwardWindowJets.kernelJet order (time-sample) • value) (original member.1 output input k)

theorem window_next (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (order : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0 ≤ time) :
    window seed F order (step.2.clockAdvance+time)=window step.1 F order time := by
  unfold window
  apply integral_congr_ae
  filter_upwards with shift
  by_cases zero : NativeForwardWindowJets.kernelJet order shift=0
  · rw [zero,zero_smul,zero_smul]
  · have support := NativeUnheatedWindowJensen.kernel_support order shift zero
    rw [add_sub_assoc,current_next seed F step generated (time-shift) (by linarith [support.2])]

theorem primitive_next (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (order : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0 ≤ time) :
    primitive seed F order (step.2.clockAdvance+time)=primitive step.1 F order time := by
  funext output input
  unfold primitive
  rw [window_next seed F order step generated time nonnegative]

end
end SaturationMonoid.NavierStokes.NativeWindowConvectionCutoffWindow
