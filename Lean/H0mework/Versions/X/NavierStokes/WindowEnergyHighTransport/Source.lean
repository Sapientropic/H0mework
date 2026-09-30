import H0mework.Versions.X.NavierStokes.WindowEnergyHighTransport.Product
import H0mework.Versions.X.NavierStokes.WindowEnergyApproximation.Window
import H0mework.Versions.X.NavierStokes.UnheatedWriterTail.Weighted

set_option autoImplicit false
open scoped BigOperators Topology ENNReal Pointwise
namespace SaturationMonoid.NavierStokes.NativeWindowHighTransportSource
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinInitialConvergence
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageHilbertCompletion
open NativeHigherTimeJets NativeEndpointVelocityCarrier NativeUnheatedSourceWeightedTail
open NativeWindowHighTransportProduct (Z)
noncomputable section
variable {nu : Viscosity}

def vectorRead (j : Coordinate) : ComplexVorticityHilbertState →L[ℂ] Z :=
  lp.mapCLM 2 (fun _ : IntegerWavevector => ContinuousLinearMap.proj j) zero_le_one
    (fun _ => ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun value => by
      simpa only [ContinuousLinearMap.proj_apply,one_mul] using norm_le_pi_norm value j))

def tensorRead (entry : Coordinate × Coordinate) : NativeCompleteStressCarrier.Space →L[ℂ] Z :=
  lp.mapCLM 2 (fun _ : IntegerWavevector => PiLp.proj (𝕜 := ℂ) 2 (fun _ : Coordinate × Coordinate => ℂ) entry)
    zero_le_one (fun _ => ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun value => by
      simpa only [PiLp.proj_apply,one_mul] using PiLp.norm_apply_le value entry))

theorem vectorRead_bound (j : Coordinate) (value : ComplexVorticityHilbertState) : ‖vectorRead j value‖ ≤ ‖value‖ := by
  apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  exact fun k => norm_le_pi_norm (value k) j

theorem tensorRead_bound (entry : Coordinate × Coordinate) (value : NativeCompleteStressCarrier.Space) :
    ‖tensorRead entry value‖ ≤ ‖value‖ := by
  apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  exact fun k => PiLp.norm_apply_le (value k) entry

def highVelocity (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ) :=
  NativeUnheatedWindowStress.projection seed F time-NativeUnheatedWindowStress.projection seed (F∩wholeRestartModes radius) time

theorem high_original (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ) :
    highVelocity seed F radius time = complexSharpSupportProjection F (wholeVelocity (tail radius (velocity seed time))) := by
  classical
  apply lp.ext
  funext wave j
  by_cases zero : wave=0
  · subst wave
    simp [highVelocity,NativeUnheatedWindowStress.projection]
  · have same : NativeAbsoluteEventualControl.velocity seed time=velocity seed time := NativeUnifiedCompleteSource.velocity_read seed time |>.symm
    by_cases inside : wave∈F <;> by_cases low : wave∈wholeRestartModes radius <;>
      simp [highVelocity,NativeUnheatedWindowStress.projection,same,complexSharpSupportProjection_apply,
        wholeVelocity,coefficients,zero,tail,wholeRestartVelocityEndpointGalerkinInitialVelocity_apply,inside,low]

theorem high_bound (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ) :
    ‖highVelocity seed F radius time‖ ≤ ‖tail radius (velocity seed time)‖ := by
  rw [high_original]
  exact (complexSharpSupportProjection_norm_le F _).trans (wholeVelocity_norm_le _)

def component (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (j output input : Coordinate) (time : ℝ) : Z :=
  -NativeWindowHighTransportProduct.product (vectorRead j (highVelocity seed F radius time))
    (tensorRead (output,input) (NativeWindowFiniteStressConvergence.finiteAt seed F time))

theorem component_row (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (j output input : Coordinate) (time : ℝ) (wave : IntegerWavevector) :
    component seed F radius j output input time wave =
      -(NativeUnheatedSexticLatticePower.density 2 wave : ℂ)*∑ p∈F,
        highVelocity seed F radius time p j*
          NativeHigherTimeJets.mixedFlux (NativeUnheatedWindowStress.projection seed F time)
            (NativeUnheatedWindowStress.projection seed F time) (wave-p) output input := by
  classical
  have supported (p : IntegerWavevector) (outside : p∉F) : vectorRead j (highVelocity seed F radius time) p=0 := by
    rw [high_original]
    change complexSharpSupportProjection F _ p j=0
    simp [outside]
  change -(NativeWindowHighTransportProduct.product _ _ wave) = _
  rw [NativeWindowHighTransportProduct.product_finite_row _ _ F supported]
  change -((NativeUnheatedSexticLatticePower.density 2 wave : ℂ)*∑ p∈F,
    highVelocity seed F radius time p j*((NativeUnheatedSexticLatticePower.density 1 (wave-p) : ℂ)*
      NativeWindowFiniteStressConvergence.finiteAt seed F time (wave-p) (output,input))) = _
  rw [neg_mul]
  congr 2
  apply Finset.sum_congr rfl
  intro p _
  rw [NativeWindowFiniteStressConvergence.finiteAt,NativeWindowFiniteStressConvergence.finite_row]
  change highVelocity seed F radius time p j*((NativeUnheatedSexticLatticePower.density 1 (wave-p) : ℂ)*
    ((NativeWindowSobolevStress.quarter (wave-p) : ℂ)*mixedFlux _ _ (wave-p) output input)) = _
  have restore (k : IntegerWavevector) : (NativeUnheatedSexticLatticePower.density 1 k : ℂ)*
      (NativeWindowSobolevStress.quarter k : ℂ)=1 := by
    rw [← Complex.ofReal_mul]
    norm_cast
    change (NativeUnheatedSexticLatticePower.radical k^1)⁻¹*NativeUnheatedSexticLatticePower.radical k=1
    rw [pow_one,inv_mul_cancel₀ (NativeUnheatedSexticLatticePower.radical_positive k).ne']
  rw [← mul_assoc (NativeUnheatedSexticLatticePower.density 1 (wave-p) : ℂ)
    (NativeWindowSobolevStress.quarter (wave-p) : ℂ),restore,one_mul]
  rfl

def cap : ℝ := NativeWindowHighTransportProduct.cap*NativeWindowFiniteStressConvergence.cap

theorem cap_nonnegative : 0 ≤ cap := mul_nonneg NativeWindowHighTransportProduct.cap_nonnegative
  NativeWindowFiniteStressConvergence.cap_nonnegative

theorem component_bound_ae (seed : GeneratedWholeRestartCurrent nu) : ∀ᵐ time : ℝ, 0≤time →
    ∀ F radius j output input, ‖component seed F radius j output input time‖ ≤
      cap*NativeUnheatedSourceGradient.mass seed time*‖tail radius (velocity seed time)‖ := by
  filter_upwards [NativeWindowFiniteStressConvergence.source_bound_ae seed] with time paid nonnegative F radius j output input
  rw [component,norm_neg]
  apply (NativeWindowHighTransportProduct.product_bound _ _).trans
  have first := (vectorRead_bound j _).trans (high_bound seed F radius time)
  have last := (tensorRead_bound (output,input) _).trans ((paid nonnegative).2 F)
  exact (mul_le_mul (mul_le_mul_of_nonneg_left first NativeWindowHighTransportProduct.cap_nonnegative) last
    (norm_nonneg _) (by positivity [NativeWindowHighTransportProduct.cap_nonnegative])).trans_eq (by unfold cap; ring)


theorem component_continuous (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (radius : ℕ) (j output input : Coordinate) : Continuous (component seed F radius j output input) := by
  classical
  have left := (vectorRead j).continuous.comp
    ((NativeUnheatedWindowStress.projection_continuous seed F).sub
      (NativeUnheatedWindowStress.projection_continuous seed (F∩wholeRestartModes radius)))
  have right := (tensorRead (output,input)).continuous.comp (NativeWindowFiniteStressConvergence.finiteAt_continuous seed F)
  apply (NativeWindowHighTransportProduct.product_continuous F (F+F) left right ?_ ?_).neg
  · intro time p outside
    change highVelocity seed F radius time p j=0
    rw [high_original]
    simp [outside]
  · intro time q outside
    change NativeWindowFiniteStressConvergence.finiteAt seed F time q (output,input)=0
    rw [NativeWindowFiniteStressConvergence.finiteAt,NativeWindowFiniteStressConvergence.finite_supported _ F q outside]
    rfl

abbrev Current := Coordinate → Coordinate → Coordinate → Z

def current (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ) : Current :=
  fun j output input => component seed F radius j output input time

theorem current_continuous (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ) :
    Continuous (current seed F radius) :=
  continuous_pi fun j => continuous_pi fun output => continuous_pi fun input => component_continuous seed F radius j output input

theorem current_bound_ae (seed : GeneratedWholeRestartCurrent nu) : ∀ᵐ time : ℝ,0≤time →∀ F radius,
    ‖current seed F radius time‖ ≤ cap*NativeUnheatedSourceGradient.mass seed time*‖tail radius (velocity seed time)‖ := by
  filter_upwards [component_bound_ae seed] with time paid nonnegative F radius
  have nonnegativeBound : 0≤cap*NativeUnheatedSourceGradient.mass seed time*‖tail radius (velocity seed time)‖ := by
    positivity [cap_nonnegative,NativeUnheatedSourceGradient.mass_nonnegative seed time]
  apply (pi_norm_le_iff_of_nonneg nonnegativeBound).mpr
  intro j
  apply (pi_norm_le_iff_of_nonneg nonnegativeBound).mpr
  intro output
  exact (pi_norm_le_iff_of_nonneg nonnegativeBound).mpr (fun input => paid nonnegative F radius j output input)

def payment (seed : GeneratedWholeRestartCurrent nu) (radius : ℕ) (horizon : ℝ) : ℝ :=
  cap*∫ time in Icc 0 horizon,(1+NativeUnheatedSourceGradient.mass seed time)*‖tail radius (velocity seed time)‖

theorem payment_integrable (seed : GeneratedWholeRestartCurrent nu) (radius : ℕ) (horizon : ℝ) (nonnegative : 0≤horizon) :
    Integrable (fun time => (1+NativeUnheatedSourceGradient.mass seed time)*‖tail radius (velocity seed time)‖)
      (volume.restrict (Icc 0 horizon)) := by
  have weight := (integrable_const (1 : ℝ)).add (NativeUnheatedSourceGradient.mass_integrable seed horizon nonnegative)
  have bounded : ∀ time, ‖‖tail radius (velocity seed time)‖‖≤2*NativeUnifiedCompleteSource.budget seed := fun time => by
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact (tail_norm_bound radius _).trans (mul_le_mul_of_nonneg_left (velocity_bound seed time) (by norm_num))
  exact weight.mul_bdd (((tail_continuous radius).comp_aestronglyMeasurable (velocity_measurable seed)).norm.restrict)
    (Eventually.of_forall bounded)

theorem current_integrable (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (horizon : ℝ) (_nonnegative : 0≤horizon) : Integrable (current seed F radius) (volume.restrict (Icc 0 horizon)) :=
  (current_continuous seed F radius).continuousOn.integrableOn_compact isCompact_Icc

theorem integral_bound (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (horizon : ℝ) (nonnegative : 0≤horizon) : (∫ time in Icc 0 horizon,‖current seed F radius time‖) ≤ payment seed radius horizon := by
  rw [payment,← integral_const_mul]
  apply integral_mono_ae (current_integrable seed F radius horizon nonnegative).norm
    ((payment_integrable seed radius horizon nonnegative).const_mul cap)
  filter_upwards [ae_restrict_of_ae (current_bound_ae seed),ae_restrict_mem measurableSet_Icc] with time paid inside
  exact (paid inside.1 F radius).trans (by nlinarith only [mul_nonneg cap_nonnegative (norm_nonneg (tail radius (velocity seed time)))])

theorem payment_tendsto (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon) :
    Tendsto (fun radius => payment seed radius horizon) atTop (𝓝 0) := by
  simpa only [payment,mul_zero] using (source_weighted_tail_tendsto seed horizon nonnegative).const_mul cap

def window (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius order : ℕ) (time : ℝ) : Current :=
  ∫ shift,NativeForwardWindowJets.kernelJet order shift • current seed F radius (time-shift)

theorem window_bound (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius order : ℕ)
    (time horizon : ℝ) (inside : time∈Icc 0 horizon) : ‖window seed F radius order time‖ ≤
      NativeWindowFiniteStressUniform.kernelBound order*payment seed radius (horizon+2) := by
  have h0 : 0≤horizon+2 := by linarith [inside.1,inside.2]
  rw [window,← NativeWindowFiniteStressUniform.average_original order time horizon inside]
  apply (norm_integral_le_integral_norm _).trans
  have paid := current_integrable seed F radius (horizon+2) h0
  have weighted := NativeWindowFiniteStressUniform.average_integrable order time horizon paid
  apply (integral_mono_ae weighted.norm (paid.norm.const_mul (NativeWindowFiniteStressUniform.kernelBound order))
    (Eventually.of_forall fun sample => by
      dsimp only
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (NativeWindowFiniteStressUniform.kernel_bounded order (time-sample)) (norm_nonneg _))).trans
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left (integral_bound seed F radius (horizon+2) h0)
    (NativeWindowFiniteStressUniform.kernelBound_positive order).le

theorem exists_uniform_small (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (horizon : ℝ) (nonnegative : 0≤horizon)
    (epsilon : ℝ) (positive : 0<epsilon) : ∃ low : ℕ,∀ radius≥low,∀ F time,time∈Icc 0 horizon →
      ‖window seed F radius order time‖<epsilon := by
  have limit := (payment_tendsto seed (horizon+2) (by linarith)).const_mul (NativeWindowFiniteStressUniform.kernelBound order)
  simp only [mul_zero] at limit
  obtain ⟨low,small⟩ := (eventually_atTop.mp (limit.eventually (Iio_mem_nhds positive)))
  exact ⟨low,fun radius above F time inside => (window_bound seed F radius order time horizon inside).trans_lt (small radius above)⟩


def read (j output input : Coordinate) (wave : IntegerWavevector) : Current →L[ℝ] ℂ :=
  (lp.evalCLM ℝ (fun _ : IntegerWavevector => ℂ) 2 wave).comp
    ((ContinuousLinearMap.proj input : (Coordinate → Z) →L[ℝ] Z).comp
      ((ContinuousLinearMap.proj output : (Coordinate → Coordinate → Z) →L[ℝ] (Coordinate → Z)).comp
        (ContinuousLinearMap.proj j : Current →L[ℝ] (Coordinate → Coordinate → Z))))

theorem window_row (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius order : ℕ)
    (time horizon : ℝ) (inside : time∈Icc 0 horizon) (j output input : Coordinate) (wave : IntegerWavevector) :
    window seed F radius order time j output input wave =
      ∫ sample in Icc 0 (horizon+2),NativeForwardWindowJets.kernelJet order (time-sample) •
        (-(NativeUnheatedSexticLatticePower.density 2 wave : ℂ)*∑ p∈F,
          highVelocity seed F radius sample p j*mixedFlux (NativeUnheatedWindowStress.projection seed F sample)
            (NativeUnheatedWindowStress.projection seed F sample) (wave-p) output input) := by
  have paid := NativeWindowFiniteStressUniform.average_integrable order time horizon
    (current_integrable seed F radius (horizon+2) (by linarith [inside.1,inside.2]))
  change read j output input wave (window seed F radius order time)=_
  rw [window,← NativeWindowFiniteStressUniform.average_original order time horizon inside,
    NativeWindowFiniteStressUniform.average,← (read j output input wave).integral_comp_comm paid]
  apply integral_congr_ae
  filter_upwards with sample
  rw [map_smul]
  congr 1
  exact component_row seed F radius j output input sample wave

theorem current_next (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0≤time) :
    current seed F radius (step.2.clockAdvance+time)=current step.1 F radius time := by
  have same : NativeAbsoluteEventualControl.velocity seed (step.2.clockAdvance+time)=NativeAbsoluteEventualControl.velocity step.1 time := by
    rw [← NativeUnifiedCompleteSource.velocity_read,← NativeUnifiedCompleteSource.velocity_read,
      NativeUnifiedCompleteSource.source_generated_next seed step generated time nonnegative]
  unfold current component highVelocity NativeUnheatedWindowStress.projection NativeWindowFiniteStressConvergence.finiteAt
  rw [same]

theorem window_next (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius order : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0≤time) :
    window seed F radius order (step.2.clockAdvance+time)=window step.1 F radius order time := by
  unfold window
  apply integral_congr_ae
  filter_upwards with shift
  by_cases zero : NativeForwardWindowJets.kernelJet order shift=0
  · rw [zero,zero_smul,zero_smul]
  · have support := NativeUnheatedWindowJensen.kernel_support order shift zero
    rw [add_sub_assoc,current_next seed F radius step generated (time-shift) (by linarith [support.2])]

end
end SaturationMonoid.NavierStokes.NativeWindowHighTransportSource
