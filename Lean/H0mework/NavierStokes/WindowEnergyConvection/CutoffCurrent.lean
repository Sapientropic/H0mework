import H0mework.NavierStokes.WindowEnergyConvection.CutoffStress
import H0mework.NavierStokes.WindowEnergyHighTransport.Resolvent

set_option autoImplicit false
open scoped BigOperators Topology ENNReal Pointwise
namespace SaturationMonoid.NavierStokes.NativeWindowConvectionCutoffCurrent
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageHilbertCompletion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open SourceGeneratedNativeResponseDisposition
open NativeWindowHighTransportProduct (Z product complexTerm complex_summable)
open NativeWindowHighTransportSource (Current vectorRead tensorRead vectorRead_bound tensorRead_bound)
noncomputable section

theorem product_add_left (L A M : Z) : product (L+A) M=product L M+product A M := by
  apply lp.ext
  funext k
  change (∑' p,complexTerm (L+A) M k p)=(∑' p,complexTerm L M k p)+(∑' p,complexTerm A M k p)
  have point (p) : complexTerm (L+A) M k p=complexTerm L M k p+complexTerm A M k p := by
    simp only [complexTerm,lp.coeFn_add,Pi.add_apply,mul_add,add_mul]
  simp_rw [point]
  exact (complex_summable L M k).of_norm.tsum_add (complex_summable A M k).of_norm

theorem product_add_right (L M A : Z) : product L (M+A)=product L M+product L A := by
  apply lp.ext
  funext k
  change (∑' p,complexTerm L (M+A) k p)=(∑' p,complexTerm L M k p)+(∑' p,complexTerm L A k p)
  have point (p) : complexTerm L (M+A) k p=complexTerm L M k p+complexTerm L A k p := by
    simp only [complexTerm,lp.coeFn_add,Pi.add_apply,mul_add]
  simp_rw [point]
  exact (complex_summable L M k).of_norm.tsum_add (complex_summable L A k).of_norm

theorem product_smul_left (c : ℂ) (L M : Z) : product (c • L) M=c • product L M := by
  apply lp.ext
  funext k
  change (∑' p,complexTerm (c • L) M k p)=c*(∑' p,complexTerm L M k p)
  rw [← tsum_mul_left]
  apply tsum_congr
  intro p
  simp only [complexTerm,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul]
  ring

theorem product_smul_right (c : ℂ) (L M : Z) : product L (c • M)=c • product L M := by
  apply lp.ext
  funext k
  change (∑' p,complexTerm L (c • M) k p)=c*(∑' p,complexTerm L M k p)
  rw [← tsum_mul_left]
  apply tsum_congr
  intro p
  simp only [complexTerm,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul]
  ring

def productLinear : Z →ₗ[ℂ] Z →ₗ[ℂ] Z where
  toFun L :=
    { toFun := product L
      map_add' := product_add_right L
      map_smul' := fun c M => product_smul_right c L M }
  map_add' L A := by ext M : 1; exact product_add_left L A M
  map_smul' c L := by ext M : 1; exact product_smul_left c L M

def productCLM : Z →L[ℂ] Z →L[ℂ] Z :=
  productLinear.mkContinuous₂ NativeWindowHighTransportProduct.cap NativeWindowHighTransportProduct.product_bound

variable {nu : Viscosity}

def component (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (j output input : Coordinate) (time : ℝ) : Z :=
  productCLM (vectorRead output (NativeUnheatedWindowStress.projection seed F time))
    (tensorRead (input,j) (NativeWindowConvectionCutoffStress.value seed F time))+
  productCLM (vectorRead input (NativeUnheatedWindowStress.projection seed F time))
    (tensorRead (output,j) (NativeWindowConvectionCutoffStress.value seed F time))

def current (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (time : ℝ) : Current :=
  fun j output input => component seed F j output input time

def cap (seed : GeneratedWholeRestartCurrent nu) : ℝ :=
  2*NativeWindowHighTransportProduct.cap*NativeUnifiedCompleteSource.budget seed

theorem sourceBudget_nonnegative (seed : GeneratedWholeRestartCurrent nu) : 0 ≤ NativeUnifiedCompleteSource.budget seed :=
  (norm_nonneg _).trans (NativeUnifiedCompleteSource.source_bound seed 0)

theorem cap_nonnegative (seed : GeneratedWholeRestartCurrent nu) : 0 ≤ cap seed := by
  unfold cap
  positivity [NativeWindowHighTransportProduct.cap_nonnegative,sourceBudget_nonnegative seed]

theorem component_bound (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (j output input : Coordinate) (time : ℝ) : ‖component seed F j output input time‖ ≤
      cap seed*‖NativeWindowConvectionCutoffStress.value seed F time‖ := by
  have velocity : ‖NativeUnheatedWindowStress.projection seed F time‖ ≤ NativeUnifiedCompleteSource.budget seed := by
    apply (complexSharpSupportProjection_norm_le F _).trans
    apply (NativeEndpointVelocityCarrier.wholeVelocity_norm_le _).trans
    simpa only [← NativeUnifiedCompleteSource.velocity_read,NativeUnheatedSourceWeightedTail.velocity] using! NativeUnheatedSourceWeightedTail.velocity_bound seed time
  have paid (o i : Coordinate) : ‖productCLM (vectorRead o (NativeUnheatedWindowStress.projection seed F time))
      (tensorRead (i,j) (NativeWindowConvectionCutoffStress.value seed F time))‖ ≤
      NativeWindowHighTransportProduct.cap*NativeUnifiedCompleteSource.budget seed*‖NativeWindowConvectionCutoffStress.value seed F time‖ :=
    (NativeWindowHighTransportProduct.product_bound _ _).trans
      (mul_le_mul (mul_le_mul_of_nonneg_left ((vectorRead_bound o _).trans velocity)
        NativeWindowHighTransportProduct.cap_nonnegative) (tensorRead_bound (i,j) _)
        (norm_nonneg _) (by positivity [NativeWindowHighTransportProduct.cap_nonnegative,sourceBudget_nonnegative seed]))
  exact (norm_add_le _ _).trans ((add_le_add (paid output input) (paid input output)).trans_eq (by unfold cap; ring))

theorem current_bound (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (time : ℝ) :
    ‖current seed F time‖ ≤ cap seed*‖NativeWindowConvectionCutoffStress.value seed F time‖ := by
  have nonnegative := mul_nonneg (cap_nonnegative seed) (norm_nonneg (NativeWindowConvectionCutoffStress.value seed F time))
  exact (pi_norm_le_iff_of_nonneg nonnegative).2 (fun j => (pi_norm_le_iff_of_nonneg nonnegative).2
    (fun output => (pi_norm_le_iff_of_nonneg nonnegative).2 (fun input => component_bound seed F j output input time)))

theorem component_measurable (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (j output input : Coordinate) : AEStronglyMeasurable (component seed F j output input) (volume : Measure ℝ) := by
  have first (o : Coordinate) := ((vectorRead o).continuous.comp (NativeUnheatedWindowStress.projection_continuous seed F)).aestronglyMeasurable (μ := volume)
  have last (i : Coordinate) := (tensorRead (i,j)).continuous.comp_aestronglyMeasurable
    (NativeWindowConvectionCutoffStress.value_locallyIntegrable seed F).aestronglyMeasurable
  exact (productCLM.aestronglyMeasurable_comp₂ (first output) (last input)).add
    (productCLM.aestronglyMeasurable_comp₂ (first input) (last output))

theorem current_measurable (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) :
    AEStronglyMeasurable (current seed F) (volume : Measure ℝ) := by
  have first (o : Coordinate) : Continuous (fun inputs : ComplexVorticityHilbertState × NativeCompleteStressCarrier.Space => vectorRead o inputs.1) :=
    (vectorRead o).continuous.comp continuous_fst
  have last (i j : Coordinate) : Continuous (fun inputs : ComplexVorticityHilbertState × NativeCompleteStressCarrier.Space => tensorRead (i,j) inputs.2) :=
    (tensorRead (i,j)).continuous.comp continuous_snd
  have slot (o i j : Coordinate) : Continuous (fun inputs : ComplexVorticityHilbertState × NativeCompleteStressCarrier.Space =>
      productCLM (vectorRead o inputs.1) (tensorRead (i,j) inputs.2)) :=
    (productCLM.continuous.comp (first o)).clm_apply (last i j)
  have continuous : Continuous (fun inputs : ComplexVorticityHilbertState × NativeCompleteStressCarrier.Space =>
      fun j output input => productCLM (vectorRead output inputs.1) (tensorRead (input,j) inputs.2)+
        productCLM (vectorRead input inputs.1) (tensorRead (output,j) inputs.2)) := by
    apply continuous_pi
    intro j
    apply continuous_pi
    intro output
    apply continuous_pi
    intro input
    exact (slot output input j).add (slot input output j)
  have paired : AEStronglyMeasurable (fun time => (NativeUnheatedWindowStress.projection seed F time,
      NativeWindowConvectionCutoffStress.value seed F time)) (volume : Measure ℝ) :=
    (NativeUnheatedWindowStress.projection_continuous seed F).aestronglyMeasurable.prodMk
      (NativeWindowConvectionCutoffStress.value_locallyIntegrable seed F).aestronglyMeasurable
  simpa only [current,component,Function.comp_def] using! continuous.comp_aestronglyMeasurable paired

theorem current_integrable (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (a b : ℝ) :
    Integrable (current seed F) (volume.restrict (Icc a b)) :=
  ((NativeWindowConvectionCutoffStress.value_integrable_total seed F a b).norm.const_mul (cap seed)).mono'
    (current_measurable seed F).restrict (Eventually.of_forall (current_bound seed F))

theorem current_locallyIntegrable (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) :
    LocallyIntegrable (current seed F) (volume : Measure ℝ) := by
  intro x
  exact ⟨Icc (x-1) (x+1),Icc_mem_nhds (by linarith) (by linarith),current_integrable seed F (x-1) (x+1)⟩

def payment (seed : GeneratedWholeRestartCurrent nu) (radius : ℕ) (horizon : ℝ) : ℝ :=
  cap seed*∫ time in Icc 0 horizon,‖NativeWindowConvectionCutoffStress.value seed (integerWaveFrequencyCube radius) time‖

theorem integral_bound (seed : GeneratedWholeRestartCurrent nu) (radius : ℕ) (horizon : ℝ) :
    (∫ time in Icc 0 horizon,‖current seed (integerWaveFrequencyCube radius) time‖) ≤ payment seed radius horizon := by
  rw [payment,← integral_const_mul]
  exact integral_mono (current_integrable seed _ 0 horizon).norm
    ((NativeWindowConvectionCutoffStress.value_integrable_total seed _ 0 horizon).norm.const_mul (cap seed)) (current_bound seed _)

theorem payment_tendsto (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    Tendsto (fun radius => payment seed radius horizon) atTop (nhds 0) := by
  simpa only [payment,mul_zero] using (NativeWindowConvectionCutoffStress.integral_tendsto seed horizon nonnegative).const_mul (cap seed)

theorem component_row_ae (seed : GeneratedWholeRestartCurrent nu) : ∀ᵐ time : ℝ,0 ≤ time →∀ F j output input k,
    component seed F j output input time k=(NativeUnheatedSexticLatticePower.density 2 k : ℂ)*∑ p∈F,
      (NativeUnheatedWindowStress.projection seed F time p output*NativeWindowConvectionCutoffStress.coefficients seed F time (k-p) input j+
       NativeUnheatedWindowStress.projection seed F time p input*NativeWindowConvectionCutoffStress.coefficients seed F time (k-p) output j) := by
  filter_upwards [NativeWindowConvectionCutoffStress.value_original_ae seed] with time original nonnegative F j output input k
  have row (o i : Coordinate) : productCLM (vectorRead o (NativeUnheatedWindowStress.projection seed F time))
      (tensorRead (i,j) (NativeWindowConvectionCutoffStress.value seed F time)) k=
      (NativeUnheatedSexticLatticePower.density 2 k : ℂ)*∑ p∈F,NativeUnheatedWindowStress.projection seed F time p o*
        NativeWindowConvectionCutoffStress.coefficients seed F time (k-p) i j := by
    have supported (p : IntegerWavevector) (outside : p∉F) : vectorRead o (NativeUnheatedWindowStress.projection seed F time) p=0 := by
      change NativeUnheatedWindowStress.projection seed F time p o=0
      simp [NativeUnheatedWindowStress.projection,complexSharpSupportProjection_apply,outside]
    change product _ _ k=_
    rw [NativeWindowHighTransportProduct.product_finite_row _ _ F supported]
    congr 1
    apply Finset.sum_congr rfl
    intro p _
    change _*((NativeUnheatedSexticLatticePower.density 1 (k-p) : ℂ)*NativeWindowConvectionCutoffStress.value seed F time (k-p) (i,j))=_
    rw [original nonnegative F (k-p)]
    change _*((NativeUnheatedSexticLatticePower.density 1 (k-p) : ℂ)*
      ((NativeWindowSobolevStress.quarter (k-p) : ℂ)*NativeWindowConvectionCutoffStress.coefficients seed F time (k-p) i j))=_
    have restore : (NativeUnheatedSexticLatticePower.density 1 (k-p) : ℂ)*(NativeWindowSobolevStress.quarter (k-p) : ℂ)=1 := by
      rw [← Complex.ofReal_mul]
      norm_cast
      change (NativeUnheatedSexticLatticePower.radical (k-p)^1)⁻¹*NativeUnheatedSexticLatticePower.radical (k-p)=1
      rw [pow_one,inv_mul_cancel₀ (NativeUnheatedSexticLatticePower.radical_positive (k-p)).ne']
    rw [← mul_assoc (NativeUnheatedSexticLatticePower.density 1 (k-p) : ℂ) (NativeWindowSobolevStress.quarter (k-p) : ℂ),restore,one_mul]
    rfl
  simp only [component,lp.coeFn_add,Pi.add_apply]
  rw [row output input,row input output,← mul_add,← Finset.sum_add_distrib]

theorem current_next (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0 ≤ time) :
    current seed F (step.2.clockAdvance+time)=current step.1 F time := by
  have velocity : NativeAbsoluteEventualControl.velocity seed (step.2.clockAdvance+time)=NativeAbsoluteEventualControl.velocity step.1 time := by
    rw [← NativeUnifiedCompleteSource.velocity_read,← NativeUnifiedCompleteSource.velocity_read,
      NativeUnifiedCompleteSource.source_generated_next seed step generated time nonnegative]
  unfold NativeWindowConvectionCutoffCurrent.current NativeWindowConvectionCutoffCurrent.component NativeUnheatedWindowStress.projection
  rw [velocity,NativeWindowConvectionCutoffStress.value_next seed F step generated time nonnegative]

end
end SaturationMonoid.NavierStokes.NativeWindowConvectionCutoffCurrent
