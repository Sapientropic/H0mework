import H0mework.Versions.X.NavierStokes.WindowEnergyPressureSectors.Source
import H0mework.Versions.X.NavierStokes.WindowEnergyHighTransport.Source
import H0mework.Versions.X.NavierStokes.PhysicalReadout.Gradient

set_option autoImplicit false
open scoped BigOperators Topology ENNReal Pointwise
namespace SaturationMonoid.NavierStokes.NativeWindowHighPressureCurrent
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageHilbertCompletion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinInitialConvergence
open ThreeDimensionalVorticityCoefficientPuncturedCanonicalGalerkinTarget
open NativeStressCurlAlgebra NativeHigherTimeJets NativeEndpointVelocityCarrier
open NativeWindowPressureSectors NativeWindowPressureLowInputs NativeUnheatedSexticLatticePower
open NativeWindowHighTransportProduct (Z)
open NativeWindowHighTransportSource (Current vectorRead vectorRead_bound)
noncomputable section

def pressure (value : ComplexVorticityHilbertState) (F : Finset IntegerWavevector) : Z :=
  ∑ p ∈ F, lp.single 2 p ((radical p:ℂ)*stressPressureCoefficient p (mixedFlux value value p))

theorem pressure_row (value : ComplexVorticityHilbertState) (F : Finset IntegerWavevector) (p : IntegerWavevector) :
    pressure value F p = if p ∈ F then (radical p:ℂ)*stressPressureCoefficient p (mixedFlux value value p) else 0 := by
  simp only [pressure,lp.coeFn_sum,Finset.sum_apply,lp.coeFn_single,Finset.sum_pi_single]

theorem pressure_bound (value : ComplexVorticityHilbertState) (zero : value 0=0)
    (regular : NativeUnheatedStressProduct.H1 value) (F : Finset IntegerWavevector) :
    ‖pressure value F‖ ≤ 12*Real.sqrt NativeUnheatedRieszKernel.constant*NativeUnheatedStressProduct.gradientMass value := by
  let state := NativeWindowSobolevProduct.state value value zero zero regular regular
  have rows (p : IntegerWavevector) : pressureSequence state p=(radical p:ℂ)*stressPressureCoefficient p (mixedFlux value value p) := by
    change NativeCofinalStress.stressPressureCLM p (radical p • mixedFlux value value p) = _
    exact (NativeCofinalStress.stressPressureCLM p |>.restrictScalars ℝ).map_smul (radical p) _
  have compare : ‖pressure value F‖ ≤ ‖pressureSequence state‖ := by
    apply lp.norm_mono (by norm_num : (2:ℝ≥0∞) ≠ 0)
    intro p
    rw [pressure_row,rows]
    split_ifs
    · rfl
    · rw [norm_zero]
      exact norm_nonneg _
  exact compare.trans ((pressureSequence_norm state).trans ((NativeWindowSobolevProduct.state_bound value value zero zero regular regular).trans_eq (by ring)))

def finiteCap (F : Finset IntegerWavevector) : ℝ := ∑ p ∈ F, 9*radical p

theorem finiteCap_nonnegative (F : Finset IntegerWavevector) : 0 ≤ finiteCap F :=
  Finset.sum_nonneg fun p _ => by positivity [radical_positive p]

theorem pressure_finite_bound (value : ComplexVorticityHilbertState) (F : Finset IntegerWavevector) :
    ‖pressure value F‖ ≤ finiteCap F*‖value‖^2 := by
  unfold pressure
  apply (norm_sum_le _ _).trans
  have each (p : IntegerWavevector) : ‖(lp.single 2 p ((radical p:ℂ)*stressPressureCoefficient p (mixedFlux value value p)) : Z)‖ ≤ 9*radical p*‖value‖^2 := by
    rw [lp.norm_single (by norm_num),norm_mul,Complex.norm_real,Real.norm_of_nonneg (radical_positive p).le]
    have bound := (pressure_norm p _).trans (NativeWindowFiniteStressConvergence.tensor_majorant (mixedFlux value value p)
      (3*‖value‖*‖value‖) (by positivity) (mixedFlux_norm_le value value p))
    exact (mul_le_mul_of_nonneg_left bound (radical_positive p).le).trans_eq (by ring)
  exact (Finset.sum_le_sum fun p _ => each p).trans_eq (by simp only [finiteCap,Finset.sum_mul])

theorem pressure_continuous (F : Finset IntegerWavevector) : Continuous (fun value => pressure value F) := by
  apply continuous_finsetSum
  intro p _
  have flux : Continuous (fun value : ComplexVorticityHilbertState => mixedFlux value value p) :=
    continuous_pi fun i => continuous_pi fun j => (mixedFluxCLM p i j).continuous.clm_apply continuous_id
  exact (lp.singleContinuousLinearMap ℂ (fun _ : IntegerWavevector => ℂ) 2 p).continuous.comp
    (((NativeCofinalStress.stressPressureCLM p).continuous.comp flux).const_mul _)

def product (value : ComplexVorticityHilbertState) (F : Finset IntegerWavevector) (input : Coordinate) : Z :=
  -NativeWindowHighTransportProduct.product (vectorRead input (complexSharpSupportProjection F value)) (pressure value F)

theorem product_bound (value : ComplexVorticityHilbertState) (F : Finset IntegerWavevector) (input : Coordinate) :
    ‖product value F input‖ ≤ NativeWindowHighTransportProduct.cap*‖value‖*‖pressure value F‖ := by
  rw [product,norm_neg]
  exact (NativeWindowHighTransportProduct.product_bound _ _).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ((vectorRead_bound input _).trans (complexSharpSupportProjection_norm_le F value))
      NativeWindowHighTransportProduct.cap_nonnegative) (norm_nonneg _))

theorem projection_continuous (F : Finset IntegerWavevector) : Continuous (complexSharpSupportProjection F) := by
  have lip : LipschitzWith 1 (complexSharpSupportProjection F) := LipschitzWith.of_dist_le_mul fun first last => by
    simpa only [NNReal.coe_one,one_mul] using complexSharpSupportProjection_dist_le F first last
  exact lip.continuous

theorem product_continuous (F : Finset IntegerWavevector) (input : Coordinate) : Continuous (fun value => product value F input) := by
  apply (NativeWindowHighTransportProduct.product_continuous F F
    ((vectorRead input).continuous.comp (projection_continuous F)) (pressure_continuous F) ?_ ?_).neg
  · intro value p outside
    change complexSharpSupportProjection F value p input=0
    simp [outside]
  · intro value p outside
    rw [pressure_row,if_neg outside]

def scalarRow (value : ComplexVorticityHilbertState) (F : Finset IntegerWavevector) (p : IntegerWavevector) : ℂ :=
  if p ∈ F then stressPressureCoefficient p (mixedFlux value value p) else 0

theorem pressure_decode (value : ComplexVorticityHilbertState) (F : Finset IntegerWavevector) (p : IntegerWavevector) :
    (density 1 p:ℂ)*pressure value F p=scalarRow value F p := by
  rw [pressure_row,scalarRow]
  split_ifs
  · simp only [density,pow_one,Complex.ofReal_inv]
    field_simp [(Complex.ofReal_ne_zero.mpr (radical_positive p).ne')]
  · exact mul_zero _

theorem product_row (value : ComplexVorticityHilbertState) (F : Finset IntegerWavevector) (input : Coordinate) (k : IntegerWavevector) :
    product value F input k = -(density 2 k:ℂ)*∑ q ∈ F,value q input*scalarRow value F (k-q) := by
  have supported (p : IntegerWavevector) (outside : p ∉ F) : vectorRead input (complexSharpSupportProjection F value) p=0 := by
    change complexSharpSupportProjection F value p input=0
    simp [outside]
  change -(NativeWindowHighTransportProduct.product _ _ k) = _
  rw [NativeWindowHighTransportProduct.product_finite_row _ _ F supported,neg_mul]
  congr 2
  apply Finset.sum_congr rfl
  intro q inside
  change complexSharpSupportProjection F value q input*((density 1 (k-q):ℂ)*pressure value F (k-q)) = _
  rw [complexSharpSupportProjection_apply,if_pos inside,pressure_decode]

def rawCurrent (value : ComplexVorticityHilbertState) (F : Finset IntegerWavevector) : Current :=
  fun j output input => (if j=output then product value F input else 0)+(if j=input then product value F output else 0)

theorem rawCurrent_continuous (F : Finset IntegerWavevector) : Continuous (fun value => rawCurrent value F) := by
  apply continuous_pi
  intro j
  apply continuous_pi
  intro output
  apply continuous_pi
  intro input
  unfold rawCurrent
  split_ifs
  · exact (product_continuous F input).add (product_continuous F output)
  · exact (product_continuous F input).add continuous_const
  · exact continuous_const.add (product_continuous F output)
  · exact continuous_const

theorem rawCurrent_bound (value : ComplexVorticityHilbertState) (F : Finset IntegerWavevector) :
    ‖rawCurrent value F‖ ≤ 2*NativeWindowHighTransportProduct.cap*‖value‖*‖pressure value F‖ := by
  have nonnegative : 0 ≤ NativeWindowHighTransportProduct.cap*‖value‖*‖pressure value F‖ := by positivity [NativeWindowHighTransportProduct.cap_nonnegative]
  have total0 : 0 ≤ 2*NativeWindowHighTransportProduct.cap*‖value‖*‖pressure value F‖ := by nlinarith only [nonnegative]
  apply (pi_norm_le_iff_of_nonneg total0).mpr
  intro j
  apply (pi_norm_le_iff_of_nonneg total0).mpr
  intro output
  apply (pi_norm_le_iff_of_nonneg total0).mpr
  intro input
  unfold rawCurrent
  have first : ‖if j=output then product value F input else 0‖ ≤ NativeWindowHighTransportProduct.cap*‖value‖*‖pressure value F‖ := by
    split_ifs
    · exact product_bound value F input
    · simpa only [norm_zero] using nonnegative
  have last : ‖if j=input then product value F output else 0‖ ≤ NativeWindowHighTransportProduct.cap*‖value‖*‖pressure value F‖ := by
    split_ifs
    · exact product_bound value F output
    · simpa only [norm_zero] using nonnegative
  exact (norm_add_le _ _).trans ((add_le_add first last).trans_eq (by ring))

def tensorRow (value : ComplexVorticityHilbertState) (F : Finset IntegerWavevector) (k : IntegerWavevector) (output input : Coordinate) : ℂ :=
  ∑ q ∈ F, if k-q ∈ F then
    force value value (k-q) output*value q input+force value value (k-q) input*value q output else 0

def strainRow (value : ComplexVorticityHilbertState) (F : Finset IntegerWavevector) (k : IntegerWavevector) (output input : Coordinate) : ℂ :=
  ∑ q ∈ F, scalarRow value F (k-q)*(NativePhysicalGradient.multiplier q output*value q input+
    NativePhysicalGradient.multiplier q input*value q output)

theorem multiplier_add (p q : IntegerWavevector) (j : Coordinate) :
    NativePhysicalGradient.multiplier (p+q) j=NativePhysicalGradient.multiplier p j+NativePhysicalGradient.multiplier q j := by
  simp only [NativePhysicalGradient.multiplier,complexWavevector,Pi.add_apply,Int.cast_add,Complex.ofReal_add]
  ring

theorem pressure_decomposition (value : ComplexVorticityHilbertState) (F : Finset IntegerWavevector) (k : IntegerWavevector)
    (output input : Coordinate) :
    tensorRow value F k output input =
      (∑ j : Coordinate,NativePhysicalGradient.multiplier k j*(radical k^2:ℝ)*rawCurrent value F j output input k)+
        strainRow value F k output input := by
  have decode (i : Coordinate) : (radical k^2:ℂ)*product value F i k = -∑ q ∈ F,value q i*scalarRow value F (k-q) := by
    rw [product_row]
    simp only [density,Complex.ofReal_inv,Complex.ofReal_pow]
    field_simp [(Complex.ofReal_ne_zero.mpr (radical_positive k).ne')]
  have divergence : (∑ j : Coordinate,NativePhysicalGradient.multiplier k j*(radical k^2:ℝ)*rawCurrent value F j output input k) =
      NativePhysicalGradient.multiplier k output*((radical k^2:ℂ)*product value F input k)+
        NativePhysicalGradient.multiplier k input*((radical k^2:ℂ)*product value F output k) := by
    have read (j o i : Coordinate) : (if j=o then product value F i else (0:Z)) k = if j=o then product value F i k else 0 := by
      split_ifs <;> rfl
    simp only [rawCurrent,lp.coeFn_add,Pi.add_apply,read,mul_add,Finset.sum_add_distrib,
      mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true,Complex.ofReal_pow]
    ring
  rw [divergence,decode,decode]
  simp only [tensorRow,strainRow,mul_neg,Finset.mul_sum,← Finset.sum_neg_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _
  have add := multiplier_add (k-q) q output
  have add' := multiplier_add (k-q) q input
  rw [sub_add_cancel] at add add'
  rw [add,add',scalarRow]
  split_ifs
  · simp only [force,NativePhysicalGradient.multiplier]
    ring
  · ring

theorem pressure_zero (value : ComplexVorticityHilbertState) (F : Finset IntegerWavevector) (output input : Coordinate) :
    tensorRow value F 0 output input=strainRow value F 0 output input := by
  rw [pressure_decomposition]
  simp [NativePhysicalGradient.multiplier,complexWavevector]

variable {nu : Viscosity}

def velocity (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) : ComplexVorticityHilbertState :=
  wholeVelocity (NativeUnheatedSourceWeightedTail.velocity seed time)

def value (seed : GeneratedWholeRestartCurrent nu) (radius : ℕ) (time : ℝ) : ComplexVorticityHilbertState :=
  high (velocity seed time) (integerWaveFrequencyCube radius)

theorem value_original (seed : GeneratedWholeRestartCurrent nu) (radius : ℕ) (time : ℝ) :
    value seed radius time=wholeVelocity (NativeUnheatedSourceWeightedTail.tail radius (NativeUnheatedSourceWeightedTail.velocity seed time)) := by
  apply lp.ext
  funext k j
  by_cases zero : k=0
  · subst k
    simp [value,high_row,velocity,wholeVelocity_zero]
  · have read (input : NativeResolventCompactness.State) : wholeVelocity input k j=input ⟨k,zero⟩ j := wholeVelocity_nonzero input ⟨k,zero⟩ j
    simp only [value,high,velocity,lp.coeFn_sub,Pi.sub_apply,complexSharpSupportProjection_apply,ite_apply,Pi.zero_apply,read,
      NativeUnheatedSourceWeightedTail.tail,wholeRestartVelocityEndpointGalerkinInitialVelocity_apply,
      wholeRestartModes,puncturedIntegerWaveFrequencyCube,Finset.mem_erase]
    by_cases member : k ∈ integerWaveFrequencyCube radius <;> simp [member,zero]

theorem projected_value_original (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ) :
    complexSharpSupportProjection F (value seed radius time)=NativeWindowHighTransportSource.highVelocity seed F radius time := by
  rw [value_original,NativeWindowHighTransportSource.high_original]

theorem value_bound (seed : GeneratedWholeRestartCurrent nu) (radius : ℕ) (time : ℝ) :
    ‖value seed radius time‖ ≤ NativeUnifiedCompleteSource.budget seed := by
  have highBound : ‖value seed radius time‖ ≤ ‖velocity seed time‖ := by
    apply lp.norm_mono (by norm_num : (2:ℝ≥0∞) ≠ 0)
    intro k
    rw [value,high_row]
    split_ifs <;> simp
  exact highBound.trans ((wholeVelocity_norm_le _).trans (NativeUnheatedSourceWeightedTail.velocity_bound seed time))

theorem value_measurable (seed : GeneratedWholeRestartCurrent nu) (radius : ℕ) :
    AEStronglyMeasurable (value seed radius) (volume : Measure ℝ) := by
  have source := wholeVelocityCLM.continuous.comp_aestronglyMeasurable (NativeUnheatedSourceWeightedTail.velocity_measurable seed)
  exact (continuous_id.sub (projection_continuous (integerWaveFrequencyCube radius))).comp_aestronglyMeasurable source

def current (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ) : Current :=
  rawCurrent (value seed radius time) F

def cap (seed : GeneratedWholeRestartCurrent nu) : ℝ :=
  24*NativeWindowHighTransportProduct.cap*Real.sqrt NativeUnheatedRieszKernel.constant*NativeUnifiedCompleteSource.budget seed

theorem cap_nonnegative (seed : GeneratedWholeRestartCurrent nu) : 0 ≤ cap seed := by
  have B0 := (norm_nonneg _).trans (NativeUnifiedCompleteSource.source_bound seed 0)
  unfold cap
  positivity [NativeWindowHighTransportProduct.cap_nonnegative]

theorem current_bound_ae (seed : GeneratedWholeRestartCurrent nu) : ∀ᵐ time : ℝ,0 ≤ time → ∀ F radius,
    ‖current seed F radius time‖ ≤ cap seed*gradientTail seed (integerWaveFrequencyCube radius) time := by
  filter_upwards [NativeUnheatedSourceGradient.physical_H1_ae seed] with time regular nonnegative F radius
  have raw : NativeUnheatedStressProduct.H1 (velocity seed time) := regular nonnegative
  have h : NativeUnheatedStressProduct.H1 (value seed radius time) := high_H1 _ raw _
  have zero : value seed radius time 0=0 := high_zero _ (wholeVelocity_zero _) _
  have same : NativeUnheatedStressProduct.gradientMass (value seed radius time)=gradientTail seed (integerWaveFrequencyCube radius) time := by
    rw [gradientTail_original seed _ time nonnegative,NativeUnheatedSourceQuadraticApprox.physicalSource,dif_pos nonnegative]
    rfl
  have pressureBound := pressure_bound (value seed radius time) zero h F
  rw [same] at pressureBound
  have paid := rawCurrent_bound (value seed radius time) F
  apply paid.trans
  have small := value_bound seed radius time
  have B0 := (norm_nonneg _).trans small
  calc
    _ ≤ 2*NativeWindowHighTransportProduct.cap*NativeUnifiedCompleteSource.budget seed*
        (12*Real.sqrt NativeUnheatedRieszKernel.constant*gradientTail seed (integerWaveFrequencyCube radius) time) := by
      gcongr <;> positivity [NativeWindowHighTransportProduct.cap_nonnegative,gradientTail_nonnegative seed (integerWaveFrequencyCube radius) time]
    _ = _ := by unfold cap; ring

theorem current_measurable (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ) :
    AEStronglyMeasurable (current seed F radius) (volume : Measure ℝ) :=
  (rawCurrent_continuous F).comp_aestronglyMeasurable (value_measurable seed radius)

theorem current_finite_bound (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ) :
    ‖current seed F radius time‖ ≤ 2*NativeWindowHighTransportProduct.cap*finiteCap F*(NativeUnifiedCompleteSource.budget seed)^3 := by
  apply (rawCurrent_bound (value seed radius time) F).trans
  have first := value_bound seed radius time
  have B0 := (norm_nonneg _).trans first
  have last := pressure_finite_bound (value seed radius time) F
  have p0 := NativeWindowHighTransportProduct.cap_nonnegative
  have f0 := finiteCap_nonnegative F
  have last' : ‖pressure (value seed radius time) F‖ ≤ finiteCap F*(NativeUnifiedCompleteSource.budget seed)^2 :=
    last.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) first 2) f0)
  calc
    _ ≤ 2*NativeWindowHighTransportProduct.cap*NativeUnifiedCompleteSource.budget seed*(finiteCap F*(NativeUnifiedCompleteSource.budget seed)^2) := by gcongr
    _ = _ := by ring

theorem current_integrable (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ) (start finish : ℝ) :
    Integrable (current seed F radius) (volume.restrict (Icc start finish)) :=
  (integrable_const (2*NativeWindowHighTransportProduct.cap*finiteCap F*(NativeUnifiedCompleteSource.budget seed)^3)).mono'
    (current_measurable seed F radius).restrict (Eventually.of_forall (current_finite_bound seed F radius))

theorem current_locallyIntegrable (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ) :
    LocallyIntegrable (current seed F radius) (volume : Measure ℝ) := by
  apply (continuous_const.locallyIntegrable (f := fun _ : ℝ => (2*NativeWindowHighTransportProduct.cap*finiteCap F*(NativeUnifiedCompleteSource.budget seed)^3 : ℝ))).mono
    (current_measurable seed F radius)
  filter_upwards with time
  exact (current_finite_bound seed F radius time).trans (le_abs_self _)

open SourceGeneratedNativeResponseDisposition
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem value_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (radius : ℕ) (time : ℝ) (nonnegative : 0 ≤ time) :
    value seed radius (step.2.clockAdvance+time)=value step.1 radius time := by
  unfold value velocity NativeUnheatedSourceWeightedTail.velocity
  rw [NativeUnifiedCompleteSource.source_generated_next seed step generated time nonnegative]

theorem current_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ) (nonnegative : 0 ≤ time) :
    current seed F radius (step.2.clockAdvance+time)=current step.1 F radius time := by
  rw [current,current,value_next seed step generated radius time nonnegative]

end
end SaturationMonoid.NavierStokes.NativeWindowHighPressureCurrent
