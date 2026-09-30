import H0mework.NavierStokes.WindowEnergyHighTransport.Source
import H0mework.NavierStokes.PhysicalReadout.Gradient

set_option autoImplicit false
open scoped BigOperators Topology ENNReal Convolution Pointwise
namespace SaturationMonoid.NavierStokes.NativeWindowHighTransportResolvent
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open SourceGeneratedNativeResponseDisposition NativePhysicalGradient
open NativeUnheatedSexticLatticePower
open NativeWindowHighTransportProduct (Z)
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open NativeWindowHighTransportSource (Current)
noncomputable section

/-- The original spatial viscous inverse applied to the divergence of the Hminus1 encoded current. -/
def factor (nu : Viscosity) (j : Coordinate) (k : IntegerWavevector) : ℂ :=
  (nu.coeff*integerWaveViscousMultiplier k)⁻¹ • (multiplier k j*(radical k^2 : ℝ))

def cap (nu : Viscosity) : ℝ := 2/(nu.coeff*(2*Real.pi))
theorem cap_positive (nu : Viscosity) : 0<cap nu := by unfold cap; positivity [nu.coeff_pos]

theorem numerator_bound (j : Coordinate) (k : IntegerWavevector) (nonzero : k≠0) :
    ‖multiplier k j‖*radical k^2  ≤  2*(2*Real.pi)*integerWaveNormSq k := by
  apply (sq_le_sq₀ (by positivity [radical_positive k]) (by positivity [integerWaveNormSq_nonneg k])).mp
  rw [mul_pow,← pow_mul,multiplier_norm_sq,show (2 : ℕ)*2=4 by rfl,radical_fourth]
  have coordinate : (k j : ℝ)^2 ≤ integerWaveNormSq k := Finset.single_le_sum (fun i _ => sq_nonneg (k i : ℝ)) (Finset.mem_univ j)
  have massBound : mass k ≤ 2*integerWaveNormSq k := by unfold mass; linarith [one_le_integerWaveNormSq k nonzero]
  have paid := mul_le_mul coordinate massBound (mass_positive k).le (integerWaveNormSq_nonneg k)
  have scaled := mul_le_mul_of_nonneg_left paid (sq_nonneg (2*Real.pi))
  nlinarith only [scaled,mul_nonneg (sq_nonneg (2*Real.pi)) (sq_nonneg (integerWaveNormSq k))]

theorem factor_bound (nu : Viscosity) (j : Coordinate) (k : IntegerWavevector) : ‖factor nu j k‖ ≤ cap nu := by
  by_cases zero : k=0
  · subst k
    simp only [factor,multiplier,complexWavevector,Pi.zero_apply,Int.cast_zero,Complex.ofReal_zero,mul_zero,zero_mul,smul_zero,norm_zero]
    exact (cap_positive nu).le
  · have positive : 0<nu.coeff*integerWaveViscousMultiplier k := by
      unfold integerWaveViscousMultiplier
      positivity [nu.coeff_pos,integerWaveNormSq_pos zero]
    rw [factor,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr positive.le),norm_mul,Complex.norm_real,
      Real.norm_of_nonneg (sq_nonneg _)]
    have same : (nu.coeff*integerWaveViscousMultiplier k)⁻¹*(‖multiplier k j‖*radical k^2)  ≤ 
        (nu.coeff*integerWaveViscousMultiplier k)⁻¹*(2*(2*Real.pi)*integerWaveNormSq k) :=
      mul_le_mul_of_nonneg_left (numerator_bound j k zero) (inv_nonneg.mpr positive.le)
    apply same.trans_eq
    unfold cap integerWaveViscousMultiplier
    field_simp [nu.coeff_pos.ne',Real.pi_ne_zero,(integerWaveNormSq_pos zero).ne']

def map (nu : Viscosity) (j : Coordinate) : Z →L[ℂ] Z :=
  lp.mapCLM 2 (fun k : IntegerWavevector => factor nu j k • ContinuousLinearMap.id ℂ ℂ)
    (cap_positive nu).le (fun k => ContinuousLinearMap.opNorm_le_bound _ (cap_positive nu).le (fun value => by
      change ‖factor nu j k*value‖ ≤ _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (factor_bound nu j k) (norm_nonneg _)))

theorem map_bound (nu : Viscosity) (j : Coordinate) (value : Z) : ‖map nu j value‖ ≤ cap nu*‖value‖ := by
  apply ((map nu j).le_opNorm value).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact lp.norm_mapCLM_le _ _ _ _

def componentRead (j output input : Coordinate) : Current →L[ℂ] Z :=
  (ContinuousLinearMap.proj input : (Coordinate → Z) →L[ℂ] Z).comp
    ((ContinuousLinearMap.proj output : (Coordinate → Coordinate → Z) →L[ℂ] (Coordinate → Z)).comp
      (ContinuousLinearMap.proj j : Current →L[ℂ] (Coordinate → Coordinate → Z)))

def resolve (nu : Viscosity) (output input : Coordinate) : Current →L[ℂ] Z :=
  ∑ j : Coordinate,(map nu j).comp (componentRead j output input)

theorem resolve_bound (nu : Viscosity) (output input : Coordinate) (value : Current) :
    ‖resolve nu output input value‖ ≤ 3*cap nu*‖value‖ := by
  change ‖∑ j : Coordinate,map nu j (value j output input)‖ ≤ _
  apply (norm_sum_le _ _).trans
  have bound (j : Coordinate) : ‖value j output input‖ ≤ ‖value‖ :=
    (norm_le_pi_norm (value j output) input).trans ((norm_le_pi_norm (value j) output).trans (norm_le_pi_norm value j))
  exact (Finset.sum_le_sum (fun j _ => (map_bound nu j _).trans (mul_le_mul_of_nonneg_left (bound j) (cap_positive nu).le))).trans_eq (by simp; ring)

theorem viscous_row (nu : Viscosity) (value : Current) (output input : Coordinate) (k : IntegerWavevector) :
    (nu.coeff*integerWaveViscousMultiplier k : ℝ) • resolve nu output input value k =
      ∑ j : Coordinate,multiplier k j*((radical k^2 : ℝ) : ℂ)*value j output input k := by
  have original (j : Coordinate) : (nu.coeff*integerWaveViscousMultiplier k : ℝ) • factor nu j k=
      multiplier k j*(radical k^2 : ℝ) := by
    by_cases zero : k=0
    · subst k; simp [factor,multiplier,complexWavevector]
    · rw [factor,smul_inv_smul₀ (by unfold integerWaveViscousMultiplier; positivity [nu.coeff_pos,integerWaveNormSq_pos zero] : nu.coeff*integerWaveViscousMultiplier k≠0)]
  change _ • (∑ j : Coordinate,factor nu j k*value j output input k)=_
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← smul_mul_assoc,original]

variable {nu : Viscosity}

def primitive (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius order : ℕ)
    (time : ℝ) (output input : Coordinate) : Z :=
  resolve nu output input (NativeWindowHighTransportSource.window seed F radius order time)

theorem window_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius order : ℕ) (time : ℝ) :
    HasDerivAt (NativeWindowHighTransportSource.window seed F radius order)
      (NativeWindowHighTransportSource.window seed F radius (order+1) time) time := by
  have : SecondCountableTopologyEither ℝ Current := ⟨Or.inl inferInstance⟩
  have locally : LocallyIntegrable (NativeWindowHighTransportSource.current seed F radius) (volume : Measure ℝ) :=
    (NativeWindowHighTransportSource.current_continuous seed F radius).locallyIntegrable
  have source := (NativeForwardWindowJets.kernelJet_compact order).hasDerivAt_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) ((NativeForwardWindowJets.kernelJet_smooth order).of_le (by simp))
    locally time
  simpa only [NativeWindowHighTransportSource.window,NativeForwardWindowJets.kernelJet,iteratedDeriv_succ] using! source

theorem primitive_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius order : ℕ)
    (time : ℝ) (output input : Coordinate) :
    HasDerivAt (fun t => primitive seed F radius order t output input) (primitive seed F radius (order+1) time output input) time :=
  ((resolve nu output input).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt time (window_hasDerivAt seed F radius order time)

theorem primitive_small (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (horizon : ℝ) (nonnegative : 0 ≤ horizon)
    (epsilon : ℝ) (positive : 0<epsilon) : ∃ low : ℕ,∀ radius ≥ low,∀ F time,time∈Icc 0 horizon →∀ output input,
      ‖primitive seed F radius order time output input‖<epsilon := by
  obtain ⟨low,small⟩ := NativeWindowHighTransportSource.exists_uniform_small seed order horizon nonnegative
    (epsilon/(3*cap nu)) (by positivity [cap_positive nu])
  refine ⟨low,fun radius above F time inside output input => ?_⟩
  apply (resolve_bound nu output input _).trans_lt
  exact (mul_lt_mul_of_pos_left (small radius above F time inside) (by positivity [cap_positive nu])).trans_eq (by field_simp [(cap_positive nu).ne'])

theorem primitive_next (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius order : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0 ≤ time) :
    primitive seed F radius order (step.2.clockAdvance+time)=primitive step.1 F radius order time := by
  unfold primitive
  rw [NativeWindowHighTransportSource.window_next seed F radius order step generated time nonnegative]


theorem current_supported (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (output input j : Coordinate) (k : IntegerWavevector) (outside : k∉F+(F+F)) :
    NativeWindowHighTransportSource.current seed F radius time j output input k=0 := by
  classical
  have left (p : IntegerWavevector) (absent : p∉F) : NativeWindowHighTransportSource.vectorRead j
      (NativeWindowHighTransportSource.highVelocity seed F radius time) p=0 := by
    rw [NativeWindowHighTransportSource.high_original]
    change complexSharpSupportProjection F _ p j=0
    simp [absent]
  have right (q : IntegerWavevector) (absent : q∉F+F) : NativeWindowHighTransportSource.tensorRead (output,input)
      (NativeWindowFiniteStressConvergence.finiteAt seed F time) q=0 := by
    change NativeWindowFiniteStressConvergence.finiteAt seed F time q (output,input)=0
    rw [NativeWindowFiniteStressConvergence.finiteAt,NativeWindowFiniteStressConvergence.finite_supported _ F q absent]
    rfl
  have actual := NativeWindowHighTransportProduct.product_supported _ _ F (F+F) left right k outside
  change -(NativeWindowHighTransportProduct.product _ _ k)=0
  rw [actual,neg_zero]

theorem window_supported (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius order : ℕ)
    (time : ℝ) (output input j : Coordinate) (k : IntegerWavevector) (outside : k∉F+(F+F)) :
    NativeWindowHighTransportSource.window seed F radius order time j output input k=0 := by
  have : SecondCountableTopologyEither ℝ Current := ⟨Or.inl inferInstance⟩
  have locally : LocallyIntegrable (NativeWindowHighTransportSource.current seed F radius) (volume : Measure ℝ) :=
    (NativeWindowHighTransportSource.current_continuous seed F radius).locallyIntegrable
  have paid := (NativeForwardWindowJets.kernelJet_compact order).convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (NativeForwardWindowJets.kernelJet_smooth order).continuous locally time
  change Integrable (fun shift => NativeForwardWindowJets.kernelJet order shift •
    NativeWindowHighTransportSource.current seed F radius (time-shift)) (volume : Measure ℝ) at paid
  change NativeWindowHighTransportSource.read j output input k (∫ shift,NativeForwardWindowJets.kernelJet order shift •
    NativeWindowHighTransportSource.current seed F radius (time-shift))=0
  rw [← (NativeWindowHighTransportSource.read j output input k).integral_comp_comm paid]
  simp only [map_smul]
  change (∫ shift,NativeForwardWindowJets.kernelJet order shift • NativeWindowHighTransportSource.current seed F radius (time-shift) j output input k)=0
  simp only [current_supported seed F radius _ output input j k outside,smul_zero,integral_zero]

theorem primitive_supported (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius order : ℕ)
    (time : ℝ) (output input : Coordinate) (k : IntegerWavevector) (outside : k∉F+(F+F)) :
    primitive seed F radius order time output input k=0 := by
  change (∑ j : Coordinate,factor nu j k*NativeWindowHighTransportSource.window seed F radius order time j output input k)=0
  exact Finset.sum_eq_zero fun j _ => by rw [window_supported seed F radius order time output input j k outside,mul_zero]


theorem primitive_zero (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius order : ℕ)
    (time : ℝ) (output input : Coordinate) : primitive seed F radius order time output input 0=0 := by
  change (∑ j : Coordinate,factor nu j 0*NativeWindowHighTransportSource.window seed F radius order time j output input 0)=0
  simp [factor,multiplier,complexWavevector]

end
end SaturationMonoid.NavierStokes.NativeWindowHighTransportResolvent
