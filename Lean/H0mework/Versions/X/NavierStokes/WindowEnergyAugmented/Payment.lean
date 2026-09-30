import H0mework.Versions.X.NavierStokes.WindowEnergyAugmented.Green
import H0mework.Versions.X.NavierStokes.WindowSourceGreen.FiniteDensityCoefficient

set_option autoImplicit false
open scoped BigOperators Topology ENNReal Convolution
namespace SaturationMonoid.NavierStokes.NativeWindowAugmentedPayment
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open NativePhysicalFourier NativeCompleteStressCarrier NativeWindowFiniteStressUniform
open NativeForwardWindowJets NativeWindowHighTransportRelative NativeWindowSobolevStress
noncomputable section
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) := inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
variable {nu : Viscosity}

def graphSample (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (time : ℝ) : ℝ :=
  (2*Real.pi)^2*NativeUnheatedBandGradient.band (F.subtype (fun k => k≠0))
    (NativeAbsoluteEventualControl.velocity seed time)

theorem graphSample_original (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (time : ℝ) :
    graphSample seed F time=(2*Real.pi)^2*NativeUnheatedStressProduct.gradientMass (NativeUnheatedWindowStress.projection seed F time) := by
  rw [NativeUnheatedWindowStress.projection,NativeUnheatedWindowStress.mass_band]
  rfl

theorem graphSample_continuous (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) :
    Continuous (graphSample seed F) :=
  (NativeUnheatedBandGradient.band_curve_continuous
    (NativeFiniteMacroGlobal.coordinate_continuous (NativeEventualTailControl.terminal seed)) _).const_mul _

theorem graphSample_nonnegative (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (time : ℝ) :
    0 ≤ graphSample seed F time := mul_nonneg (sq_nonneg _) (NativeUnheatedBandGradient.band_nonnegative _ _)

def graphJet (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (order : ℕ) : ℝ → ℝ :=
  kernelJet order ⋆[ContinuousLinearMap.lsmul ℝ ℝ] graphSample seed F

theorem graphJet_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (order : ℕ) (time : ℝ) :
    HasDerivAt (graphJet seed F order) (graphJet seed F (order+1) time) time := by
  have source := (kernelJet_compact order).hasDerivAt_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    ((kernelJet_smooth order).of_le (by simp)) ((graphSample_continuous seed F).locallyIntegrable (μ := (volume : Measure ℝ))) time
  simpa only [graphJet,kernelJet,iteratedDeriv_succ] using source

def graphBudget (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (horizon : ℝ) : ℝ :=
  (2*Real.pi)^2*kernelBound order*NativeUnheatedGlobalGradient.budget (NativeEventualTailControl.terminal seed) (horizon+2)

theorem graphJet_bound (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (order : ℕ) (time horizon : ℝ) (inside : time∈Icc 0 horizon) :
    ‖graphJet seed F order time‖ ≤ graphBudget seed order horizon := by
  change ‖∫ shift, kernelJet order shift • graphSample seed F (time-shift)‖ ≤ _
  rw [← average_original order time horizon inside,NativeWindowFiniteStressUniform.average]
  have paid := norm_integral_le_of_norm_le
    (μ := volume.restrict (Icc 0 (horizon+2)))
    (f := fun sample => kernelJet order (time-sample) • graphSample seed F sample)
    (((graphSample_continuous seed F).const_mul (kernelBound order)).integrableOn_Icc)
    (Eventually.of_forall fun sample => by
      rw [norm_smul,Real.norm_of_nonneg (graphSample_nonnegative seed F sample)]
      exact mul_le_mul_of_nonneg_right (kernel_bounded order (time-sample)) (graphSample_nonnegative seed F sample))
  rw [integral_const_mul] at paid
  have original := NativeUnheatedGlobalGradient.source_interval_bound seed 0 (horizon+2) le_rfl
    (by linarith [inside.1,inside.2]) (F.subtype (fun k => k≠0))
  rw [intervalIntegral.integral_of_le (by linarith [inside.1,inside.2] : 0 ≤ horizon+2),← integral_Icc_eq_integral_Ioc] at original
  apply paid.trans
  simp only [graphSample,integral_const_mul,graphBudget]
  have bounded := mul_le_mul_of_nonneg_left original (mul_nonneg (kernelBound_positive order).le (sq_nonneg (2*Real.pi)))
  nlinarith only [bounded]

theorem quarter_one (wave : IntegerWavevector) : 1 ≤ quarter wave := by
  change 1 ≤ Real.sqrt (Real.sqrt (1+integerWaveNormSq wave))
  exact Real.one_le_sqrt.mpr (Real.one_le_sqrt.mpr (by linarith [integerWaveNormSq_nonneg wave]))

def restore (output input : Coordinate) : Space →L[ℝ] ScalarSequence :=
  lp.mapCLM 2 (fun wave : IntegerWavevector => (-((quarter wave)⁻¹)) • PiLp.proj (𝕜 := ℝ) 2
    (fun _ : Coordinate × Coordinate => ℂ) (output,input)) (by norm_num : (0 : ℝ) ≤ 1)
      (fun wave => ContinuousLinearMap.opNorm_le_bound _ (by norm_num : (0 : ℝ) ≤ 1) (fun value => by
        simp only [smul_apply,PiLp.proj_apply,norm_smul,norm_neg,
          Real.norm_of_nonneg (inv_nonneg.mpr (quarter_positive wave).le),one_mul]
        exact (mul_le_of_le_one_left (norm_nonneg _) (inv_le_one_of_one_le₀ (quarter_one wave))).trans (PiLp.norm_apply_le value (output,input))))

theorem restore_bound (output input : Coordinate) (value : Space) : ‖restore output input value‖ ≤ ‖value‖ := by
  apply ((restore output input).le_opNorm value).trans
  have bound : ‖restore output input‖ ≤ 1 := lp.norm_mapCLM_le _ _ _ _
  simpa only [one_mul] using mul_le_mul_of_nonneg_right bound (norm_nonneg value)

def stressJet (seed : GeneratedWholeRestartCurrent nu) (radius order : ℕ) (time : ℝ)
    (output input : Coordinate) : ScalarField := fieldCLM (restore output input (window seed radius order time))

theorem stressJet_zero (seed : GeneratedWholeRestartCurrent nu) (radius : ℕ) (time : ℝ)
    (nonnegative : 0 ≤ time) (output input : Coordinate) : stressJet seed radius 0 time output input=
      NativeWindowStressHeatSource.physical (NativeWindowFiniteGramFourier.stress seed time
        (integerWaveFrequencyCube radius) output input) := by
  apply (UnitAddTorus.mFourierBasis (d := Coordinate)).repr.injective
  apply lp.ext
  funext wave
  change (UnitAddTorus.mFourierBasis (d := Coordinate)).repr
    ((UnitAddTorus.mFourierBasis (d := Coordinate)).repr.symm (restore output input (window seed radius 0 time))) wave=_
  rw [LinearIsometryEquiv.apply_symm_apply]
  change -(quarter wave)⁻¹ • window seed radius 0 time wave (output,input)=_
  rw [NativeWindowFiniteDensityCoefficient.window_zero_row seed radius time nonnegative wave output input]
  rw [UnitAddTorus.mFourierBasis_repr]
  change _=UnitAddTorus.mFourierCoeff (((Complex.ofRealCLM.compLeftContinuous ℝ Torus)
    (NativeWindowFiniteGramFourier.stress seed time (integerWaveFrequencyCube radius) output input)).toLp 2 volume ℂ) wave
  rw [UnitAddTorus.mFourierCoeff_toLp]
  simp only [Complex.real_smul,Complex.ofReal_neg]
  rw [← mul_assoc,neg_mul_neg,← Complex.ofReal_mul,inv_mul_cancel₀ (quarter_positive wave).ne',Complex.ofReal_one,one_mul]
  rfl

theorem window_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (radius order : ℕ) (time : ℝ) :
    HasDerivAt (window seed radius order) (window seed radius (order+1) time) time := by
  have source := (kernelJet_compact order).hasDerivAt_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    ((kernelJet_smooth order).of_le (by simp))
    ((NativeWindowFiniteStressConvergence.finiteAt_continuous seed (integerWaveFrequencyCube radius)).locallyIntegrable (μ := (volume : Measure ℝ))) time
  simpa only [window,kernelJet,iteratedDeriv_succ] using! source

theorem stressJet_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (radius order : ℕ) (time : ℝ)
    (output input : Coordinate) : HasDerivAt (fun t => stressJet seed radius order t output input)
      (stressJet seed radius (order+1) time output input) time :=
  (fieldCLM.comp (restore output input)).hasFDerivAt.comp_hasDerivAt time (window_hasDerivAt seed radius order time)

theorem stressJet_original (seed : GeneratedWholeRestartCurrent nu) (radius order : ℕ) (time : ℝ)
    (nonnegative : 0 ≤ time) (output input : Coordinate) : stressJet seed radius order time output input=
      NativeWindowStressHeatSource.physical (NativeWindowStressHeatTime.jet seed (integerWaveFrequencyCube radius) output input order time) := by
  induction order generalizing time with
  | zero => simpa only [NativeWindowStressHeatTime.jet_zero] using stressJet_zero seed radius time nonnegative output input
  | succ order ih =>
    have first := (stressJet_hasDerivAt seed radius order time output input).hasDerivWithinAt (s := Ici (0 : ℝ))
    have last := (NativeWindowStressHeatSource.physical.hasFDerivAt.comp_hasDerivAt time
      (NativeWindowStressHeatTime.jet_hasDerivAt seed (integerWaveFrequencyCube radius) output input order time)).hasDerivWithinAt (s := Ici (0 : ℝ))
    have same := last.congr_of_mem (fun sample inside => ih sample inside) nonnegative
    have equal := congrArg (fun f : ℝ →L[ℝ] ScalarField => f 1) ((uniqueDiffOn_Ici (0 : ℝ)).eq nonnegative first same)
    simpa only [ContinuousLinearMap.toSpanSingleton_apply,one_smul] using equal

def stressBudget (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (horizon : ℝ) : ℝ :=
  kernelBound order*NativeWindowFiniteStressConvergence.cap*
    NativeUnheatedGlobalGradient.budget (NativeEventualTailControl.terminal seed) (horizon+2)

theorem stressJet_bound (seed : GeneratedWholeRestartCurrent nu) (radius order : ℕ) (time horizon : ℝ)
    (inside : time∈Icc 0 horizon) (output input : Coordinate) :
    ‖stressJet seed radius order time output input‖ ≤ stressBudget seed order horizon := by
  change ‖(UnitAddTorus.mFourierBasis (d := Coordinate)).repr.symm _‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  exact (restore_bound output input _).trans (window_bound seed radius order time horizon inside)


def massJet (seed : GeneratedWholeRestartCurrent nu) (radius order : ℕ) (time : ℝ) : ℝ :=
  ∑ i : Coordinate,inner ℝ (NativeWindowStressHeatSource.physical 1) (stressJet seed radius order time i i)

def word (seed : GeneratedWholeRestartCurrent nu) (outerRadius radius order : ℕ) (time : ℝ) : ℝ :=
  massJet seed outerRadius order time+nu.coeff*graphJet seed (integerWaveFrequencyCube outerRadius) order time+
    ∑ output : Coordinate,∑ input : Coordinate,inner ℝ
      (stressJet seed outerRadius 0 time output input+primitiveField seed (integerWaveFrequencyCube outerRadius) radius 0 time output input)
      (stressJet seed outerRadius order time output input)

def wordRate (seed : GeneratedWholeRestartCurrent nu) (outerRadius radius order : ℕ) (time : ℝ) : ℝ :=
  massJet seed outerRadius (order+1) time+nu.coeff*graphJet seed (integerWaveFrequencyCube outerRadius) (order+1) time+
    ∑ output : Coordinate,∑ input : Coordinate,(inner ℝ
      (stressJet seed outerRadius 1 time output input+primitiveField seed (integerWaveFrequencyCube outerRadius) radius 1 time output input)
      (stressJet seed outerRadius order time output input)+inner ℝ
      (stressJet seed outerRadius 0 time output input+primitiveField seed (integerWaveFrequencyCube outerRadius) radius 0 time output input)
      (stressJet seed outerRadius (order+1) time output input))

theorem word_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (outerRadius radius order : ℕ) (time : ℝ) :
    HasDerivAt (word seed outerRadius radius order) (wordRate seed outerRadius radius order time) time := by
  have trace : HasDerivAt (massJet seed outerRadius order) (massJet seed outerRadius (order+1) time) time := by
    simpa only [massJet,inner_zero_left,add_zero] using! HasDerivAt.sum (u := Finset.univ) (fun i _ =>
      (hasDerivAt_const time (NativeWindowStressHeatSource.physical 1)).inner ℝ (stressJet_hasDerivAt seed outerRadius order time i i))
  have row (output input : Coordinate) :=
    ((stressJet_hasDerivAt seed outerRadius 0 time output input).add
      (primitiveField_hasDerivAt seed (integerWaveFrequencyCube outerRadius) radius 0 time output input)).inner ℝ
        (stressJet_hasDerivAt seed outerRadius order time output input)
  have matrix := HasDerivAt.sum (u := Finset.univ) fun output _ => HasDerivAt.sum (u := Finset.univ) fun input _ => row output input
  have actual := (trace.add ((graphJet_hasDerivAt seed (integerWaveFrequencyCube outerRadius) order time).const_mul nu.coeff)).add matrix
  simp only [Pi.add_apply,Nat.zero_add] at actual
  have swapped : wordRate seed outerRadius radius order time=
      massJet seed outerRadius (order+1) time+nu.coeff*graphJet seed (integerWaveFrequencyCube outerRadius) (order+1) time+
        ∑ output : Coordinate,∑ input : Coordinate,(inner ℝ
          (stressJet seed outerRadius 0 time output input+primitiveField seed (integerWaveFrequencyCube outerRadius) radius 0 time output input)
          (stressJet seed outerRadius (order+1) time output input)+inner ℝ
          (stressJet seed outerRadius 1 time output input+primitiveField seed (integerWaveFrequencyCube outerRadius) radius 1 time output input)
          (stressJet seed outerRadius order time output input)) := by
    simp only [wordRate,Finset.sum_add_distrib]
    ring
  rw [swapped]
  simpa only [word] using! actual

def wordBudget (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (horizon : ℝ) : ℝ :=
  3*‖NativeWindowStressHeatSource.physical 1‖*stressBudget seed order horizon+nu.coeff*graphBudget seed order horizon+
    9*(stressBudget seed 0 horizon+1)*stressBudget seed order horizon

theorem word_uniform (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    ∃ low : ℕ,∀ radius ≥ low,∀ outerRadius order time,time∈Icc 0 horizon →
      |word seed outerRadius radius order time| ≤ wordBudget seed order horizon := by
  obtain ⟨low,paid⟩ := NativeWindowHighTransportResolvent.primitive_small seed 0 horizon nonnegative 1 (by norm_num)
  refine ⟨low,fun radius above outerRadius order time inside => ?_⟩
  have S (n : ℕ) (output input : Coordinate) := stressJet_bound seed outerRadius n time horizon inside output input
  have P (output input : Coordinate) : ‖primitiveField seed (integerWaveFrequencyCube outerRadius) radius 0 time output input‖ ≤ 1 := by
    rw [primitiveField_norm]
    exact (paid radius above _ time inside output input).le
  have S0 (n : ℕ) : 0 ≤ stressBudget seed n horizon := (norm_nonneg _).trans (S n 0 0)
  have matrix (output input : Coordinate) : |inner ℝ
      (stressJet seed outerRadius 0 time output input+primitiveField seed (integerWaveFrequencyCube outerRadius) radius 0 time output input)
      (stressJet seed outerRadius order time output input)| ≤ (stressBudget seed 0 horizon+1)*stressBudget seed order horizon :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul ((norm_add_le _ _).trans (add_le_add (S 0 output input) (P output input)))
      (S order output input) (norm_nonneg _) (add_nonneg (S0 0) zero_le_one))
  have trace : |massJet seed outerRadius order time| ≤ 3*‖NativeWindowStressHeatSource.physical 1‖*stressBudget seed order horizon := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    exact (Finset.sum_le_sum (fun i _ => (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left (S order i i) (norm_nonneg _)))).trans_eq (by simp; ring)
  have sum : |∑ output : Coordinate,∑ input : Coordinate,inner ℝ
      (stressJet seed outerRadius 0 time output input+primitiveField seed (integerWaveFrequencyCube outerRadius) radius 0 time output input)
      (stressJet seed outerRadius order time output input)| ≤ 9*(stressBudget seed 0 horizon+1)*stressBudget seed order horizon :=
    (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum (fun output _ => Finset.abs_sum_le_sum_abs _ _)).trans
      ((Finset.sum_le_sum (fun output _ => Finset.sum_le_sum (fun input _ => matrix output input))).trans_eq (by simp; ring)))
  have graph := graphJet_bound seed (integerWaveFrequencyCube outerRadius) order time horizon inside
  rw [Real.norm_eq_abs] at graph
  have weighted : |nu.coeff*graphJet seed (integerWaveFrequencyCube outerRadius) order time| ≤ nu.coeff*graphBudget seed order horizon := by
    rw [abs_mul,abs_of_pos nu.coeff_pos]
    exact mul_le_mul_of_nonneg_left graph nu.coeff_pos.le
  exact (abs_add_le _ _).trans ((add_le_add ((abs_add_le _ _).trans (add_le_add trace weighted)) sum))


theorem word_rate_uniform (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    ∃ low : ℕ,∀ radius ≥ low,∀ outerRadius order time,time∈Icc 0 horizon →
      |wordRate seed outerRadius radius order time| ≤ wordBudget seed (order+1) horizon+
        9*(stressBudget seed 1 horizon+1)*stressBudget seed order horizon := by
  obtain ⟨first,words⟩ := word_uniform seed horizon nonnegative
  obtain ⟨last,small⟩ := NativeWindowHighTransportResolvent.primitive_small seed 1 horizon nonnegative 1 (by norm_num)
  refine ⟨max first last,fun radius above outerRadius order time inside => ?_⟩
  have S (n : ℕ) (output input : Coordinate) := stressJet_bound seed outerRadius n time horizon inside output input
  have nonnegativeS (n : ℕ) : 0 ≤ stressBudget seed n horizon := (norm_nonneg _).trans (S n 0 0)
  have P (output input : Coordinate) : ‖primitiveField seed (integerWaveFrequencyCube outerRadius) radius 1 time output input‖ ≤ 1 := by
    rw [primitiveField_norm]
    exact (small radius ((le_max_right first last).trans above) _ time inside output input).le
  have row (output input : Coordinate) : |inner ℝ
      (stressJet seed outerRadius 1 time output input+primitiveField seed (integerWaveFrequencyCube outerRadius) radius 1 time output input)
      (stressJet seed outerRadius order time output input)| ≤ (stressBudget seed 1 horizon+1)*stressBudget seed order horizon :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul ((norm_add_le _ _).trans (add_le_add (S 1 output input) (P output input)))
      (S order output input) (norm_nonneg _) (add_nonneg (nonnegativeS 1) zero_le_one))
  have extra : |∑ output : Coordinate,∑ input : Coordinate,inner ℝ
      (stressJet seed outerRadius 1 time output input+primitiveField seed (integerWaveFrequencyCube outerRadius) radius 1 time output input)
      (stressJet seed outerRadius order time output input)| ≤ 9*(stressBudget seed 1 horizon+1)*stressBudget seed order horizon :=
    (Finset.abs_sum_le_sum_abs (fun output =>
      ∑ input : Coordinate,inner ℝ
        (stressJet seed outerRadius 1 time output input+primitiveField seed (integerWaveFrequencyCube outerRadius) radius 1 time output input)
        (stressJet seed outerRadius order time output input)) Finset.univ).trans
      ((Finset.sum_le_sum (fun output _ => Finset.abs_sum_le_sum_abs _ _)).trans
        ((Finset.sum_le_sum (fun output _ => Finset.sum_le_sum (fun input _ => row output input))).trans_eq (by simp; ring)))
  have split : wordRate seed outerRadius radius order time=word seed outerRadius radius (order+1) time+
      ∑ output : Coordinate,∑ input : Coordinate,inner ℝ
        (stressJet seed outerRadius 1 time output input+primitiveField seed (integerWaveFrequencyCube outerRadius) radius 1 time output input)
        (stressJet seed outerRadius order time output input) := by
    simp only [wordRate,word,Finset.sum_add_distrib]
    ring
  rw [split]
  exact (abs_add_le _ _).trans (add_le_add (words radius ((le_max_left first last).trans above) outerRadius (order+1) time inside) extra)

theorem matrix_word_original (seed : GeneratedWholeRestartCurrent nu) (outerRadius radius order innerRadius : ℕ)
    (time : ℝ) (nonnegative : 0 ≤ time)
    (cover : ∀ wave∈integerWaveFrequencyCube outerRadius,wave≠0 →wave∈NativeWholeH1Mixed.modes innerRadius) :
    word seed outerRadius radius order time-massJet seed outerRadius order time-
      nu.coeff*graphJet seed (integerWaveFrequencyCube outerRadius) order time=
    ∫ sample in time+1..time+2,NativeUnheatedStressPairEvolution.kernelWeight order time 0 sample*
      NativeFiniteActionResolvent.pairing (NativeWholeH1Mixed.modes innerRadius) (NativeWindowStressOseenSource.load innerRadius seed sample)
        (NativeWindowAugmentedGreen.matrixTest seed time (NativeWholeH1Mixed.modes innerRadius) (integerWaveFrequencyCube outerRadius) radius
          (NativeWindowStressOseenSource.load innerRadius seed sample)) := by
  rw [NativeWindowAugmentedGreen.matrix_average seed time nonnegative innerRadius radius order _ cover]
  simp only [word,stressJet_original seed outerRadius order time nonnegative,stressJet_zero seed outerRadius time nonnegative,
    NativeWindowAugmentedGreen.matrixField]
  ring


open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open SourceGeneratedNativeResponseDisposition

theorem graphJet_next (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (order : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0 ≤ time) :
    graphJet seed F order (step.2.clockAdvance+time)=graphJet step.1 F order time := by
  change (∫ shift, kernelJet order shift • graphSample seed F (step.2.clockAdvance+time-shift))=
    ∫ shift, kernelJet order shift • graphSample step.1 F (time-shift)
  apply integral_congr_ae
  filter_upwards with shift
  by_cases zero : kernelJet order shift=0
  · simp only [zero,zero_smul]
  · have support := NativeUnheatedWindowJensen.kernel_support order shift zero
    simp only [graphSample,← NativeUnifiedCompleteSource.velocity_read,add_sub_assoc,
      NativeUnifiedCompleteSource.source_generated_next seed step generated (time-shift) (by linarith [support.2])]

theorem word_next (seed : GeneratedWholeRestartCurrent nu) (outerRadius radius order : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0 ≤ time) :
    word seed outerRadius radius order (step.2.clockAdvance+time)=word step.1 outerRadius radius order time := by
  simp only [word,massJet,stressJet,NativeWindowFiniteStressUniform.window_next seed outerRadius _ step generated time nonnegative,
    graphJet_next seed _ order step generated time nonnegative,primitiveField,
    NativeWindowHighTransportResolvent.primitive_next seed _ radius _ step generated time nonnegative]

end
end SaturationMonoid.NavierStokes.NativeWindowAugmentedPayment
