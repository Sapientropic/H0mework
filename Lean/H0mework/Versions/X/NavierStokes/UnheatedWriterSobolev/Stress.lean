import H0mework.Versions.X.NavierStokes.UnheatedWriterHalf.Carrier
import H0mework.Versions.X.NavierStokes.SourceUnheated.WindowResidual
import H0mework.Versions.X.NavierStokes.WindowHistory.Gradient

set_option autoImplicit false
open scoped BigOperators Topology ENNReal Convolution
namespace SaturationMonoid.NavierStokes.NativeWindowSobolevStress
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open NativeCompleteStressCarrier NativeCompleteStressAction NativeEndpointVelocityCarrier NativeHigherTimeJets
open NativeWholeResolvent NativeWholeH1Mixed NativeUnheatedWindowJensen NativeForwardWindowJets
noncomputable section
variable {nu : Viscosity}

def quarter (wave : IntegerWavevector) : ℝ := Real.sqrt (Real.sqrt (1+integerWaveNormSq wave))
theorem quarter_nonnegative (wave : IntegerWavevector) : 0 ≤ quarter wave := Real.sqrt_nonneg _
theorem quarter_positive (wave : IntegerWavevector) : 0 < quarter wave := by
  unfold quarter
  positivity [integerWaveNormSq_nonneg wave]
theorem quarter_sq (wave : IntegerWavevector) : quarter wave^2 = Real.sqrt (1+integerWaveNormSq wave) :=
  Real.sq_sqrt (Real.sqrt_nonneg _)

def observe (F : Finset IntegerWavevector) (stress : NativeFluidStressFourierState) :
    EuclideanSpace ℂ (F × (Coordinate × Coordinate)) :=
  WithLp.toLp 2 fun entry => quarter entry.1.1 • stress entry.1.1 entry.2.1 entry.2.2

def observeCLM (F : Finset IntegerWavevector) :
    Space →L[ℝ] EuclideanSpace ℂ (F × (Coordinate × Coordinate)) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : F × (Coordinate × Coordinate) => ℂ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun entry => quarter entry.1.1 • readCLM entry.1.1 entry.2.1 entry.2.2)

theorem observeCLM_apply (F : Finset IntegerWavevector) (value : Space) : observeCLM F value = observe F (read value) := rfl

theorem observe_norm_sq (F : Finset IntegerWavevector) (stress : NativeFluidStressFourierState) :
    ‖observe F stress‖^2 = ∑ wave ∈ F, Real.sqrt (1+integerWaveNormSq wave)*‖tensor (stress wave)‖^2 := by
  have same : observe F stress = NativeUnheatedStressProduct.observe F (fun wave => quarter wave • stress wave) := rfl
  rw [same,NativeUnheatedStressProduct.observe_norm_sq]
  apply Finset.sum_congr rfl
  intro wave _
  change ‖quarter wave • tensor (stress wave)‖^2 = _
  rw [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,quarter_sq]

theorem raw_bound (value : wholePhysical) (regular : H1 value) (F : Finset IntegerWavevector) :
    ‖observe F (mixedFlux (wholeVelocity value.1) (wholeVelocity value.1))‖ ≤
      3*Real.sqrt NativeUnheatedRieszKernel.constant*gradientMass value := by
  have entries (wave : IntegerWavevector) :
      ‖tensor (mixedFlux (wholeVelocity value.1) (wholeVelocity value.1) wave)‖^2 ≤
        9*NativeUnheatedQuarticEnvelope.row value wave^2 := by
    rw [tensor_norm_sq]
    have bound := Finset.sum_le_sum (s := (Finset.univ : Finset Coordinate)) fun output _ =>
      Finset.sum_le_sum (s := (Finset.univ : Finset Coordinate)) fun input _ =>
        pow_le_pow_left₀ (norm_nonneg _) (NativeUnheatedHalfNonlinear.flux_row_bound value wave output input) 2
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat,
      ← mul_assoc,show (3 : ℝ)*3=9 by norm_num] using bound
  have mass0 : 0 ≤ gradientMass value := tsum_nonneg (gradient_nonnegative value)
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity [NativeUnheatedRieszKernel.constant_nonnegative])).mp
  rw [observe_norm_sq]
  have rows := Finset.sum_le_sum (s := F) fun wave _ =>
    mul_le_mul_of_nonneg_left (entries wave) (Real.sqrt_nonneg (1+integerWaveNormSq wave))
  apply rows.trans
  have paid := mul_le_mul_of_nonneg_left (NativeUnheatedQuarticHalfEnvelope.observed_bound value regular F)
    (by norm_num : (0 : ℝ) ≤ 9)
  convert! paid using 1
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro wave _
    ring
  · rw [mul_pow,mul_pow,Real.sq_sqrt NativeUnheatedRieszKernel.constant_nonnegative]
    ring

theorem source_bound_ae (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) :
    ∀ᵐ time : ℝ, 0 ≤ time → ‖observeCLM F (NativeUnifiedCompleteSource.source seed time).snd‖ ≤
      3*Real.sqrt NativeUnheatedRieszKernel.constant*NativeUnheatedSourceGradient.mass seed time := by
  filter_upwards [NativeUnheatedSourceGradient.physical_H1_ae seed,NativeUnifiedGlobalStressSource.stress_ae seed]
    with time regular stress nonnegative
  have same : read (NativeUnifiedCompleteSource.source seed time).snd =
      mixedFlux (wholeVelocity (NativeUnheatedSourceGradient.physical seed time nonnegative).1)
        (wholeVelocity (NativeUnheatedSourceGradient.physical seed time nonnegative).1) := by
    rw [NativeUnifiedCompleteSource.stress_read,stress,mixedFlux_diagonal]
    change _ = NativeStressSource.quadraticFlux (wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst)
    rw [NativeUnifiedCompleteSource.velocity_read]
  rw [observeCLM_apply,same]
  simpa only [NativeUnheatedSourceGradient.physical_mass] using
    raw_bound (NativeUnheatedSourceGradient.physical seed time nonnegative) (regular nonnegative) F

theorem observed_average (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ) (F : Finset IntegerWavevector) :
    observe F (NativeUnheatedWindowStress.stress seed order time) =
      ∫ shift, kernelJet order shift • observeCLM F (NativeUnifiedCompleteSource.source seed (time-shift)).snd ∂shiftMeasure := by
  let view : FullSpace →L[ℝ] EuclideanSpace ℂ (F × (Coordinate × Coordinate)) :=
    (observeCLM F).comp (WithLp.sndL 2 ℝ WholeRestartVelocityEndpointState Space)
  have integrable : Integrable (fun shift : ℝ => kernelJet order shift • NativeUnifiedCompleteSource.source seed (time-shift)) :=
    (kernelJet_compact order).convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ)
      (kernelJet_smooth order).continuous (NativeForwardWindowSource.original_locallyIntegrable seed) time
  change view (∫ shift : ℝ, kernelJet order shift • NativeUnifiedCompleteSource.source seed (time-shift)) = _
  rw [← view.integral_comp_comm integrable]
  simp only [map_smul]
  change (∫ shift : ℝ, kernelJet order shift • observeCLM F (NativeUnifiedCompleteSource.source seed (time-shift)).snd) = _
  rw [shiftMeasure,← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards with shift
  by_cases inside : shift ∈ Icc (-2 : ℝ) (-1)
  · simp only [indicator_of_mem inside]
  · have zero : kernelJet order shift=0 := by
      by_contra nonzero
      exact inside (kernel_support order shift nonzero)
    simp only [indicator_of_notMem inside,zero,zero_smul]

def budget (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ) : ℝ :=
  3*Real.sqrt NativeUnheatedRieszKernel.constant*Real.sqrt (NativeUnheatedWindowGradient.kernelCeiling order)*
    NativeUnheatedGlobalGradient.budget (NativeEventualTailControl.terminal seed) (time+2)

theorem mass_shift_to_horizon (seed : GeneratedWholeRestartCurrent nu) (time horizon : ℝ)
    (valid : -1 ≤ time) (before : time ≤ horizon) :
    (∫ shift in Icc (-2 : ℝ) (-1), NativeUnheatedSourceGradient.mass seed (time-shift)) ≤
      NativeUnheatedGlobalGradient.budget (NativeEventualTailControl.terminal seed) (horizon+2) := by
  rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le (by norm_num : (-2 : ℝ) ≤ -1),
    intervalIntegral.integral_comp_sub_left]
  have first : time-(-1 : ℝ)=time+1 := by ring
  have last : time-(-2 : ℝ)=time+2 := by ring
  rw [first,last]
  have integrable : IntervalIntegrable (NativeUnheatedSourceGradient.mass seed) volume 0 (horizon+2) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith : 0 ≤ horizon+2)).mpr
      (NativeUnheatedSourceGradient.mass_integrable seed (horizon+2) (by linarith))
  have paid := intervalIntegral.integral_mono_interval (show 0 ≤ time+1 by linarith)
    (show time+1 ≤ time+2 by linarith) (show time+2 ≤ horizon+2 by linarith)
    (Eventually.of_forall (NativeUnheatedSourceGradient.mass_nonnegative seed)) integrable
  apply paid.trans
  rw [intervalIntegral.integral_of_le (by linarith : 0 ≤ horizon+2),← integral_Icc_eq_integral_Ioc]
  exact NativeUnheatedSourceGradient.mass_integral_bound seed (horizon+2) (by linarith)

theorem observed_bound_on_interval (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time horizon : ℝ) (valid : -1 ≤ time) (before : time ≤ horizon)
    (F : Finset IntegerWavevector) : ‖observe F (NativeUnheatedWindowStress.stress seed order time)‖ ≤ budget seed order horizon := by
  rw [observed_average]
  let factor := 3*Real.sqrt NativeUnheatedRieszKernel.constant*Real.sqrt (NativeUnheatedWindowGradient.kernelCeiling order)
  have integrable : Integrable (fun shift => NativeUnheatedSourceGradient.mass seed (time-shift)) shiftMeasure :=
    NativeWindowHistoryGradient.mass_shift_integrable seed time valid
  have actual := (Measure.measurePreserving_sub_left (volume : Measure ℝ) time).quasiMeasurePreserving.ae
    (source_bound_ae seed F)
  have paid := norm_integral_le_of_norm_le
    (f := fun shift => kernelJet order shift • observeCLM F (NativeUnifiedCompleteSource.source seed (time-shift)).snd)
    (integrable.const_mul factor) (by
    filter_upwards [ae_restrict_of_ae actual,ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Icc]
      with shift source inside
    rw [norm_smul]
    have kernel : ‖kernelJet order shift‖ ≤ Real.sqrt (NativeUnheatedWindowGradient.kernelCeiling order) :=
      Real.le_sqrt_of_sq_le (by simpa only [Real.norm_eq_abs,sq_abs] using
        NativeUnheatedWindowGradient.kernel_square_le order shift inside)
    exact (mul_le_mul kernel (source (by linarith [inside.2])) (norm_nonneg _) (Real.sqrt_nonneg _)).trans_eq
      (by dsimp [factor]; ring))
  rw [integral_const_mul] at paid
  exact paid.trans (mul_le_mul_of_nonneg_left (mass_shift_to_horizon seed time horizon valid before) (by
    dsimp [factor]; positivity))

theorem observed_bound (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ) (valid : -1 ≤ time)
    (F : Finset IntegerWavevector) : ‖observe F (NativeUnheatedWindowStress.stress seed order time)‖ ≤ budget seed order time :=
  observed_bound_on_interval seed order time time valid le_rfl F

theorem stress_summable (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ) (valid : -1 ≤ time) :
    Summable (fun wave => Real.sqrt (1+integerWaveNormSq wave)*
      ‖tensor (NativeUnheatedWindowStress.stress seed order time wave)‖^2) := by
  apply summable_of_sum_le (fun wave => mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg _)) (c := budget seed order time^2)
  intro F
  rw [← observe_norm_sq]
  exact pow_le_pow_left₀ (norm_nonneg _) (observed_bound seed order time valid F) 2

def state (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ) (valid : -1 ≤ time) : Space :=
  ⟨fun wave => quarter wave • tensor (NativeUnheatedWindowStress.stress seed order time wave), by
    apply memℓp_gen
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,quarter_sq]
      using stress_summable seed order time valid⟩

theorem state_row (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ) (valid : -1 ≤ time)
    (wave : IntegerWavevector) (output input : Coordinate) :
    state seed order time valid wave (output,input) = quarter wave • read (jet seed order time).snd wave output input := rfl

theorem restore_state (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ) (valid : -1 ≤ time)
    (wave : IntegerWavevector) (output input : Coordinate) :
    (quarter wave)⁻¹ • state seed order time valid wave (output,input) =
      read (jet seed order time).snd wave output input := by
  rw [state_row,inv_smul_smul₀ (quarter_positive wave).ne']

theorem state_bound (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ) (valid : -1 ≤ time) :
    ‖state seed order time valid‖ ≤ budget seed order time := by
  have nonnegative : 0 ≤ budget seed order time := (norm_nonneg _).trans (observed_bound seed order time valid ∅)
  apply (sq_le_sq₀ (norm_nonneg _) nonnegative).mp
  have normed := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num) (state seed order time valid)
  simp only [ENNReal.toReal_ofNat,Real.rpow_two,state,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,quarter_sq] at normed
  change ‖state seed order time valid‖^2 = ∑' wave, Real.sqrt (1+integerWaveNormSq wave)*
    ‖tensor (NativeUnheatedWindowStress.stress seed order time wave)‖^2 at normed
  rw [normed]
  apply (stress_summable seed order time valid).tsum_le_of_sum_le
  intro F
  rw [← observe_norm_sq]
  exact pow_le_pow_left₀ (norm_nonneg _) (observed_bound seed order time valid F) 2

theorem moment_bound (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ) (valid : -1 ≤ time) :
    (∑' wave, Real.sqrt (1+integerWaveNormSq wave)*
      ‖tensor (NativeUnheatedWindowStress.stress seed order time wave)‖^2) ≤ budget seed order time^2 := by
  apply (stress_summable seed order time valid).tsum_le_of_sum_le
  intro F
  rw [← observe_norm_sq]
  exact pow_le_pow_left₀ (norm_nonneg _) (observed_bound seed order time valid F) 2

theorem moment_bound_on_interval (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time horizon : ℝ)
    (valid : -1 ≤ time) (before : time ≤ horizon) :
    (∑' wave, Real.sqrt (1+integerWaveNormSq wave)*
      ‖tensor (NativeUnheatedWindowStress.stress seed order time wave)‖^2) ≤ budget seed order horizon^2 := by
  apply (stress_summable seed order time valid).tsum_le_of_sum_le
  intro F
  rw [← observe_norm_sq]
  exact pow_le_pow_left₀ (norm_nonneg _) (observed_bound_on_interval seed order time horizon valid before F) 2

theorem state_residual_split (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ) (valid : -1 ≤ time)
    (wave : IntegerWavevector) (output input : Coordinate) :
    state seed order time valid wave (output,input) = quarter wave •
      (NativeUnheatedWindowResidual.coefficients seed order time wave output input+
        mixedTimeSum (NativeUnheatedWindowResidual.velocity seed) (NativeUnheatedWindowResidual.velocity seed)
          order time wave output input) := by
  rw [state_row]
  change quarter wave • NativeUnheatedWindowStress.stress seed order time wave output input = _
  simp only [NativeUnheatedWindowResidual.coefficients,Pi.sub_apply,sub_add_cancel]

open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open SourceGeneratedNativeResponseDisposition

theorem state_next (seed : GeneratedWholeRestartCurrent nu) (order : ℕ)
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response)
    (time : ℝ) (nonnegative : 0 ≤ time) :
    state seed order (response.2.clockAdvance+time) (by linarith [response.2.clockAdvance_pos]) =
      state response.1 order time (by linarith) := by
  apply lp.ext
  funext wave
  change quarter wave • tensor (read (jet seed order (response.2.clockAdvance+time)).snd wave) = _
  rw [jet_next seed order response generated time nonnegative]
  rfl

end
end SaturationMonoid.NavierStokes.NativeWindowSobolevStress
