import H0mework.NavierStokes.WindowEnergyAugmented.FixedOperator
import H0mework.NavierStokes.WindowEnergyAugmented.Payment

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowAugmentedGlobalGreen
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open NativeResolventCompactness NativeUnheatedGlobalNegativeOne NativeWindowAugmentedSourceForm
open NativeWindowAugmentedFixedOperator NativeUnheatedSourceQuadraticApprox NativeWindowFiniteStressUniform
open NativeFiniteActionResolvent NativeWholeH1Mixed NativeWindowStressOseenSource NativeWindowOperatorGreen
noncomputable section
variable {nu : Viscosity}

def difference (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (L F : Finset IntegerWavevector)
    (radius M : ℕ) (sample : ℝ) : ℝ :=
  form seed observation L F radius (value M seed sample-NativeUnheatedSourceWeightedTail.nonlinear seed sample) (state seed sample)+
    form seed observation L F radius (state seed sample) (value M seed sample-NativeUnheatedSourceWeightedTail.nonlinear seed sample)

theorem difference_original (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ)
    (L F : Finset IntegerWavevector) (radius M : ℕ) (sample : ℝ) :
    approximateRate seed observation L F radius M sample-actualRate seed observation L F radius sample=
      difference seed observation L F radius M sample := by
  rw [actualRate_split]
  simp only [approximateRate,nonlinearRate,difference,map_sub,sub_apply]
  ring

def cap (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (L F : Finset IntegerWavevector) (radius : ℕ) : ℝ :=
  2*‖form seed observation L F radius‖*NativeUnifiedCompleteSource.budget seed

theorem difference_bound (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ)
    (L F : Finset IntegerWavevector) (radius M : ℕ) (sample : ℝ) :
    ‖difference seed observation L F radius M sample‖ ≤ cap seed observation L F radius*
      ‖value M seed sample-NativeUnheatedSourceWeightedTail.nonlinear seed sample‖ := by
  apply (norm_add_le _ _).trans
  let B:=form seed observation L F radius
  let err:=value M seed sample-NativeUnheatedSourceWeightedTail.nonlinear seed sample
  have source := NativeUnheatedSourceWeightedTail.state_bound seed sample
  have first := (B.le_opNorm₂ err (state seed sample)).trans
    (mul_le_mul_of_nonneg_left source (mul_nonneg (norm_nonneg B) (norm_nonneg err)))
  have last := (B.le_opNorm₂ (state seed sample) err).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left source (norm_nonneg B)) (norm_nonneg err))
  exact (add_le_add first last).trans_eq (by dsimp [B,err,cap]; ring)

theorem difference_integrable (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ)
    (L F : Finset IntegerWavevector) (radius M : ℕ) (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    Integrable (difference seed observation L F radius M) (volume.restrict (Icc 0 horizon)) := by
  have ratePaid := (value_integrable M seed horizon nonnegative).sub
    (NativeUnheatedSourceWeightedTail.nonlinear_integrable seed horizon nonnegative)
  have stateMeasured : AEStronglyMeasurable (state seed) (volume.restrict (Icc 0 horizon)) :=
    ((state_continuousOn seed).mono (fun _ inside => inside.1)).aestronglyMeasurable measurableSet_Icc
  have measured := ((form seed observation L F radius).aestronglyMeasurable_comp₂
      ratePaid.aestronglyMeasurable stateMeasured).add
    ((form seed observation L F radius).aestronglyMeasurable_comp₂ stateMeasured ratePaid.aestronglyMeasurable)
  exact (ratePaid.norm.const_mul (cap seed observation L F radius)).mono' measured
    (Eventually.of_forall fun sample => difference_bound seed observation L F radius M sample)

def rateWindow (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ)
    (L F : Finset IntegerWavevector) (radius order : ℕ) : ℝ :=
  NativeWindowFiniteStressUniform.average order observation observation (actualRate seed observation L F radius)

def approximateWindow (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ)
    (L F : Finset IntegerWavevector) (radius order M : ℕ) : ℝ :=
  NativeWindowFiniteStressUniform.average order observation observation (approximateRate seed observation L F radius M)

theorem approximateWindow_limit (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (nonnegative : 0 ≤ observation)
    (L F : Finset IntegerWavevector) (radius order : ℕ) :
    Tendsto (fun M => approximateWindow seed observation L F radius order M) atTop
      (𝓝 (rateWindow seed observation L F radius order)) := by
  have actualPaid : Integrable (actualRate seed observation L F radius) (volume.restrict (Icc 0 (observation+2))) :=
    by simpa only [uIcc_of_le (by linarith : 0 ≤ observation+2)] using!
      (intervalIntegrable_iff').mp (actualRate_integrable seed observation L F radius 0 (observation+2) le_rfl (by linarith))
  have errorBound (M : ℕ) : ‖approximateWindow seed observation L F radius order M-rateWindow seed observation L F radius order‖ ≤
      kernelBound order*cap seed observation L F radius*
        (∫ sample in Icc 0 (observation+2),‖value M seed sample-NativeUnheatedSourceWeightedTail.nonlinear seed sample‖) := by
    have differencePaid := difference_integrable seed observation L F radius M (observation+2) (by linarith)
    have approximated : approximateRate seed observation L F radius M=actualRate seed observation L F radius+
        difference seed observation L F radius M := by
      funext sample
      exact (sub_eq_iff_eq_add.mp (difference_original seed observation L F radius M sample)).trans (add_comm _ _)
    rw [approximateWindow,rateWindow,approximated,NativeWindowFiniteStressUniform.average,NativeWindowFiniteStressUniform.average]
    simp only [Pi.add_apply,smul_add]
    rw [integral_add (average_integrable order observation observation actualPaid)
      (average_integrable order observation observation differencePaid),add_sub_cancel_left]
    have sourcePaid := (value_integrable M seed (observation+2) (by linarith)).sub
      (NativeUnheatedSourceWeightedTail.nonlinear_integrable seed (observation+2) (by linarith))
    have paid := norm_integral_le_of_norm_le
      (f := fun sample => NativeForwardWindowJets.kernelJet order (observation-sample) • difference seed observation L F radius M sample)
      (sourcePaid.norm.const_mul (kernelBound order*cap seed observation L F radius)) (Eventually.of_forall fun sample => by
        rw [norm_smul]
        exact (mul_le_mul (kernel_bounded order (observation-sample))
          (difference_bound seed observation L F radius M sample) (norm_nonneg _) (kernelBound_positive order).le).trans_eq (by simp only [Pi.sub_apply]; ring))
    exact paid.trans_eq (integral_const_mul _ _)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) errorBound
  simpa only [mul_zero] using (quadratic_approximation seed (observation+2) (by linarith)).const_mul
    (kernelBound order*cap seed observation L F radius)

def greenWindow (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ)
    (L F : Finset IntegerWavevector) (radius order M : ℕ) : ℝ :=
  NativeWindowFiniteStressUniform.average order observation observation (fun sample =>
    pairing (modes M) (load M seed sample) (lyapunov (modes M) (modes_zero M) (modes_closed M) nu
      (advector M seed sample) (advector_reality M seed sample)
      (NativeWindowAugmentedFixedOperator.test seed observation (modes M) L F radius) (load M seed sample)))

theorem global_green (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (nonnegative : 0 ≤ observation)
    (L F : Finset IntegerWavevector) (radius order : ℕ) :
    Tendsto (fun M => greenWindow seed observation L F radius order M) atTop
      (𝓝 (rateWindow seed observation L F radius order)) := by
  apply (approximateWindow_limit seed observation nonnegative L F radius order).congr'
  filter_upwards [cover_eventually (L∪F)] with M cover
  unfold approximateWindow greenWindow NativeWindowFiniteStressUniform.average
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (approximate_green_ae seed observation L F radius M cover),
    ae_restrict_mem measurableSet_Icc] with sample generated inside
  rw [generated inside.1]

theorem rateWindow_write (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (nonnegative : 0 ≤ observation)
    (L F : Finset IntegerWavevector) (radius order : ℕ) : rateWindow seed observation L F radius order=
      NativeWindowFiniteStressUniform.average (order+1) observation observation (diagonal seed observation L F radius) := by
  rw [rateWindow,average_original order observation observation ⟨nonnegative,le_rfl⟩,
    average_original (order+1) observation observation ⟨nonnegative,le_rfl⟩,
    NativeWindowStressHeatTime.kernel_integral,NativeWindowStressHeatTime.kernel_integral]
  exact weighted_write seed observation nonnegative L F radius order

theorem global_green_write (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (nonnegative : 0 ≤ observation)
    (L F : Finset IntegerWavevector) (radius order : ℕ) :
    Tendsto (fun M => greenWindow seed observation L F radius order M) atTop
      (𝓝 (NativeWindowFiniteStressUniform.average (order+1) observation observation (diagonal seed observation L F radius))) := by
  rw [← rateWindow_write seed observation nonnegative L F radius order]
  exact global_green seed observation nonnegative L F radius order


def spectralValue (seed : GeneratedWholeRestartCurrent nu) (L : Finset IntegerWavevector) (sample : ℝ) : ℝ :=
  spectralForm nu L (state seed sample) (state seed sample)

theorem spectralValue_original (seed : GeneratedWholeRestartCurrent nu) (L : Finset IntegerWavevector) (sample : ℝ) :
    spectralValue seed L sample=∑ wave ∈ L,(1+nu.coeff*integerWaveViscousMultiplier wave)*
      ∑ coordinate : Coordinate,‖NativeUnheatedTriadRows.velocity seed sample wave coordinate‖^2 := by
  simp only [spectralValue,spectralForm,sum_apply,smul_apply,ContinuousLinearMap.bilinearComp_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro wave _
  apply Finset.sum_congr rfl
  intro coordinate _
  change _*inner ℝ (NativeUnheatedTriadRows.velocity seed sample wave coordinate) (NativeUnheatedTriadRows.velocity seed sample wave coordinate)=_
  rw [real_inner_self_eq_norm_sq]

theorem gradient_spectrum (seed : GeneratedWholeRestartCurrent nu) (L : Finset IntegerWavevector) (sample : ℝ) :
    (∑ wave ∈ L,integerWaveNormSq wave*∑ coordinate : Coordinate,‖NativeUnheatedTriadRows.velocity seed sample wave coordinate‖^2)=
      NativeUnheatedBandGradient.band (L.subtype (fun wave => wave≠0)) (NativeAbsoluteEventualControl.velocity seed sample) := by
  rw [← NativeUnheatedWindowStress.mass_band,NativeUnheatedStressProduct.projection_mass]
  simp only [NativeUnheatedStressProduct.density,NativeUnheatedStressProduct.amplitude,PiLp.norm_sq_eq_of_L2,
    ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity.euclideanCoordinateRow_apply,
    NativeUnheatedTriadRows.velocity_original,NativeUnifiedCompleteSource.velocity_read]

theorem spectralValue_bound (seed : GeneratedWholeRestartCurrent nu) (L : Finset IntegerWavevector) (sample : ℝ) :
    0 ≤ spectralValue seed L sample ∧ spectralValue seed L sample ≤ (1+nu.coeff*(2*Real.pi)^2)*
      NativeUnheatedBandGradient.band (L.subtype (fun wave => wave≠0)) (NativeAbsoluteEventualControl.velocity seed sample) := by
  rw [spectralValue_original,← gradient_spectrum]
  constructor
  · apply Finset.sum_nonneg
    intro wave _
    apply mul_nonneg _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    unfold integerWaveViscousMultiplier
    positivity [nu.coeff_pos,integerWaveNormSq_nonneg wave]
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro wave _
    by_cases zero : wave=0
    · subst wave
      simp [NativeUnheatedTriadRows.velocity_original,NativeEndpointVelocityCarrier.wholeVelocity_zero]
    · have factor : 1+nu.coeff*integerWaveViscousMultiplier wave ≤ (1+nu.coeff*(2*Real.pi)^2)*integerWaveNormSq wave := by
        unfold integerWaveViscousMultiplier
        nlinarith only [ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity.one_le_integerWaveNormSq wave zero]
      exact (mul_le_mul_of_nonneg_right factor (Finset.sum_nonneg fun _ _ => sq_nonneg _)).trans_eq (by ring)

def spectralWindow (seed : GeneratedWholeRestartCurrent nu) (L : Finset IntegerWavevector) (order : ℕ) (observation : ℝ) : ℝ :=
  NativeWindowFiniteStressUniform.average order observation observation (spectralValue seed L)

theorem spectralWindow_bound (seed : GeneratedWholeRestartCurrent nu) (L : Finset IntegerWavevector) (order : ℕ)
    (time horizon : ℝ) (inside : time∈Icc 0 horizon) : ‖spectralWindow seed L order time‖ ≤
      (1+nu.coeff*(2*Real.pi)^2)*kernelBound order*
        NativeUnheatedGlobalGradient.budget (NativeEventualTailControl.terminal seed) (horizon+2) := by
  rw [spectralWindow,average_original order time time ⟨inside.1,le_rfl⟩,
    ← average_original order time horizon inside,NativeWindowFiniteStressUniform.average]
  have bandContinuous : Continuous (fun sample => NativeUnheatedBandGradient.band (L.subtype (fun wave => wave≠0))
      (NativeAbsoluteEventualControl.velocity seed sample)) := NativeUnheatedBandGradient.band_curve_continuous
    (NativeFiniteMacroGlobal.coordinate_continuous (NativeEventualTailControl.terminal seed)) (L.subtype (fun wave => wave≠0))
  have paid := norm_integral_le_of_norm_le (μ := volume.restrict (Icc 0 (horizon+2)))
    (f := fun sample => NativeForwardWindowJets.kernelJet order (time-sample) • spectralValue seed L sample)
    ((bandContinuous.const_mul (kernelBound order*(1+nu.coeff*(2*Real.pi)^2))).integrableOn_Icc)
    (Eventually.of_forall fun sample => by
      rw [norm_smul,Real.norm_of_nonneg (spectralValue_bound seed L sample).1]
      exact (mul_le_mul (kernel_bounded order (time-sample)) (spectralValue_bound seed L sample).2
        (spectralValue_bound seed L sample).1 (kernelBound_positive order).le).trans_eq (by ring))
  rw [integral_const_mul] at paid
  have original := NativeUnheatedGlobalGradient.source_interval_bound seed 0 (horizon+2) le_rfl
    (by linarith [inside.1,inside.2]) (L.subtype (fun wave => wave≠0))
  rw [intervalIntegral.integral_of_le (by linarith [inside.1,inside.2] : 0 ≤ horizon+2),← integral_Icc_eq_integral_Ioc] at original
  apply paid.trans
  have scaled := mul_le_mul_of_nonneg_left original
    (show 0 ≤ kernelBound order*(1+nu.coeff*(2*Real.pi)^2) by positivity [kernelBound_positive order,nu.coeff_pos])
  nlinarith only [scaled]


def matrixWindow (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (radius order : ℕ) (observation : ℝ) : ℝ :=
  ∑ output : Coordinate,∑ input : Coordinate,inner ℝ (matrixField seed observation F radius output input)
    (NativeWindowStressHeatSource.physical (NativeWindowStressHeatTime.jet seed F output input order observation))

theorem matrixWindow_uniform (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    ∃ low : ℕ,∀ radius ≥ low,∀ outerRadius order time,time∈Icc 0 horizon →
      ‖matrixWindow seed (ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.integerWaveFrequencyCube outerRadius) radius order time‖ ≤
        9*(NativeWindowAugmentedPayment.stressBudget seed 0 horizon+1)*NativeWindowAugmentedPayment.stressBudget seed order horizon := by
  obtain ⟨low,paid⟩ := NativeWindowJointNormalForm.correctionJet_small seed 0 horizon nonnegative 1 (by norm_num)
  refine ⟨low,fun radius above outerRadius order time inside => ?_⟩
  let F:=ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.integerWaveFrequencyCube outerRadius
  have S (n : ℕ) (output input : Coordinate) : ‖NativeWindowStressHeatSource.physical
      (NativeWindowStressHeatTime.jet seed F output input n time)‖ ≤ NativeWindowAugmentedPayment.stressBudget seed n horizon := by
    rw [← NativeWindowAugmentedPayment.stressJet_original seed outerRadius n time inside.1]
    exact NativeWindowAugmentedPayment.stressJet_bound seed outerRadius n time horizon inside output input
  have S0 : 0 ≤ NativeWindowAugmentedPayment.stressBudget seed 0 horizon := (norm_nonneg _).trans (S 0 0 0)
  have T (output input : Coordinate) : ‖matrixField seed time F radius output input‖ ≤
      NativeWindowAugmentedPayment.stressBudget seed 0 horizon+1 := by
    have small := (paid radius above F time inside output input).le
    rw [NativeWindowJointNormalForm.correctionJet_zero] at small
    have original := S 0 output input
    rw [NativeWindowStressHeatTime.jet_zero] at original
    exact (norm_add_le _ _).trans (add_le_add original small)
  have row (output input : Coordinate) : ‖inner ℝ (matrixField seed time F radius output input)
      (NativeWindowStressHeatSource.physical (NativeWindowStressHeatTime.jet seed F output input order time))‖ ≤
        (NativeWindowAugmentedPayment.stressBudget seed 0 horizon+1)*NativeWindowAugmentedPayment.stressBudget seed order horizon := by
    rw [Real.norm_eq_abs]
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul (T output input) (S order output input) (norm_nonneg _) (by linarith))
  apply (norm_sum_le _ _).trans
  apply (Finset.sum_le_sum (fun output _ => norm_sum_le _ _)).trans
  exact (Finset.sum_le_sum (fun output _ => Finset.sum_le_sum (fun input _ => row output input))).trans_eq (by simp; ring)

theorem energyWindow_uniform (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    ∃ low : ℕ,∀ radius ≥ low,∀ outerRadius (L : Finset IntegerWavevector) order time,time∈Icc 0 horizon →
      ‖spectralWindow seed L order time+
        matrixWindow seed (ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.integerWaveFrequencyCube outerRadius) radius order time‖ ≤
      (1+nu.coeff*(2*Real.pi)^2)*kernelBound order*NativeUnheatedGlobalGradient.budget (NativeEventualTailControl.terminal seed) (horizon+2)+
        9*(NativeWindowAugmentedPayment.stressBudget seed 0 horizon+1)*NativeWindowAugmentedPayment.stressBudget seed order horizon := by
  obtain ⟨low,paid⟩ := matrixWindow_uniform seed horizon nonnegative
  exact ⟨low,fun radius above outerRadius L order time inside => (norm_add_le _ _).trans
    (add_le_add (spectralWindow_bound seed L order time horizon inside) (paid radius above outerRadius order time inside))⟩


open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem diagonalWindow_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (observation : ℝ) (nonnegative : 0 ≤ observation)
    (L F : Finset IntegerWavevector) (radius order : ℕ) :
    NativeWindowFiniteStressUniform.average order (step.2.clockAdvance+observation) (step.2.clockAdvance+observation)
      (diagonal seed (step.2.clockAdvance+observation) L F radius)=
    NativeWindowFiniteStressUniform.average order observation observation (diagonal step.1 observation L F radius) := by
  rw [average_original order (step.2.clockAdvance+observation) (step.2.clockAdvance+observation)
    ⟨add_nonneg step.2.clockAdvance_pos.le nonnegative,le_rfl⟩,average_original order observation observation ⟨nonnegative,le_rfl⟩]
  apply integral_congr_ae
  filter_upwards with shift
  by_cases zero : NativeForwardWindowJets.kernelJet order shift=0
  · simp only [zero,zero_smul]
  · have support := NativeUnheatedWindowJensen.kernel_support order shift zero
    rw [add_sub_assoc,diagonal_next seed step generated observation (observation-shift) nonnegative (by linarith [support.2]) L F radius]

theorem rateWindow_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (observation : ℝ) (nonnegative : 0 ≤ observation)
    (L F : Finset IntegerWavevector) (radius order : ℕ) :
    rateWindow seed (step.2.clockAdvance+observation) L F radius order=rateWindow step.1 observation L F radius order := by
  rw [rateWindow_write seed _ (add_nonneg step.2.clockAdvance_pos.le nonnegative),
    rateWindow_write step.1 observation nonnegative,diagonalWindow_next seed step generated observation nonnegative]

end
end SaturationMonoid.NavierStokes.NativeWindowAugmentedGlobalGreen
