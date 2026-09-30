import H0mework.Versions.X.NavierStokes.WindowStressHeat.Balance
import H0mework.Versions.X.NavierStokes.UnheatedWriterTail.Quadratic

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowStressOseenApprox
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativePhysicalFourier NativeCompleteStressAction NativeResolventCompactness NativeUnheatedSourceGradient
open NativeUnheatedSourceQuadraticApprox NativeUnheatedSourceWeightedTail
open NativeWindowStressHeatTime NativeWindowStressHeatBalance NativeUnheatedStressPairEvolution
noncomputable section
variable {nu : Viscosity}

def pairRead (F : Finset IntegerWavevector) (output input : Coordinate) : State →L[ℝ] FullSpace →L[ℝ] C(Torus,ℝ) :=
  (ContinuousLinearMap.mul ℝ C(Torus,ℝ)).bilinearComp (NativeWindowStressHeatTime.read F output) (NativeWindowFiniteGramFourier.read F input)+
  (ContinuousLinearMap.mul ℝ C(Torus,ℝ)).bilinearComp (NativeWindowStressHeatTime.read F input) (NativeWindowFiniteGramFourier.read F output)

theorem pairRead_apply (F : Finset IntegerWavevector) (output input : Coordinate) (N : State) (U : FullSpace) :
    pairRead F output input N U = NativeWindowStressHeatTime.read F output N*NativeWindowFiniteGramFourier.read F input U+
      NativeWindowStressHeatTime.read F input N*NativeWindowFiniteGramFourier.read F output U := rfl

theorem pairRead_original (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector)
    (output input : Coordinate) : pairRead F output input (nonlinear seed time) (NativeUnifiedCompleteSource.source seed time) =
      nonlinearPair seed F output input time := by
  simp only [pairRead_apply,nonlinearPair,fieldAction,field_original]
  rw [mul_comm _ ((NativeWindowFiniteGramFourier.read F output) _)]

def pair (radius : ℕ) (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector)
    (output input : Coordinate) : C(Torus,ℝ) :=
  pairRead F output input (value radius seed time) (NativeUnifiedCompleteSource.source seed time)

theorem projected_action_row (radius : ℕ) (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (wave : IntegerWavevector) (coordinate : Coordinate) :
    let U := NativeEndpointVelocityCarrier.wholeVelocity (NativeWholeH1Approximation.project radius (physicalSource seed time)).1
    NativeUnheatedTriadRows.decode wave coordinate (value radius seed time) =
      NativeTimeJetCarrier.projectedDivergenceCLM wave (NativeHigherTimeJets.mixedFlux U U wave) coordinate := by
  rw [NativeUnheatedTriadRows.decode_apply,value,NativeUnheatedCubicRows.negative_row]
  simp only [Pi.smul_apply]
  by_cases zero : wave = 0
  · simp only [zero,NativeUnheatedCubicRows.row_zero,Pi.zero_apply,smul_zero]
    simp [NativeTimeJetCarrier.projectedDivergenceCLM_apply,ThreeDimensionalVorticityCoefficientRawSourceCore.transverseProjection]
  · exact smul_inv_smul₀ (NativeUnheatedPairNegativeKernel.root_positive wave zero).ne' _

theorem pair_projected (radius : ℕ) (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (F : Finset IntegerWavevector) (output input : Coordinate) :
    let U := NativeEndpointVelocityCarrier.wholeVelocity (NativeWholeH1Approximation.project radius (physicalSource seed time)).1
    let N := fun wave => NativeTimeJetCarrier.projectedDivergenceCLM wave (NativeHigherTimeJets.mixedFlux U U wave)
    pair radius seed time F output input =
      (∑ wave ∈ F, basis wave (N wave output))*field seed F input time+
      (∑ wave ∈ F, basis wave (N wave input))*field seed F output time := by
  simp only [pair,pairRead_apply,NativeWindowStressHeatBalance.read_apply,projected_action_row,field_original]

theorem pair_tendsto_ae (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (output input : Coordinate) :
    ∀ᵐ time : ℝ, 0 ≤ time → Tendsto (fun radius => pair radius seed time F output input) atTop
      (𝓝 (nonlinearPair seed F output input time)) := by
  filter_upwards [value_tendsto_ae seed] with time actual nonnegative
  rw [← pairRead_original]
  exact ((pairRead F output input).flip (NativeUnifiedCompleteSource.source seed time)).continuous.tendsto _ |>.comp (actual nonnegative)

def pairBudget (F : Finset IntegerWavevector) (output input : Coordinate) : ℝ :=
  ‖NativeWindowStressHeatTime.read F output‖*‖NativeWindowFiniteGramFourier.read F input‖+
    ‖NativeWindowStressHeatTime.read F input‖*‖NativeWindowFiniteGramFourier.read F output‖

theorem pairRead_bound (F : Finset IntegerWavevector) (output input : Coordinate) (N : State) (U : FullSpace) :
    ‖pairRead F output input N U‖ ≤ pairBudget F output input*‖N‖*‖U‖ := by
  have term (left right : Coordinate) : ‖NativeWindowStressHeatTime.read F left N*NativeWindowFiniteGramFourier.read F right U‖ ≤
      (‖NativeWindowStressHeatTime.read F left‖*‖NativeWindowFiniteGramFourier.read F right‖)*‖N‖*‖U‖ :=
    (norm_mul_le _ _).trans ((mul_le_mul ((NativeWindowStressHeatTime.read F left).le_opNorm N)
      ((NativeWindowFiniteGramFourier.read F right).le_opNorm U) (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans_eq (by ring))
  rw [pairRead_apply]
  exact (norm_add_le _ _).trans ((add_le_add (term output input) (term input output)).trans_eq (by unfold pairBudget; ring))

def cap (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (output input : Coordinate) : ℝ :=
  pairBudget F output input*Real.sqrt NativeMovingCriticalProductWeights.constant*NativeUnifiedCompleteSource.budget seed

theorem pair_bound_ae (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (output input : Coordinate) :
    ∀ᵐ time : ℝ, 0 ≤ time → ∀ radius,
      ‖pair radius seed time F output input‖ ≤ cap seed F output input*mass seed time := by
  filter_upwards [value_bound_ae seed] with time bound nonnegative radius
  apply (pairRead_bound F output input _ _).trans
  have positive : 0 ≤ pairBudget F output input := by unfold pairBudget; positivity
  exact (mul_le_mul (mul_le_mul_of_nonneg_left (bound nonnegative radius) positive)
    (NativeUnifiedCompleteSource.source_bound seed time) (norm_nonneg _)
      (mul_nonneg positive (mul_nonneg (Real.sqrt_nonneg _) (mass_nonnegative seed time)))).trans_eq (by unfold cap; ring)

theorem pair_measurable (radius : ℕ) (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (output input : Coordinate) : AEStronglyMeasurable (fun time => pair radius seed time F output input) (volume : Measure ℝ) :=
  (pairRead F output input).aestronglyMeasurable_comp₂ (value_measurable radius seed) (NativeUnifiedCompleteSource.source_measurable seed)

def window (radius : ℕ) (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector)
    (output input : Coordinate) : C(Torus,ℝ) :=
  -(∫ actual in time+1..time+2, kernelWeight 0 time 0 actual • pair radius seed actual F output input)

theorem window_tendsto (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (nonnegative : 0 ≤ time)
    (F : Finset IntegerWavevector) (output input : Coordinate) :
    Tendsto (fun radius => window radius seed time F output input) atTop
      (𝓝 (nonlinearWindow seed time F output input)) := by
  have order : time+1 ≤ time+2 := by linarith
  have subset : Icc (time+1) (time+2) ⊆ Icc 0 (time+2) := fun _ inside => ⟨by linarith [inside.1],inside.2⟩
  have source : IntegrableOn (mass seed) (Icc (time+1) (time+2)) (volume : Measure ℝ) :=
    (show IntegrableOn (mass seed) (Icc 0 (time+2)) (volume : Measure ℝ) from mass_integrable seed (time+2) (by linarith)).mono_set subset
  have majorant : IntegrableOn (fun actual => ‖kernelWeight 0 time 0 actual‖*(cap seed F output input*mass seed actual))
      (Icc (time+1) (time+2)) := IntegrableOn.continuousOn_mul (kernelWeight_continuous 0 time 0).norm.continuousOn
        (source.const_mul _) isCompact_Icc
  have measured (radius : ℕ) : AEStronglyMeasurable
      (fun actual => kernelWeight 0 time 0 actual • pair radius seed actual F output input)
      (volume.restrict (Icc (time+1) (time+2))) := by
    exact (kernelWeight_continuous 0 time 0).aestronglyMeasurable.restrict.smul (pair_measurable radius seed F output input).restrict
  have generated := tendsto_integral_of_dominated_convergence
    (fun actual => ‖kernelWeight 0 time 0 actual‖*(cap seed F output input*mass seed actual))
    measured
    majorant (fun radius => by
      filter_upwards [ae_restrict_of_ae (pair_bound_ae seed F output input),ae_restrict_mem measurableSet_Icc] with actual bound inside
      simp only [norm_smul]
      exact mul_le_mul_of_nonneg_left (bound (subset inside).1 radius) (norm_nonneg _)) (by
      filter_upwards [ae_restrict_of_ae (pair_tendsto_ae seed F output input),ae_restrict_mem measurableSet_Icc] with actual converges inside
      simpa only [Pi.smul_apply] using! (converges (subset inside).1).const_smul (kernelWeight 0 time 0 actual))
  unfold window nonlinearWindow
  simp_rw [intervalIntegral.integral_of_le order,← integral_Icc_eq_integral_Ioc]
  exact generated.neg

def work (radius : ℕ) (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector) : ℝ :=
  ∑ output : Coordinate, ∑ input : Coordinate, inner ℝ (sigma seed F output input time)
    (NativeWindowStressHeatSource.physical (window radius seed time F output input))

theorem work_tendsto (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (nonnegative : 0 ≤ time)
    (F : Finset IntegerWavevector) : Tendsto (fun radius => work radius seed time F) atTop (𝓝 (nonlinearWork seed time F)) := by
  apply tendsto_finsetSum
  intro output _
  apply tendsto_finsetSum
  intro input _
  exact (((innerSL ℝ (sigma seed F output input time)).comp NativeWindowStressHeatSource.physical).continuous.tendsto _).comp
    (window_tendsto seed time nonnegative F output input)

open SourceGeneratedNativeResponseDisposition ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem window_next (radius : ℕ) (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some step) (time : ℝ) (nonnegative : 0 ≤ time)
    (F : Finset IntegerWavevector) (output input : Coordinate) :
    window radius seed (step.2.clockAdvance+time) F output input = window radius step.1 time F output input := by
  simp only [window,← kernel_integral]
  apply congrArg Neg.neg
  apply integral_congr_ae
  filter_upwards with shift
  by_cases zero : NativeForwardWindowJets.kernelJet 0 shift = 0
  · simp only [zero,zero_smul]
  · have later : 0 ≤ time-shift := by linarith [NativeForwardWindowJets.kernelJet_nonpositive 0 shift zero]
    simp only [pair,add_sub_assoc,value_next radius seed step generated (time-shift) later,
      NativeUnifiedCompleteSource.source_generated_next seed step generated (time-shift) later]

theorem work_next (radius : ℕ) (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some step) (time : ℝ) (nonnegative : 0 ≤ time)
    (F : Finset IntegerWavevector) : work radius seed (step.2.clockAdvance+time) F = work radius step.1 time F := by
  simp only [work,sigma,NativeWindowFiniteGramFourier.stress_next seed step generated time nonnegative,
    window_next radius seed step generated time nonnegative]

end
end SaturationMonoid.NavierStokes.NativeWindowStressOseenApprox
