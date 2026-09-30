import H0mework.NavierStokes.WindowHistoryCreation.Source
import H0mework.NavierStokes.WindowSchurMean.Blocks

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryMeanDrift
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open NativeFiniteActionResolvent NativeWholeResolvent NativePhysicalPairing NativeCommonAdvectorAction
open NativePhysicalFourier
open NativeWindowStressHeatSource (physical)
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativeWindowOperatorGreen (laplacian)
open NativeWindowHistoryMeanAction (meanValue meanOperator frozen)
open NativeWindowHistoryMeanBlocks (diffusion)
open NativeWindowHistoryCreationGeometry (transport square gradientSquare)
open NativeWindowHistoryCreationSource (budget)
noncomputable section
local instance physicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance physicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
variable {nu : Viscosity}

theorem mean_square_le_stress (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ)
    (nonnegative : 0≤time) (point : Torus) :
    square (modes M) (meanValue seed M time) point≤NativeWindowTraceGradient.traceStress seed time (integerWaveFrequencyCube M) point := by
  have same : NativeWindowHistoryCreationCovariance.trace seed M time point=
      NativeWindowTraceGradient.traceStress seed time (integerWaveFrequencyCube M) point-
        square (modes M) (meanValue seed M time) point := by
    rw [NativeWindowHistoryCreationCovariance.trace_matrix,NativeWindowTraceGradient.traceStress,square]
    simp only [ContinuousMap.sum_apply,ContinuousMap.mul_apply]
    simp_rw [NativeWindowHistoryCreationCovariance.covariance_diagonal seed M time nonnegative,Finset.sum_sub_distrib,pow_two]
  linarith only [same,NativeWindowHistoryCreationCovariance.trace_nonnegative seed M time point]

theorem source_gradient_form (seed : GeneratedWholeRestartCurrent nu) (horizon epsilon : ℝ) (positive : 0<epsilon)
    (M : ℕ) (time : ℝ) (inside : time∈Icc 0 horizon) (v : physicalSpace (modes M)) :
    (∫point : Torus,NativeWindowTraceGradient.traceStress seed time (integerWaveFrequencyCube M) point*
      gradientSquare (modes M) (modes_zero M) (modes_closed M) v point)≤
      epsilon*pairing (modes M) (laplacian (modes M) (modes_zero M) (modes_closed M) nu v)
        (laplacian (modes M) (modes_zero M) (modes_closed M) nu v)+budget seed horizon epsilon*curlPair (modes M) v.1 v.1 := by
  have absorbed:=NativeWindowHistoryCreationGeometry.gradient_absorption
    (NativeWindowTraceGradient.traceStress seed time (integerWaveFrequencyCube M)) (modes M) (modes_zero M) (modes_closed M) nu v epsilon positive
  have power:=pow_le_pow_left₀ (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
    (mul_le_mul_of_nonneg_left (NativeWindowHistoryCreationSource.trace_bound seed M time horizon inside)
      (Real.sqrt_nonneg NativeWindowGreenTestForm.testKernel.cap)) 8
  have cap : NativeWindowHistoryCreationForm.budget
      ‖physical (NativeWindowTraceGradient.traceStress seed time (integerWaveFrequencyCube M))‖ (epsilon*(2*Real.pi)^2)≤budget seed horizon epsilon := by
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right power (by positivity))
  have gradient0 : 0≤curlPair (modes M) v.1 v.1 := by
    rw [← NativeDualCurlResolvent.gradient_norm_sq (modes M) (modes_zero M)]
    exact sq_nonneg _
  exact absorbed.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right cap gradient0))

def drift (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : wholePhysical →L[ℝ] wholePhysical :=
  meanOperator seed M time-diffusion nu M

theorem drift_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : wholePhysical) :
    drift seed M time v=includeCLM (modes M) (modes_closed M)
      (transport (modes M) (modes_zero M) (modes_closed M) nu (meanValue seed M time)
        (restrictCLM (modes M) (modes_zero M) (modes_closed M) v)) := by
  simp only [drift,sub_apply,meanOperator,diffusion,NativeWindowHistoryOseen.lift,ContinuousLinearMap.comp_apply]
  rw [← map_sub]
  change includeCLM (modes M) (modes_closed M) ((frozen nu M (meanValue seed M time)-frozen nu M 0)
    (restrictCLM (modes M) (modes_zero M) (modes_closed M) v))=_
  rw [NativeWindowHistoryCreationSource.frozen_transport,sub_zero]

theorem drift_stress_bound (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ)
    (nonnegative : 0≤time) (v : physicalSpace (modes M)) :
    ‖drift seed M time (includeCLM (modes M) (modes_closed M) v)‖^2≤
      ∫point : Torus,NativeWindowTraceGradient.traceStress seed time (integerWaveFrequencyCube M) point*
        gradientSquare (modes M) (modes_zero M) (modes_closed M) v point := by
  rw [drift_original,restrict_include,include_norm (modes M) (modes_zero M)]
  apply (NativeWindowHistoryCreationGeometry.transport_bound (modes M) (modes_zero M) (modes_closed M) nu _ v).trans
  have square0 (point : Torus) : 0 ≤ square (modes M) (meanValue seed M time) point := by
    simp only [square,ContinuousMap.sum_apply,ContinuousMap.mul_apply]
    exact Finset.sum_nonneg fun _ _ => mul_self_nonneg _
  apply integral_mono_of_nonneg (Eventually.of_forall fun point => mul_nonneg
    (square0 point) (NativeWindowHistoryCreationSource.gradientSquare_nonnegative _ _ _ v point))
    (((NativeWindowTraceGradient.traceStress seed time (integerWaveFrequencyCube M)).continuous.mul
      (gradientSquare (modes M) (modes_zero M) (modes_closed M) v).continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))
  exact Eventually.of_forall fun point => mul_le_mul_of_nonneg_right (mean_square_le_stress seed M time nonnegative point)
    (NativeWindowHistoryCreationSource.gradientSquare_nonnegative _ _ _ v point)

theorem source_drift_bound (seed : GeneratedWholeRestartCurrent nu) (horizon epsilon : ℝ) (positive : 0<epsilon)
    (M : ℕ) (time : ℝ) (inside : time∈Icc 0 horizon) (v : physicalSpace (modes M)) :
    ‖drift seed M time (includeCLM (modes M) (modes_closed M) v)‖^2≤
      epsilon*pairing (modes M) (laplacian (modes M) (modes_zero M) (modes_closed M) nu v)
        (laplacian (modes M) (modes_zero M) (modes_closed M) nu v)+budget seed horizon epsilon*curlPair (modes M) v.1 v.1 :=
  (drift_stress_bound seed M time inside.1 v).trans (source_gradient_form seed horizon epsilon positive M time inside v)

theorem source_whole_bound (seed : GeneratedWholeRestartCurrent nu) (horizon epsilon : ℝ) (positive : 0<epsilon)
    (M : ℕ) (time : ℝ) (inside : time∈Icc 0 horizon) (v : wholePhysical) :
    let vM:=restrictCLM (modes M) (modes_zero M) (modes_closed M) v
    ‖drift seed M time v‖^2≤epsilon*pairing (modes M)
      (laplacian (modes M) (modes_zero M) (modes_closed M) nu vM)
      (laplacian (modes M) (modes_zero M) (modes_closed M) nu vM)+budget seed horizon epsilon*curlPair (modes M) vM.1 vM.1 := by
  dsimp only
  simpa only [drift_original,restrict_include] using!
    source_drift_bound seed horizon epsilon positive M time inside (restrictCLM (modes M) (modes_zero M) (modes_closed M) v)

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem drift_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0≤time) :
    drift seed M (step.2.clockAdvance+time)=drift step.1 M time :=
  congrArg (fun A : wholePhysical →L[ℝ] wholePhysical => A-diffusion nu M)
    (congrArg Prod.fst (NativeWindowHistoryMeanBlocks.blocks_next seed M step generated time nonnegative))

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryMeanDrift
