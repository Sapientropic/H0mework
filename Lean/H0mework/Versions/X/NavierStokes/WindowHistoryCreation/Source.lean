import H0mework.Versions.X.NavierStokes.WindowHistoryCreation.Covariance

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryCreationSource
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open NativeFiniteActionResolvent NativeWholeResolvent NativePhysicalPairing NativeCommonAdvectorAction
open NativePhysicalFourier
open NativeWindowStressHeatSource (physical)
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativeWindowOperatorGreen (laplacian)
open NativeWindowHistoryMeanAction (creation frozen meanValue)
open NativeWindowHistoryCreationCovariance (centered trace trace_integrable)
open NativeWindowHistoryCreationGeometry (transport square gradientSquare)
open NativeWindowTraceAdjoint (value)
open NativeForwardWindowPairingReadout (averageMeasure)
noncomputable section
local instance physicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance physicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
variable {nu : Viscosity}

theorem frozen_transport (nu : Viscosity) (M : ℕ) (u w v : physicalSpace (modes M)) :
    (frozen nu M u-frozen nu M w) v=transport (modes M) (modes_zero M) (modes_closed M) nu (u-w) v := by
  apply Subtype.ext
  rw [NativeWindowHistoryMeanAction.frozen_difference,NativeWindowTraceAdjoint.curlMap_apply]
  rfl

theorem creation_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : physicalSpace (modes M)) :
    creation seed M time (includeCLM (modes M) (modes_closed M) v)=ᵐ[averageMeasure] fun lag =>
      includeCLM (modes M) (modes_closed M)
        (transport (modes M) (modes_zero M) (modes_closed M) nu (centered seed M time (time-lag)) v) := by
  filter_upwards [NativeWindowHistoryMeanAction.creation_ae seed M time (includeCLM (modes M) (modes_closed M) v)] with lag original
  rw [original,NativeWindowHistoryOseen.lift,ContinuousLinearMap.comp_apply,ContinuousLinearMap.comp_apply,restrict_include,frozen_transport]
  rfl

theorem creation_restrict (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : wholePhysical) :
    creation seed M time v=creation seed M time (includeCLM (modes M) (modes_closed M)
      (restrictCLM (modes M) (modes_zero M) (modes_closed M) v)) := by
  apply Lp.ext
  filter_upwards [NativeWindowHistoryMeanAction.creation_ae seed M time v,
    NativeWindowHistoryMeanAction.creation_ae seed M time (includeCLM (modes M) (modes_closed M)
      (restrictCLM (modes M) (modes_zero M) (modes_closed M) v))] with lag first last
  rw [first,last]
  simp only [NativeWindowHistoryOseen.lift,ContinuousLinearMap.comp_apply,restrict_include]

private theorem physical_testing (f w : C(Torus,ℝ)) :
    ((innerSL ℝ (physical w)).comp physical) f=∫point : Torus,f point*w point := by
  rw [ContinuousLinearMap.comp_apply,innerSL_apply_apply,NativeWindowStressHeatSource.physical_inner]
  apply integral_congr_ae
  filter_upwards with point
  ring

theorem covariance_bound (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : physicalSpace (modes M)) :
    ‖creation seed M time (includeCLM (modes M) (modes_closed M) v)‖^2≤
      ∫point : Torus,trace seed M time point*gradientSquare (modes M) (modes_zero M) (modes_closed M) v point := by
  let read:=(innerSL ℝ (physical (gradientSquare (modes M) (modes_zero M) (modes_closed M) v))).comp physical
  have first:Integrable (fun lag => ‖coefficients (modes M)
      (transport (modes M) (modes_zero M) (modes_closed M) nu (centered seed M time (time-lag)) v)‖^2) averageMeasure := by
    have paid:=(Lp.memLp (creation seed M time (includeCLM (modes M) (modes_closed M) v))).integrable_norm_pow (by decide : (2:ℕ)≠0)
    apply paid.congr
    filter_upwards [creation_original seed M time v] with lag original
    rw [original,include_norm (modes M) (modes_zero M) (modes_closed M)]
  have last:Integrable (fun lag => read (square (modes M) (centered seed M time (time-lag)))) averageMeasure :=
    read.integrable_comp (trace_integrable seed M time)
  have paid:=integral_mono_ae first last (Eventually.of_forall fun lag =>
    (NativeWindowHistoryCreationGeometry.transport_bound (modes M) (modes_zero M) (modes_closed M) nu _ v).trans_eq
      (physical_testing _ _).symm)
  have native:‖creation seed M time (includeCLM (modes M) (modes_closed M) v)‖^2=
      ∫lag,‖coefficients (modes M) (transport (modes M) (modes_zero M) (modes_closed M) nu
        (centered seed M time (time-lag)) v)‖^2 ∂averageMeasure := by
    rw [NativeWindowTraceWholeHistory.norm_square]
    apply integral_congr_ae
    filter_upwards [creation_original seed M time v] with lag original
    rw [original,include_norm (modes M) (modes_zero M) (modes_closed M)]
  rw [native]
  exact paid.trans_eq ((read.integral_comp_comm (trace_integrable seed M time)).trans (physical_testing _ _))

theorem gradientSquare_nonnegative (M : Finset IntegerWavevector) (zero : 0∉M)
    (closed : FiniteModeNegClosed M) (v : physicalSpace M) (point : Torus) :
    0≤gradientSquare M zero closed v point := by
  change 0≤∑ j : Coordinate,∑ i : Coordinate,NativeWindowStressOseenTest.evaluate M M i
    (NativeWindowAugmentedGradient.derivative M zero closed j v) point*
      NativeWindowStressOseenTest.evaluate M M i (NativeWindowAugmentedGradient.derivative M zero closed j v) point
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => mul_self_nonneg _

theorem stress_bound (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (nonnegative : 0≤time)
    (v : physicalSpace (modes M)) : ‖creation seed M time (includeCLM (modes M) (modes_closed M) v)‖^2≤
      ∫point : Torus,NativeWindowTraceGradient.traceStress seed time (integerWaveFrequencyCube M) point*
        gradientSquare (modes M) (modes_zero M) (modes_closed M) v point := by
  apply (covariance_bound seed M time v).trans
  apply integral_mono_of_nonneg (Eventually.of_forall fun point => mul_nonneg
    (NativeWindowHistoryCreationCovariance.trace_nonnegative seed M time point) (gradientSquare_nonnegative _ _ _ v point))
    (((NativeWindowTraceGradient.traceStress seed time (integerWaveFrequencyCube M)).continuous.mul
      (gradientSquare (modes M) (modes_zero M) (modes_closed M) v).continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))
  exact Eventually.of_forall fun point => mul_le_mul_of_nonneg_right
    (NativeWindowHistoryCreationCovariance.trace_le_stress seed M time nonnegative point) (gradientSquare_nonnegative _ _ _ v point)

def densityBudget (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) : ℝ :=
  max 0 (3*NativeWindowAugmentedPayment.stressBudget seed 0 horizon)

theorem trace_bound (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time horizon : ℝ) (inside : time∈Icc 0 horizon) :
    ‖physical (NativeWindowTraceGradient.traceStress seed time (integerWaveFrequencyCube M))‖≤densityBudget seed horizon := by
  rw [NativeWindowTraceGradient.traceStress,map_sum]
  apply (norm_sum_le _ _).trans
  have row (i : Coordinate) : ‖physical (NativeWindowFiniteGramFourier.stress seed time (integerWaveFrequencyCube M) i i)‖≤
      NativeWindowAugmentedPayment.stressBudget seed 0 horizon := by
    have paid:=NativeWindowAugmentedPayment.stressJet_bound seed M 0 time horizon inside i i
    rw [NativeWindowAugmentedPayment.stressJet_original seed M 0 time inside.1,NativeWindowStressHeatTime.jet_zero] at paid
    exact paid
  exact ((Finset.sum_le_sum fun i _ => row i).trans_eq (by simp)).trans (le_max_right _ _)

def budget (seed : GeneratedWholeRestartCurrent nu) (horizon epsilon : ℝ) : ℝ :=
  NativeWindowHistoryCreationForm.budget (densityBudget seed horizon) (epsilon*(2*Real.pi)^2)

theorem source_creation_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (epsilon : ℝ) (positive : 0<epsilon)
    (M : ℕ) (time : ℝ) (inside : time∈Icc 0 horizon) (v : physicalSpace (modes M)) :
    ‖creation seed M time (includeCLM (modes M) (modes_closed M) v)‖^2≤
      epsilon*pairing (modes M) (laplacian (modes M) (modes_zero M) (modes_closed M) nu v)
        (laplacian (modes M) (modes_zero M) (modes_closed M) nu v)+budget seed horizon epsilon*curlPair (modes M) v.1 v.1 := by
  apply ((stress_bound seed M time inside.1 v).trans
    (NativeWindowHistoryCreationGeometry.gradient_absorption _ (modes M) (modes_zero M) (modes_closed M) nu v epsilon positive)).trans
  have coefficient:=trace_bound seed M time horizon inside
  have power:=pow_le_pow_left₀ (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
    (mul_le_mul_of_nonneg_left coefficient (Real.sqrt_nonneg NativeWindowGreenTestForm.testKernel.cap)) 8
  have cap:NativeWindowHistoryCreationForm.budget
      ‖physical (NativeWindowTraceGradient.traceStress seed time (integerWaveFrequencyCube M))‖ (epsilon*(2*Real.pi)^2)≤budget seed horizon epsilon := by
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right power (by positivity))
  have gradient0:0≤curlPair (modes M) v.1 v.1 := by
    rw [NativeWindowHistoryCreationGeometry.curl_mass (modes M) (modes_zero M)]
    exact mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun k _ => mul_nonneg (integerWaveNormSq_nonneg k)
      (Finset.sum_nonneg fun _ _ => sq_nonneg _))
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_right cap gradient0)

theorem budget_nonnegative (seed : GeneratedWholeRestartCurrent nu) (horizon epsilon : ℝ) (positive : 0<epsilon) :
    0≤budget seed horizon epsilon := by unfold budget NativeWindowHistoryCreationForm.budget; positivity

theorem source_whole_bound (seed : GeneratedWholeRestartCurrent nu) (horizon epsilon : ℝ) (positive : 0<epsilon)
    (M : ℕ) (time : ℝ) (inside : time∈Icc 0 horizon) (v : wholePhysical) :
    let vM:=restrictCLM (modes M) (modes_zero M) (modes_closed M) v
    ‖creation seed M time v‖^2≤epsilon*pairing (modes M)
      (laplacian (modes M) (modes_zero M) (modes_closed M) nu vM)
      (laplacian (modes M) (modes_zero M) (modes_closed M) nu vM)+budget seed horizon epsilon*curlPair (modes M) vM.1 vM.1 := by
  dsimp only
  rw [creation_restrict seed M time v]
  exact source_creation_bound seed horizon epsilon positive M time inside _

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem creation_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0≤time) :
    creation seed M (step.2.clockAdvance+time)=creation step.1 M time :=
  congrArg (fun A : NativeWindowHistoryOseen.H →L[ℝ] NativeWindowHistoryOseen.H =>
    NativeWindowHistoryMeanProjection.residual.comp (A.comp NativeWindowHistoryMeanProjection.embed))
    (congrArg Prod.fst (NativeWindowHistoryOseen.whole_next seed M step generated time nonnegative))

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryCreationSource
