import H0mework.Versions.X.NavierStokes.WindowSchurAbsolute.PhysicalCurrent

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowAbsoluteTimePhysicalLimit
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWholeResolvent (wholePhysical)
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativeWindowAbsoluteTimePhysicalCurrent (stressCoefficient current current_fourier)
open NativeForwardWindowPairingReadout (averageMeasure)
open NativeWindowTraceWholeHistory (history finiteHistory projection)
noncomputable section
variable {nu : Viscosity}

theorem projection_velocity (M : ℕ) (v : wholePhysical) :
    NativeEndpointVelocityCarrier.wholeVelocity (projection M v).1=
      complexSharpSupportProjection (modes M) (NativeEndpointVelocityCarrier.wholeVelocity v.1) := by
  change NativeEndpointVelocityCarrier.wholeVelocity
    (ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity.puncturedEuclideanize
      (NativeWholeResolvent.restrictCLM (modes M) (modes_zero M) (modes_closed M) v).1)=_
  rw [NativeRecoveryPhysical.wholeVelocity_puncturedEuclideanize _
    (NativeFiniteActionResolvent.physical_supported
      (NativeWholeResolvent.restrictCLM (modes M) (modes_zero M) (modes_closed M) v) 0 (modes_zero M))]
  rfl

theorem projection_stress (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (s : ℝ) :
    NativeWindowHistoryCovarianceRecovery.fiber (projection M (NativeWindowTraceWholeHistory.original seed s))
      (projection M (NativeWindowTraceWholeHistory.original seed s))=
        NativeUnheatedWindowStress.finiteStress seed (modes M) s := by
  change NativeCompleteStressBilinear.mixed
    (NativeEndpointVelocityCarrier.wholeVelocity (projection M (NativeWindowTraceWholeHistory.original seed s)).1)
    (NativeEndpointVelocityCarrier.wholeVelocity (projection M (NativeWindowTraceWholeHistory.original seed s)).1)=_
  rw [projection_velocity]
  change NativeCompleteStressBilinear.mixed
    (complexSharpSupportProjection (modes M) (NativeEndpointVelocityCarrier.wholeVelocity (NativeUnifiedCompleteSource.source seed s).fst))
    (complexSharpSupportProjection (modes M) (NativeEndpointVelocityCarrier.wholeVelocity (NativeUnifiedCompleteSource.source seed s).fst))=_
  rw [NativeUnifiedCompleteSource.velocity_read]
  rfl

theorem coefficient_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ)
    (k : IntegerWavevector) (i j : Coordinate) :
    stressCoefficient seed M time k i j=NativeCompleteStressCarrier.read
      (NativeWindowHistoryCovarianceRecovery.stress (finiteHistory seed time M)) k i j := by
  let h:=finiteHistory seed time M
  let B:=NativeWindowHistoryCovarianceRecovery.fiber
  have paid:Integrable (fun lag => B (h lag) (h lag)) averageMeasure :=
    memLp_one_iff_integrable.mp (B.memLp_of_bilin 1 (Lp.memLp h) (Lp.memLp h))
  change _=(NativeCompleteStressCarrier.readCLM k i j) (NativeWindowHistoryCovarianceRecovery.stress h)
  rw [NativeWindowHistoryCovarianceRecovery.stress_integral,← (NativeCompleteStressCarrier.readCLM k i j).integral_comp_comm paid]
  apply integral_congr_ae
  filter_upwards [NativeWindowTraceWholeHistory.finiteHistory_ae seed time M] with lag actual
  change h lag=_ at actual
  rw [actual]
  change _=NativeCompleteStressCarrier.read (NativeWindowHistoryCovarianceRecovery.fiber
    (projection M (NativeWindowTraceWholeHistory.original seed (time-lag)))
    (projection M (NativeWindowTraceWholeHistory.original seed (time-lag)))) k i j
  rw [projection_stress]

theorem stress_tendsto (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (k : IntegerWavevector) (i j : Coordinate) :
    Tendsto (fun M => stressCoefficient seed M time k i j) atTop
      (𝓝 (NativeCompleteStressCarrier.read (NativeForwardWindowSource.source seed time).snd k i j)) := by
  have complete:=NativeWindowHistoryCovarianceRecovery.stress_continuous.tendsto (history seed time) |>.comp
    (NativeWindowHistoryWholeRecovery.projected_tendsto (history seed time))
  have observed:=(NativeCompleteStressCarrier.readCLM k i j).continuous.tendsto _ |>.comp complete
  simpa only [coefficient_original,Function.comp_def,NativeCompleteStressCarrier.readCLM_apply,
    NativeWindowHistoryCovarianceRecovery.source_stress] using! observed

theorem velocity_tendsto (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (k : IntegerWavevector) (i : Coordinate) :
    Tendsto (fun M => complexSharpSupportProjection (modes M)
      (NativeEndpointVelocityCarrier.wholeVelocity (NativeForwardWindowSource.source seed time).fst) k i) atTop
      (𝓝 (NativeEndpointVelocityCarrier.wholeVelocity (NativeForwardWindowSource.source seed time).fst k i)) := by
  have full:=NativeWholeH1Mixed.restrict_tendsto
    (NativeWindowHistoryMeanProjection.mean (history seed time))
  have observed:=((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Coordinate => ℂ) i).continuous.tendsto _).comp
    (((lp.evalCLM ℝ (fun _ : IntegerWavevector => ComplexCoordinateVector) 2 k).continuous.tendsto _).comp full)
  change Tendsto (fun M => complexSharpSupportProjection (modes M)
    (NativeEndpointVelocityCarrier.wholeVelocity (NativeWindowHistoryMeanProjection.mean (history seed time)).1) k i)
    atTop (𝓝 (NativeEndpointVelocityCarrier.wholeVelocity
      (NativeWindowHistoryMeanProjection.mean (history seed time)).1 k i)) at observed
  simpa only [NativeWindowHistoryMeanProjection.source_mean] using! observed

theorem current_tendsto (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (direction : Fin 4) (k : IntegerWavevector) :
    Tendsto (fun M => UnitAddTorus.mFourierCoeff (current seed M time direction) k) atTop
      (𝓝 (NativePairedCurrentFourier.coefficient
        (NativeEndpointVelocityCarrier.wholeVelocity (NativeForwardWindowSource.source seed time).fst)
        (NativeCompleteStressCarrier.read (NativeForwardWindowSource.source seed time).snd) direction k)) := by
  simp only [current_fourier,NativePairedCurrentFourier.coefficient]
  refine Fin.cases ?_ (fun i => velocity_tendsto seed time k i) direction
  simp only [Fin.cases_zero,NativePairedCurrentFourier.trace]
  exact (tendsto_const_nhds).sub ((tendsto_finsetSum Finset.univ (fun i _ => stress_tendsto seed time k i i)).div_const 8)

theorem full_source_tendsto (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    Tendsto (fun M => NativeWindowHistoryCovarianceRecovery.read (finiteHistory seed time M)) atTop
      (𝓝 (NativeForwardWindowSource.source seed time)) := by
  have complete:=NativeWindowHistoryCovarianceRecovery.read_continuous.tendsto (history seed time) |>.comp
    (NativeWindowHistoryWholeRecovery.projected_tendsto (history seed time))
  simpa only [Function.comp_def,NativeWindowHistoryCovarianceRecovery.source_read] using! complete

theorem full_residual_tendsto (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    Tendsto (fun M => NativeWindowHistoryCovarianceRecovery.residual (finiteHistory seed time M)) atTop
      (𝓝 ((NativeForwardWindowSource.source seed time).snd-
        NativeStressTimeAlgebra.quadratic (NativeForwardWindowSource.source seed time).fst)) := by
  have complete:=NativeWindowHistoryCovarianceRecovery.residual_continuous.tendsto (history seed time) |>.comp
    (NativeWindowHistoryWholeRecovery.projected_tendsto (history seed time))
  simpa only [Function.comp_def,NativeWindowHistoryCovarianceRecovery.source_residual] using! complete

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem current_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0≤time)
    (direction : Fin 4) (x : NativePhysicalFourier.Torus) :
    current seed M (step.2.clockAdvance+time) direction x=current step.1 M time direction x := by
  rw [NativeWindowAbsoluteTimePhysicalCurrent.source_current,NativeWindowAbsoluteTimePhysicalCurrent.source_current,
    NativeForwardWindowSource.source_next seed step generated time nonnegative,
    NativeWindowFiniteGramFourier.stress_next seed step generated time nonnegative]

theorem full_read_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0≤time) :
    NativeWindowHistoryCovarianceRecovery.read (finiteHistory seed (step.2.clockAdvance+time) M)=
      NativeWindowHistoryCovarianceRecovery.read (finiteHistory step.1 time M) :=
  congrArg NativeWindowHistoryCovarianceRecovery.read
    (NativeWindowTraceWholeHistory.finiteHistory_next seed step generated time nonnegative M)

theorem full_residual_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0≤time) :
    NativeWindowHistoryCovarianceRecovery.residual (finiteHistory seed (step.2.clockAdvance+time) M)=
      NativeWindowHistoryCovarianceRecovery.residual (finiteHistory step.1 time M) :=
  congrArg NativeWindowHistoryCovarianceRecovery.residual
    (NativeWindowTraceWholeHistory.finiteHistory_next seed step generated time nonnegative M)

end
end SaturationMonoid.NavierStokes.NativeWindowAbsoluteTimePhysicalLimit
