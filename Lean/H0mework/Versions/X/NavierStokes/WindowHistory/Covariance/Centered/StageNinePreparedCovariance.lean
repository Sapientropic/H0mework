import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.StageNinePreparedSourceIdentity

set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeStageNinePreparedCovariance
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientPuncturedCanonicalGalerkinTarget
open NativeFiniteActionResolvent NativePhysicalFourier
open NativeWholeH1Mixed (modes)
open NativeWindowHistoryCreationCovariance (centered covariance trace)
open NativeWindowHistoryMeanAction (meanValue)
open NativeWindowTraceAdjoint (value)
open NativeForwardWindowPairingReadout (averageMeasure)
noncomputable section
variable {nu : Viscosity}

private theorem variance {f : ℝ → ℝ} (paid : MemLp f 2 averageMeasure) (m : ℝ)
    (mean : ∫lag,f lag ∂averageMeasure=m) :
    (∫lag,(f lag-m)^2 ∂averageMeasure)=
      (∫lag,(f lag)^2 ∂averageMeasure)-m^2 := by
  have first:=paid.integrable (by norm_num : (1:ℝ≥0∞)≤2)
  have split:(fun lag => (f lag-m)^2)=fun lag => (f lag)^2-2*m*f lag+m^2 := by funext lag; ring
  have squarePaid:Integrable (fun lag => (f lag)^2-2*m*f lag) averageMeasure :=
    paid.integrable_sq.sub (first.const_mul (2*m))
  rw [split,integral_add squarePaid (integrable_const _),
    integral_sub paid.integrable_sq (first.const_mul (2*m)),integral_const_mul,mean]
  simp only [integral_const,Measure.real,measure_univ,ENNReal.toReal_one,one_smul]
  ring

theorem covariance_diagonal_total (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (time : ℝ) (i : Coordinate) (point : Torus) :
    covariance seed M time i i point=
      NativeWindowFiniteGramFourier.stress seed time (integerWaveFrequencyCube M) i i point-
        (NativeWindowStressOseenTest.evaluate (modes M) (modes M) i
          (meanValue seed M time) point)^2 := by
  let read:=(ContinuousMap.evalCLM ℝ point).comp
    (LinearMap.toContinuousLinearMap (NativeWindowStressOseenTest.evaluate (modes M) (modes M) i))
  have paid:=NativeWindowTraceTerminalGraph.continuous_memLp time
    (fun sample => read (value seed M sample))
    (read.continuous.comp (NativeWindowTraceAdjoint.value_continuous seed M)) 2
  have mean:(∫lag,read (value seed M (time-lag)) ∂averageMeasure)=
      read (meanValue seed M time) := by
    rw [read.integral_comp_comm ((NativeWindowTraceTerminalGraph.continuous_memLp time
      (value seed M) (NativeWindowTraceAdjoint.value_continuous seed M) 1).integrable le_rfl),
      NativeWindowHistoryMeanAction.value_average]
  have same:=variance paid _ mean
  rw [NativeWindowHistoryCreationCovariance.covariance_point]
  have expanded:(fun lag => NativeWindowStressOseenTest.evaluate (modes M) (modes M) i
      (centered seed M time (time-lag)) point*
      NativeWindowStressOseenTest.evaluate (modes M) (modes M) i
        (centered seed M time (time-lag)) point)=
      fun lag => (read (value seed M (time-lag))-read (meanValue seed M time))^2 := by
    funext lag
    simp only [NativeWindowHistoryCreationCovariance.centered,map_sub,
      ContinuousMap.sub_apply,read,ContinuousLinearMap.comp_apply,ContinuousMap.evalCLM_apply]
    change (_-_)*(_-_)=(NativeWindowStressOseenTest.evaluate (modes M) (modes M) i
      (value seed M (time-lag)) point-
      NativeWindowStressOseenTest.evaluate (modes M) (modes M) i
        (meanValue seed M time) point)^2
    ring
  rw [expanded,same,NativeWindowFiniteGramFourier.stress_apply]
  congr 1
  apply integral_congr_ae
  filter_upwards [NativeWindowTraceEndpointWindow.average_interval] with lag support
  change (NativeWindowStressOseenTest.evaluate (modes M) (modes M) i
    (value seed M (time-lag)) point)^2=_
  rw [NativeWindowHistoryCreationCovariance.prepared_value_field seed M (time-lag) i]
  ring

theorem trace_le_stress_total (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (time : ℝ) (point : Torus) :
    trace seed M time point≤NativeWindowTraceGradient.traceStress seed time
      (integerWaveFrequencyCube M) point := by
  rw [NativeWindowHistoryCreationCovariance.trace_matrix,NativeWindowTraceGradient.traceStress]
  simp only [ContinuousMap.sum_apply]
  exact Finset.sum_le_sum fun i _ =>
    (covariance_diagonal_total seed M time i point).trans_le
      (sub_le_self _ (sq_nonneg _))

theorem mean_square_le_stress_total (seed : GeneratedWholeRestartCurrent nu)
    (M : ℕ) (time : ℝ) (point : Torus) :
    NativeWindowHistoryCreationGeometry.square (modes M) (meanValue seed M time) point≤
      NativeWindowTraceGradient.traceStress seed time (integerWaveFrequencyCube M) point := by
  have same : trace seed M time point=
      NativeWindowTraceGradient.traceStress seed time (integerWaveFrequencyCube M) point-
        NativeWindowHistoryCreationGeometry.square (modes M) (meanValue seed M time) point := by
    rw [NativeWindowHistoryCreationCovariance.trace_matrix,
      NativeWindowTraceGradient.traceStress,NativeWindowHistoryCreationGeometry.square]
    simp only [ContinuousMap.sum_apply,ContinuousMap.mul_apply]
    simp_rw [covariance_diagonal_total seed M time,Finset.sum_sub_distrib,pow_two]
  linarith only [same,NativeWindowHistoryCreationCovariance.trace_nonnegative seed M time point]
end
end SaturationMonoid.NavierStokes.NativeStageNinePreparedCovariance
