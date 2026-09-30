import H0mework.Versions.X.NavierStokes.WindowHistoryCreation.Geometry
import H0mework.Versions.X.NavierStokes.WindowSchurMean.Action

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryCreationCovariance
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientPuncturedCanonicalGalerkinTarget
open NativeFiniteActionResolvent NativePhysicalFourier
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativeWindowStressOseenTest (evaluate evaluate_apply)
open NativeWindowHistoryCreationGeometry (square)
open NativeWindowHistoryMeanAction (meanValue)
open NativeWindowTraceAdjoint (value)
open NativeForwardWindowPairingReadout (averageMeasure)
noncomputable section
local instance physicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance physicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
variable {nu : Viscosity}

theorem square_continuous (M : Finset IntegerWavevector) : Continuous (square M) := by
  apply continuous_finsetSum
  intro i _
  exact ((LinearMap.toContinuousLinearMap (evaluate M M i)).continuous).mul
    (LinearMap.toContinuousLinearMap (evaluate M M i)).continuous

def centered (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time sample : ℝ) : physicalSpace (modes M) :=
  value seed M sample-meanValue seed M time

theorem centered_continuous (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    Continuous (centered seed M time) := (NativeWindowTraceAdjoint.value_continuous seed M).sub continuous_const

def covariance (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (output input : Coordinate) : C(Torus,ℝ) :=
  ∫lag,evaluate (modes M) (modes M) output (centered seed M time (time-lag))*
    evaluate (modes M) (modes M) input (centered seed M time (time-lag)) ∂averageMeasure

def trace (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : C(Torus,ℝ) :=
  ∫lag,square (modes M) (centered seed M time (time-lag)) ∂averageMeasure

theorem covariance_integrable (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (output input : Coordinate) :
    Integrable (fun lag => evaluate (modes M) (modes M) output (centered seed M time (time-lag))*
      evaluate (modes M) (modes M) input (centered seed M time (time-lag))) averageMeasure :=
  (NativeWindowTraceTerminalGraph.continuous_memLp time _
    (((LinearMap.toContinuousLinearMap (evaluate (modes M) (modes M) output)).continuous.comp (centered_continuous seed M time)).mul
      ((LinearMap.toContinuousLinearMap (evaluate (modes M) (modes M) input)).continuous.comp (centered_continuous seed M time))) 1).integrable le_rfl

theorem trace_integrable (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    Integrable (fun lag => square (modes M) (centered seed M time (time-lag))) averageMeasure :=
  (NativeWindowTraceTerminalGraph.continuous_memLp time _ ((square_continuous (modes M)).comp (centered_continuous seed M time)) 1).integrable le_rfl

theorem trace_matrix (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    trace seed M time=∑ i : Coordinate,covariance seed M time i i := by
  unfold trace square covariance
  exact integral_finsetSum Finset.univ (fun i _ => covariance_integrable seed M time i i)

theorem covariance_point (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ)
    (output input : Coordinate) (point : Torus) : covariance seed M time output input point=∫lag,
      evaluate (modes M) (modes M) output (centered seed M time (time-lag)) point*
        evaluate (modes M) (modes M) input (centered seed M time (time-lag)) point ∂averageMeasure := by
  change (ContinuousMap.evalCLM ℝ point) (∫lag,evaluate (modes M) (modes M) output (centered seed M time (time-lag))*
    evaluate (modes M) (modes M) input (centered seed M time (time-lag)) ∂averageMeasure)=_
  exact ((ContinuousMap.evalCLM ℝ point).integral_comp_comm (covariance_integrable seed M time output input)).symm

theorem trace_nonnegative (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (point : Torus) :
    0≤trace seed M time point := by
  rw [trace_matrix]
  simp only [ContinuousMap.sum_apply]
  apply Finset.sum_nonneg
  intro i _
  rw [covariance_point]
  exact integral_nonneg fun _ => mul_self_nonneg _

theorem evaluate_cube (M : ℕ) (v : physicalSpace (modes M)) (i : Coordinate) :
    evaluate (modes M) (modes M) i v=evaluate (modes M) (integerWaveFrequencyCube M) i v := by
  rw [evaluate_apply,evaluate_apply]
  apply Finset.sum_subset (Finset.erase_subset 0 (integerWaveFrequencyCube M))
  intro k _ outside
  rw [physical_supported v k outside,Pi.zero_apply,map_zero]

theorem value_field (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (sample : ℝ) (nonnegative : 0 ≤ sample) (i : Coordinate) :
    evaluate (modes M) (modes M) i (value seed M sample)=NativeWindowFiniteGramFourier.read (integerWaveFrequencyCube M) i
      (NativeUnifiedCompleteSource.source seed sample) := by
  rw [evaluate_cube]
  have cover:∀k∈integerWaveFrequencyCube M,k≠0 →k∈modes M := fun _ inside nonzero => Finset.mem_erase.mpr ⟨nonzero,inside⟩
  exact (NativeWindowTraceDualWindow.value_read seed M sample nonnegative _ cover i).trans
    (NativeWindowStressHeatTime.field_original seed _ i sample)

private theorem variance {f : ℝ → ℝ} (paid : MemLp f 2 averageMeasure) (m : ℝ) (mean : ∫lag,f lag ∂averageMeasure=m) :
    (∫lag,(f lag-m)^2 ∂averageMeasure)=(∫lag,(f lag)^2 ∂averageMeasure)-m^2 := by
  have first:=paid.integrable (by norm_num : (1:ℝ≥0∞)≤2)
  have split:(fun lag => (f lag-m)^2)=fun lag => (f lag)^2-2*m*f lag+m^2 := by funext lag; ring
  have squarePaid:Integrable (fun lag => (f lag)^2-2*m*f lag) averageMeasure := paid.integrable_sq.sub (first.const_mul (2*m))
  rw [split,integral_add squarePaid (integrable_const _),
    integral_sub paid.integrable_sq (first.const_mul (2*m)),integral_const_mul,mean]
  simp only [integral_const,Measure.real,measure_univ,ENNReal.toReal_one,one_smul]
  ring

theorem covariance_diagonal (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (nonnegative : 0≤time)
    (i : Coordinate) (point : Torus) : covariance seed M time i i point=
      NativeWindowFiniteGramFourier.stress seed time (integerWaveFrequencyCube M) i i point-
        (evaluate (modes M) (modes M) i (meanValue seed M time) point)^2 := by
  let read:=(ContinuousMap.evalCLM ℝ point).comp (LinearMap.toContinuousLinearMap (evaluate (modes M) (modes M) i))
  have paid:=NativeWindowTraceTerminalGraph.continuous_memLp time (fun sample => read (value seed M sample))
    (read.continuous.comp (NativeWindowTraceAdjoint.value_continuous seed M)) 2
  have mean:(∫lag,read (value seed M (time-lag)) ∂averageMeasure)=read (meanValue seed M time) := by
    rw [read.integral_comp_comm ((NativeWindowTraceTerminalGraph.continuous_memLp time (value seed M)
      (NativeWindowTraceAdjoint.value_continuous seed M) 1).integrable le_rfl),NativeWindowHistoryMeanAction.value_average]
  have same:=variance paid _ mean
  rw [covariance_point]
  have expanded:(fun lag => evaluate (modes M) (modes M) i (centered seed M time (time-lag)) point*
      evaluate (modes M) (modes M) i (centered seed M time (time-lag)) point)=
      fun lag => (read (value seed M (time-lag))-read (meanValue seed M time))^2 := by
    funext lag
    simp only [centered,map_sub,ContinuousMap.sub_apply,read,ContinuousLinearMap.comp_apply,ContinuousMap.evalCLM_apply]
    change (_-_)*(_-_)=(evaluate (modes M) (modes M) i (value seed M (time-lag)) point-
      evaluate (modes M) (modes M) i (meanValue seed M time) point)^2
    ring
  rw [expanded,same,NativeWindowFiniteGramFourier.stress_apply]
  congr 1
  apply integral_congr_ae
  filter_upwards [NativeWindowTraceEndpointWindow.average_interval] with lag support
  change (evaluate (modes M) (modes M) i (value seed M (time-lag)) point)^2=_
  rw [value_field seed M (time-lag) (by linarith [support.2]) i]
  ring

theorem trace_le_stress (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (nonnegative : 0≤time) (point : Torus) :
    trace seed M time point≤NativeWindowTraceGradient.traceStress seed time (integerWaveFrequencyCube M) point := by
  rw [trace_matrix,NativeWindowTraceGradient.traceStress]
  simp only [ContinuousMap.sum_apply]
  exact Finset.sum_le_sum fun i _ => (covariance_diagonal seed M time nonnegative i point).trans_le (sub_le_self _ (sq_nonneg _))

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryCreationCovariance
