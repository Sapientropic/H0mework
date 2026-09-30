import H0mework.Versions.X.NavierStokes.WindowHistoryCreation.Covariance

set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryCreationCovariance
open Set
open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open ThreeDimensionalVorticityCoefficientFinitePhysicalTrajectoryEndpointSplice
open NativeFiniteMacroPhysical
open NativeEventualTailControl
open NativeUnifiedGlobalStressSource
noncomputable section
variable {nu : Viscosity}

private theorem source_history_before {seed current : GeneratedWholeRestartCurrent nu}
    (arrival : NativeReachable seed generatedWholeRestartEndpointMacroRespond current)
    (time : ℝ) (before : time≤0) :
    history arrival time=initial seed := by
  induction arrival with
  | initial => rfl
  | @step previous arrival response generated ih =>
    rw [history,endpointSplice_of_le _ _ _ _
      (before.trans (clock_nonnegative arrival))]
    exact ih

theorem complete_source_before (seed : GeneratedWholeRestartCurrent nu)
    (time : ℝ) (before : time≤0) :
    NativeUnifiedCompleteSource.source seed time=
      NativeUnifiedCompleteSource.source seed 0 := by
  have source : NativeUnifiedGlobalStressSource.source seed time=
      NativeUnifiedGlobalStressSource.source seed 0 := by
    unfold NativeUnifiedGlobalStressSource.source NativeUnifiedGlobalStressSource.global
    rw [endpointSplice_of_le _ _ _ _
      (before.trans (clock_nonnegative (terminal seed).arrival)),
      endpointSplice_of_le _ _ _ _ (clock_nonnegative (terminal seed).arrival)]
    exact (source_history_before (terminal seed).arrival time before).trans
      (history_zero (terminal seed).arrival).symm
  unfold NativeUnifiedCompleteSource.source NativeUnifiedCompleteSource.stress
  simp only [NativeUnifiedGlobalStressSource.stress,source]

theorem prepared_value_field (seed : GeneratedWholeRestartCurrent nu)
    (M : ℕ) (sample : ℝ) (i : ThreeDimensionalPeriodicCoarseFilterCore.Coordinate) :
    NativeWindowStressOseenTest.evaluate (NativeWholeH1Mixed.modes M)
      (NativeWholeH1Mixed.modes M) i (NativeWindowTraceAdjoint.value seed M sample)=
      NativeWindowFiniteGramFourier.read
        (ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.integerWaveFrequencyCube M)
        i (NativeUnifiedCompleteSource.source seed sample) := by
  by_cases nonnegative : 0 ≤ sample
  · exact value_field seed M sample nonnegative i
  · have before : sample≤0 := le_of_not_ge nonnegative
    have finite : NativeWindowTraceAdjoint.value seed M sample=
        NativeWindowTraceAdjoint.value seed M 0 := by
      simp only [NativeWindowTraceAdjoint.value,
        NativeWindowHierarchyPairWindow.state_before seed sample before]
    rw [finite,complete_source_before seed sample before]
    exact value_field seed M 0 le_rfl i
end
end SaturationMonoid.NavierStokes.NativeWindowHistoryCreationCovariance
