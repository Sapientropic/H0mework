import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.StageNinePreparedCovariance
import H0mework.Versions.X.NavierStokes.WindowEnergyAugmented.PreparationControl

set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeStageNinePreparedCovariance
open Set
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open RationalVorticityEvaluator.ButterflyStackedSourceCurrent (stackedShortCurrent)
open NativeWindowStressHeatSource (physical)
noncomputable section

def preparedTraceBudget (horizon : ℝ) : ℝ :=
  3*NativeWindowPreparedSobolevWindow.budget 0 horizon

theorem preparedTraceBudget_nonnegative (horizon : ℝ) (nonnegative : 0≤horizon) :
    0≤preparedTraceBudget horizon := by
  have inside : (0 : ℝ)∈Icc (-2 : ℝ) horizon:=⟨by norm_num,nonnegative⟩
  have source:=NativeWindowPreparedAugmentedControl.stressJet_bound
    0 0 0 horizon nonnegative inside 0 0
  have B0 : 0≤NativeWindowPreparedSobolevWindow.budget 0 horizon :=
    (norm_nonneg _).trans source
  dsimp only [preparedTraceBudget]
  positivity

theorem prepared_trace_bound (horizon : ℝ) (nonnegative : 0≤horizon)
    (M : ℕ) (time : ℝ) (inside : time∈Icc (-2 : ℝ) horizon) :
    ‖physical (NativeWindowTraceGradient.traceStress stackedShortCurrent time
      (integerWaveFrequencyCube M))‖≤preparedTraceBudget horizon := by
  rw [NativeWindowTraceGradient.traceStress,map_sum]
  apply (norm_sum_le _ _).trans
  have row (i : Coordinate) :
      ‖physical (NativeWindowFiniteGramFourier.stress stackedShortCurrent time
        (integerWaveFrequencyCube M) i i)‖≤
        NativeWindowPreparedSobolevWindow.budget 0 horizon := by
    have paid:=NativeWindowPreparedAugmentedControl.stressJet_bound
      M 0 time horizon nonnegative inside i i
    rw [NativeWindowPreparedAugmentedControl.stressJet_zero M time inside.1 i i] at paid
    exact paid
  exact (Finset.sum_le_sum fun i _ => row i).trans_eq (by
    simp only [Fin.sum_univ_three]
    unfold preparedTraceBudget
    ring)
end
end SaturationMonoid.NavierStokes.NativeStageNinePreparedCovariance
