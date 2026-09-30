import H0mework.NavierStokes.MacroAction.FiniteMacroPhysical
import H0mework.NavierStokes.NormControl.Native

set_option autoImplicit false
open scoped Topology

namespace SaturationMonoid.NavierStokes.NativeFiniteMacroGlobal

open Set Filter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartBoundedPreAccumulationPhysicalTrajectory
open ThreeDimensionalVorticityCoefficientFinitePhysicalTrajectoryEndpointSplice
open NativeFiniteMacroPhysical NativeNormControl

noncomputable section

variable {nu : Viscosity} {seed : GeneratedWholeRestartCurrent nu}

def tail (run : GeneratedWholeRestartEndpointMacroTerminalRun seed) (time : ℝ) : WholeRestartVelocityEndpointState :=
  puncturedWholeVelocityEuclideanState (run.globalPhysicalTrajectory.physicalPath (max time 0))

theorem tail_zero (run : GeneratedWholeRestartEndpointMacroTerminalRun seed) :
    tail run 0 = puncturedWholeVelocityEuclideanState run.terminal.initialState := by
  simp only [tail, max_self, run.globalPhysicalTrajectory.initial_eq]

theorem tail_continuous (run : GeneratedWholeRestartEndpointMacroTerminalRun seed) : Continuous (tail run) := by
  apply continuous_iff_continuousAt.mpr
  intro time
  let horizon := max time 0 + 1
  have positive : 0 < horizon := by dsimp [horizon]; linarith [le_max_right time 0]
  let receipt := (WholeGlobalReceipt.ofTrajectory run.globalPhysicalTrajectory).receiptAt horizon positive
  have clipped : Continuous fun sample : ℝ => max sample 0 := continuous_id.max continuous_const
  have localContinuous := continuous_puncturedWholeVelocityEuclideanState.comp
    (receipt.wholePath.continuous.comp ((continuous_projIcc (a := 0) (b := horizon) (h := positive.le)).comp clipped))
  apply localContinuous.continuousAt.congr_of_eventuallyEq
  have nearby : ∀ᶠ sample : ℝ in 𝓝 time, max sample 0 < horizon :=
    (clipped.tendsto time) (Iio_mem_nhds (by dsimp [horizon]; linarith))
  filter_upwards [nearby] with sample below
  have inside : max sample 0 ∈ Icc (0 : ℝ) horizon := ⟨le_max_right _ _, below.le⟩
  simp only [Function.comp_def, projIcc_of_mem positive.le inside]
  rw [WholeGlobalReceipt.ofTrajectory_path]
  rfl

def globalPath (run : GeneratedWholeRestartEndpointMacroTerminalRun seed) : ℝ → WholeRestartVelocityEndpointState :=
  endpointSplice (clock run.arrival) (path run.arrival) (tail run)

theorem prefix_preserved (run : GeneratedWholeRestartEndpointMacroTerminalRun seed)
    (time : ℝ) (before : time ≤ clock run.arrival) : globalPath run time = path run.arrival time :=
  endpointSplice_of_le _ _ _ _ before

theorem initial (run : GeneratedWholeRestartEndpointMacroTerminalRun seed) :
    globalPath run 0 = puncturedWholeVelocityEuclideanState seed.initialState := by
  rw [prefix_preserved run 0 (clock_nonnegative run.arrival), NativeFiniteMacroPhysical.initial]

theorem tail_chart (run : GeneratedWholeRestartEndpointMacroTerminalRun seed) (time : ℝ) (nonnegative : 0 ≤ time) :
    globalPath run (clock run.arrival + time) = puncturedWholeVelocityEuclideanState
      (run.globalPhysicalTrajectory.physicalPath time) := by
  by_cases atZero : time = 0
  · subst time
    rw [add_zero, prefix_preserved run _ le_rfl, endpoint, run.globalPhysicalTrajectory.initial_eq]
  · have later : clock run.arrival < clock run.arrival + time := by
      have positive : 0 < time := lt_of_le_of_ne nonnegative (Ne.symm atZero)
      linarith
    rw [globalPath, endpointSplice_of_lt _ _ _ _ later, add_sub_cancel_left, tail, max_eq_left nonnegative]

theorem norm_le (run : GeneratedWholeRestartEndpointMacroTerminalRun seed) (time : ℝ) :
    ‖globalPath run time‖ ≤ ‖puncturedWholeVelocityEuclideanState seed.initialState‖ := by
  by_cases before : time ≤ clock run.arrival
  · rw [prefix_preserved run time before]
    exact NativeFiniteMacroPhysical.norm_le run.arrival time
  · rw [globalPath, endpointSplice_of_lt _ _ _ _ (lt_of_not_ge before)]
    have source := old_trajectory_velocity_norm_le run.globalPhysicalTrajectory
      (max (time - clock run.arrival) 0) (le_max_right _ _)
    exact source.trans (by simpa only [endpoint] using NativeFiniteMacroPhysical.norm_le run.arrival (clock run.arrival))

theorem coordinate_continuous (run : GeneratedWholeRestartEndpointMacroTerminalRun seed) (wave : NonzeroIntegerWavevector) :
    Continuous fun time => globalPath run time wave := by
  have tailContinuous : Continuous fun time => tail run time wave :=
    (lp.evalCLM ℂ (fun _ : NonzeroIntegerWavevector => ComplexCoordinateEuclidean) 2 wave).continuous.comp (tail_continuous run)
  have same : tail run 0 wave = path run.arrival (clock run.arrival) wave := by rw [tail_zero, endpoint]
  have joined := splice_continuous (clock run.arrival) (fun time => path run.arrival time wave)
    (fun time => tail run time wave) (NativeFiniteMacroPhysical.coordinate_continuous run.arrival wave) tailContinuous same
  convert joined using 1
  funext time
  by_cases before : time ≤ clock run.arrival <;> simp [globalPath, endpointSplice, before]

end
end SaturationMonoid.NavierStokes.NativeFiniteMacroGlobal
