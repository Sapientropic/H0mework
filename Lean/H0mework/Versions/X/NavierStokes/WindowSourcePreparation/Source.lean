import H0mework.Versions.X.NavierStokes.PhysicalView.RootPreparation
import H0mework.Versions.X.NavierStokes.SourceWindow.Pairing

set_option autoImplicit false
open scoped Topology ENNReal BigOperators
namespace SaturationMonoid.NavierStokes.NativeWindowPreparationSource
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open ThreeDimensionalVorticityCoefficientFinitePhysicalTrajectoryEndpointSplice
open SourceGeneratedNativeResponseDisposition NativeCompleteStressAction NativeEndpointVelocityCarrier
open NativeForwardWindowSource NativeFiniteMacroPhysical
noncomputable section
variable {nu : Viscosity} {seed current : GeneratedWholeRestartCurrent nu}

theorem history_nonpositive (arrival : NativeReachable seed generatedWholeRestartEndpointMacroRespond current)
    (time : ℝ) (nonpositive : time ≤ 0) :
    NativeUnifiedGlobalStressSource.history arrival time = NativeUnifiedGlobalStressSource.initial seed := by
  induction arrival with
  | initial => rfl
  | step arrival generated previous =>
    simpa only [NativeUnifiedGlobalStressSource.history,
      endpointSplice_of_le _ _ _ _ (nonpositive.trans (clock_nonnegative arrival))] using previous

theorem raw_nonpositive (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (nonpositive : time ≤ 0) :
    NativeUnifiedGlobalStressSource.source seed time = NativeUnifiedGlobalStressSource.source seed 0 := by
  rw [NativeUnifiedGlobalStressSource.source_zero, NativeUnifiedGlobalStressSource.source,
    NativeUnifiedGlobalStressSource.global,
    endpointSplice_of_le _ _ _ _ (nonpositive.trans (clock_nonnegative _))]
  exact history_nonpositive _ time nonpositive

theorem complete_nonpositive (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (nonpositive : time ≤ 0) :
    NativeUnifiedCompleteSource.source seed time = NativeUnifiedCompleteSource.source seed 0 := by
  apply congrArg (WithLp.toLp 2)
  apply Prod.ext
  · change (NativeUnifiedGlobalStressSource.source seed time).1 = (NativeUnifiedGlobalStressSource.source seed 0).1
    exact congrArg (fun value : NativeUnifiedGlobalStressSource.State => value.1) (raw_nonpositive seed time nonpositive)
  · apply NativeCompleteStressCarrier.read_injective
    simp only [NativeUnifiedCompleteSource.stress, NativeCompleteStressCarrier.read_ofBound]
    exact congrArg Prod.snd (raw_nonpositive seed time nonpositive)

theorem window_initial (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (before : time ≤ -2) :
    NativeForwardWindowSource.source seed time = NativeUnifiedCompleteSource.source seed 0 := by
  rw [source_integrand]
  calc
    _ = ∫ shift : ℝ, kernel shift • NativeUnifiedCompleteSource.source seed 0 := by
      apply integral_congr_ae
      filter_upwards with shift
      by_cases zero : kernel shift = 0
      · simp only [zero, zero_smul]
      · rw [complete_nonpositive seed (time-shift) (by linarith [(NativeViewPreparation.kernel_window shift zero).1])]
    _ = _ := by rw [integral_smul_const, kernel_mass, one_smul]

theorem initial_velocity (seed : GeneratedWholeRestartCurrent nu) :
    (NativeForwardWindowSource.source seed (-2)).fst =
      puncturedWholeVelocityEuclideanState seed.initialState := by
  rw [window_initial seed (-2) le_rfl]
  change (NativeUnifiedGlobalStressSource.source seed 0).1 = _
  rw [NativeUnifiedGlobalStressSource.source_zero]
  rfl

theorem initial_stress (seed : GeneratedWholeRestartCurrent nu) :
    NativeCompleteStressCarrier.read (NativeForwardWindowSource.source seed (-2)).snd =
      NativeStressSource.quadraticFlux (wholeVelocity (NativeForwardWindowSource.source seed (-2)).fst) := by
  rw [window_initial seed (-2) le_rfl, NativeUnifiedCompleteSource.stress_read]
  change (NativeUnifiedGlobalStressSource.source seed 0).2 =
    NativeStressSource.quadraticFlux (wholeVelocity (NativeUnifiedGlobalStressSource.source seed 0).1)
  rw [NativeUnifiedGlobalStressSource.source_zero]
  rfl

theorem initial_residual (seed : GeneratedWholeRestartCurrent nu) :
    NativeCompleteCorrectionRead.residual (NativeForwardWindowSource.source seed (-2)) = 0 := by
  change NativeCompleteStressCarrier.read (NativeForwardWindowSource.source seed (-2)).snd-
    NativeStressSource.quadraticFlux (wholeVelocity (NativeForwardWindowSource.source seed (-2)).fst) = 0
  rw [initial_stress, sub_self]

end
end SaturationMonoid.NavierStokes.NativeWindowPreparationSource
