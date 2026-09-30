import H0mework.Versions.X.NavierStokes.MacroAction.FiniteMacroMomentum
import H0mework.Versions.X.NavierStokes.MacroAction.FiniteMacroEvolution
import H0mework.Versions.X.NavierStokes.PhysicalReadout.Source

set_option autoImplicit false
open scoped Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeGlobalPhysicalCarrier

open Set Filter MeasureTheory
open SourceGeneratedNativeResponseDisposition SourceGeneratedNativeBoundedRun
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartBoundedPreAccumulationPhysicalTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientFinitePhysicalTrajectoryEndpointSplice
open NativeEndpointVelocityCarrier NativePhysicalFourier NativePhysicalSource NativeRecoveryPhysical
open NativeMacroMomentumIntegral NativeFiniteMacroPhysical NativeEventualTailControl

noncomputable section

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

variable {nu : Viscosity} {seed current next : GeneratedWholeRestartCurrent nu}

theorem receipt_velocity_reality {initial : ComplexVorticityHilbertState} {duration : ℝ}
    (receipt : WholeContinuousMildSerrinReceipt nu initial duration) (time : ℝ) :
    FiniteStateFourierReality (wholeVelocity (NativeOriginalMomentumIntegral.receiptVelocity receipt time)) := by
  rw [NativeOriginalMomentumIntegral.receiptVelocity, wholeVelocity_punctured]
  exact velocity_reality _ (receipt_reality receipt _)

theorem stage_reality (step : GeneratedWholeRestartEndpointMacroStep nu current next)
    (time : Icc (0 : ℝ) step.clockAdvance) :
    FiniteStateFourierReality (wholeVelocity (step.physicalStage time)) := by
  rw [← step.physicalStageTrajectory_eq_stage time, physicalStage_reads_earlyCurve step time time.2]
  by_cases before : time.1 < wholeRestartVelocityAccumulationTime current
  · let length := wholeRestartPreAccumulationCoverIndex current step.elapsedBounded ⟨time.1, time.2.1, before⟩
    have bound := (wholeRestartPreAccumulationCoverIndex_spec current step.elapsedBounded
      ⟨time.1, time.2.1, before⟩).le.trans ((elapsedTime_strictMono current).monotone (Nat.le_succ length))
    change FiniteStateFourierReality (wholeVelocity (NativeOriginalMomentumIntegral.velocity current step.elapsedBounded time.1))
    rw [NativeOriginalMomentumIntegral.velocity_eq_prefix current step.elapsedBounded length time.1 ⟨time.2.1, bound⟩]
    exact receipt_velocity_reality _ _
  · have localTime : time.1 - wholeRestartVelocityAccumulationTime current ∈ Icc (0 : ℝ) (recoveryTime step) := by
      have endBound := time.2.2.trans_eq (clock_split step)
      constructor <;> linarith
    have same := earlyCurve_after step _ localTime
    rw [add_sub_cancel] at same
    rw [same, recovery, recoveryCurve_full]
    exact wholeMild_reality _ _ _

theorem stageTrajectory_reality (step : GeneratedWholeRestartEndpointMacroStep nu current next) (time : ℝ) :
    FiniteStateFourierReality (wholeVelocity (step.physicalStageTrajectory time)) := stage_reality step _

theorem initial_reality (seed : GeneratedWholeRestartCurrent nu) :
    FiniteStateFourierReality (wholeVelocity (puncturedWholeVelocityEuclideanState seed.initialState)) := by
  rw [wholeVelocity_punctured, ← seed.receipt.wholePath_initial]
  exact velocity_reality _ (receipt_reality seed.receipt _)

theorem path_reality (arrival : NativeReachable seed generatedWholeRestartEndpointMacroRespond current) (time : ℝ) :
    FiniteStateFourierReality (wholeVelocity (path arrival time)) := by
  induction arrival with
  | initial => exact initial_reality seed
  | @step prior arrival response generated previous =>
      by_cases before : time ≤ clock arrival
      · rw [step_preserves arrival response generated time before]
        exact previous
      · rw [path, endpointSplice_of_lt _ _ _ _ (lt_of_not_ge before)]
        exact stageTrajectory_reality response.2 _

theorem tail_reality (run : GeneratedWholeRestartEndpointMacroTerminalRun seed) (time : ℝ) :
    FiniteStateFourierReality (wholeVelocity (NativeFiniteMacroGlobal.tail run time)) := by
  let horizon := max time 0 + 1
  have positive : 0 < horizon := by dsimp [horizon]; linarith [le_max_right time 0]
  let receipt := (WholeGlobalReceipt.ofTrajectory run.globalPhysicalTrajectory).receiptAt horizon positive
  have member : max time 0 ∈ Icc (0 : ℝ) horizon := ⟨le_max_right _ _, by dsimp [horizon]; linarith⟩
  rw [NativeFiniteMacroGlobal.tail, wholeVelocity_punctured,
    ← WholeGlobalReceipt.ofTrajectory_path run.globalPhysicalTrajectory horizon positive ⟨max time 0, member⟩]
  exact velocity_reality _ (receipt_reality receipt _)

theorem source_reality (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    FiniteStateFourierReality (wholeVelocity (NativeAbsoluteEventualControl.velocity seed time)) := by
  by_cases before : time ≤ clock (terminal seed).arrival
  · rw [NativeAbsoluteEventualControl.velocity, NativeFiniteMacroGlobal.prefix_preserved _ time before]
    exact path_reality _ time
  · rw [NativeAbsoluteEventualControl.velocity, NativeFiniteMacroGlobal.globalPath,
      endpointSplice_of_lt _ _ _ _ (lt_of_not_ge before)]
    exact tail_reality _ _

def field (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) : Lp PhysicalSpace 2 (volume : Measure Torus) :=
  physicalCLM (NativeAbsoluteEventualControl.velocity seed time)

theorem source_fourier (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (coordinate : Coordinate) (wave : IntegerWavevector) :
    UnitAddTorus.mFourierCoeff (fun point => (field seed time point coordinate : ℂ)) wave =
      wholeVelocity (NativeAbsoluteEventualControl.velocity seed time) wave coordinate :=
  realField_fourier _ (source_reality seed time) coordinate wave

theorem source_norm (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    ‖field seed time‖ = ‖NativeAbsoluteEventualControl.velocity seed time‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  exact (realField_norm_sq _ (source_reality seed time)).trans (wholeVelocity_mass _)

theorem source_norm_le (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    ‖field seed time‖ ≤ ‖puncturedWholeVelocityEuclideanState seed.initialState‖ :=
  (source_norm seed time).le.trans (NativeAbsoluteEventualControl.velocity_norm_le seed time)

theorem source_full_flux (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (output input : Coordinate) (wave : IntegerWavevector) :
    UnitAddTorus.mFourierCoeff (fun point =>
      ((-(field seed time point input * field seed time point output) : ℝ) : ℂ)) wave =
      NativeStressSource.quadraticFlux (wholeVelocity (NativeAbsoluteEventualControl.velocity seed time)) wave output input :=
  real_flux_fourier _ (source_reality seed time) output input wave

theorem source_next_field (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response)
    (time : ℝ) (nonnegative : 0 ≤ time) :
    field seed (response.2.clockAdvance + time) = field response.1 time := by
  rw [field, field, NativeFiniteMacroEvolution.source_generated_next_evolution response generated time nonnegative]

end
end SaturationMonoid.NavierStokes.NativeGlobalPhysicalCarrier
