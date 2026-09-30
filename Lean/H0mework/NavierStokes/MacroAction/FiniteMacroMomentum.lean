import H0mework.NavierStokes.MomentumAction.MomentumIntegralSplice
import H0mework.NavierStokes.MomentumAction.ReceiptMomentumIntegral
import H0mework.NavierStokes.MacroAction.MacroMomentumIntegral
import H0mework.NavierStokes.SourceAction.AbsoluteEventual

set_option autoImplicit false
open scoped Topology

namespace SaturationMonoid.NavierStokes.NativeFiniteMacroMomentum

open Set Filter MeasureTheory
open SourceGeneratedNativeResponseDisposition SourceGeneratedNativeBoundedRun
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartFinitePrefixDualSquareLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open ThreeDimensionalVorticityCoefficientFinitePhysicalTrajectoryEndpointSplice
open NativeFiniteMacroPhysical NativeMomentumIntegral NativeOriginalMomentumIntegral
open NativeEventualTailControl NativeAbsoluteEventualControl NativeEndpointVelocityCarrier
open NativeTimeJetCarrier

noncomputable section

variable {nu : Viscosity} {seed current : GeneratedWholeRestartCurrent nu}

theorem receipt_writes {initial : ComplexVorticityHilbertState} {duration : ℝ}
    (receipt : WholeContinuousMildSerrinReceipt nu initial duration) :
    WritesOn nu (receiptVelocity receipt) duration := by
  intro wave
  exact ⟨receipt_integrable receipt wave, fun time inside => receipt_primitive receipt wave ⟨time, inside⟩⟩

theorem tail_writes (run : GeneratedWholeRestartEndpointMacroTerminalRun seed)
    (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    WritesOn nu (NativeFiniteMacroGlobal.tail run) horizon := by
  by_cases zero : horizon = 0
  · subst horizon
    exact writes_zero
  · have positive : 0 < horizon := lt_of_le_of_ne nonnegative (Ne.symm zero)
    let receipt := (WholeGlobalReceipt.ofTrajectory run.globalPhysicalTrajectory).receiptAt horizon positive
    apply (receipt_writes receipt).congr nonnegative
    intro time inside
    simp only [NativeFiniteMacroGlobal.tail, max_eq_left inside.1, receiptVelocity,
      projIcc_of_mem receipt.requestedTimePos.le inside]
    rw [WholeGlobalReceipt.ofTrajectory_path]

theorem arrival_writes
    (arrival : NativeReachable seed generatedWholeRestartEndpointMacroRespond current) :
    WritesOn nu (path arrival) (clock arrival) := by
  induction arrival with
  | initial => exact writes_zero
  | @step prior arrival response generated previous =>
      apply previous.splice (NativeMacroMomentumIntegral.stage_writes response.2)
        (clock_nonnegative arrival) response.2.clockAdvance_pos.le
      exact ((response.2.physicalStageTrajectory_eq_stage response.2.physicalStageZero).trans
        response.2.physicalStage_zero).trans (endpoint arrival).symm

theorem global_writes
    (run : GeneratedWholeRestartEndpointMacroTerminalRun seed)
    (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    WritesOn nu (NativeFiniteMacroGlobal.globalPath run) horizon := by
  have joined := (arrival_writes run.arrival).splice (tail_writes run horizon nonnegative)
    (clock_nonnegative run.arrival) nonnegative
    ((NativeFiniteMacroGlobal.tail_zero run).trans (endpoint run.arrival).symm)
  exact joined.mono nonnegative (by linarith [clock_nonnegative run.arrival])

theorem source_absolute_writes (seed : GeneratedWholeRestartCurrent nu)
    (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    WritesOn nu (NativeAbsoluteEventualControl.velocity seed) horizon :=
  global_writes (terminal seed) horizon nonnegative

theorem source_momentum_write (seed : GeneratedWholeRestartCurrent nu) (a b : ℝ)
    (a_nonnegative : 0 ≤ a) (b_nonnegative : 0 ≤ b) (wave : IntegerWavevector) :
    wholeVelocity (NativeAbsoluteEventualControl.velocity seed b) wave -
        wholeVelocity (NativeAbsoluteEventualControl.velocity seed a) wave =
      ∫ time in a..b,
        projectedDivergenceCLM wave
            (NativeStressSource.quadraticFlux (wholeVelocity (NativeAbsoluteEventualControl.velocity seed time)) wave) -
          (nu.coeff * integerWaveViscousMultiplier wave) •
            wholeVelocity (NativeAbsoluteEventualControl.velocity seed time) wave :=
  (source_absolute_writes seed (max a b) (a_nonnegative.trans (le_max_left _ _))).between
    ⟨a_nonnegative, le_max_left _ _⟩ ⟨b_nonnegative, le_max_right _ _⟩ wave

theorem source_tail_momentum_write (seed : GeneratedWholeRestartCurrent nu)
    (time : ℝ) (nonnegative : 0 ≤ time) (wave : IntegerWavevector) :
    wholeBiotSavartVelocityState ((sourceTail seed).physicalPath time) wave -
        wholeBiotSavartVelocityState seed.initialState wave =
      ∫ earlier in (0 : ℝ)..(startTime seed + time),
        action nu (NativeAbsoluteEventualControl.velocity seed earlier) wave := by
  have written := (source_absolute_writes seed (startTime seed + time)
    (add_nonneg (startTime_nonnegative seed) nonnegative) wave).2
    (startTime seed + time) ⟨add_nonneg (startTime_nonnegative seed) nonnegative, le_rfl⟩
  simpa only [row, NativeAbsoluteEventualControl.velocity_initial, velocity_tail seed time nonnegative,
    wholeVelocity_punctured] using written

theorem source_early_momentum_write (seed : GeneratedWholeRestartCurrent nu) (wave : IntegerWavevector) :
    wholeBiotSavartVelocityState ((sourceTail seed).physicalPath 0) wave -
        wholeBiotSavartVelocityState seed.initialState wave =
      ∫ earlier in (0 : ℝ)..startTime seed,
        action nu (NativeAbsoluteEventualControl.velocity seed earlier) wave := by
  simpa only [add_zero] using source_tail_momentum_write seed 0 le_rfl wave

end
end SaturationMonoid.NavierStokes.NativeFiniteMacroMomentum
