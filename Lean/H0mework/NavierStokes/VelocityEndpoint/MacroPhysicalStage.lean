import H0mework.NavierStokes.MacroRuntime.Runtime
import H0mework.NavierStokes.Restart.BoundedAccumulationAbsoluteVelocitySplice

/-!
# Actual physical stage carried by one recursive endpoint macro write

Every recursive endpoint macro edge already owns an exact physical clock,
the bounded old-run velocity path, the endpoint whole-mild write, the next
whole-restart current, and the complete aligned component/kinetic trace.
This module places those objects on one stage interval before recursively
splicing stages along `macroClock`.

The stage has no caller-selected path, endpoint, duration, defect branch or
trace.  Its initial and terminal physical velocities are the Biot--Savart
projections of the edge source and target.  At the internal accumulation
interface the source itself exhausts the two honest outcomes: zero kinetic
defect gives the existing whole-`L²` strong gluing law, while positive defect
writes a nonzero aligned trace in that exact macro response.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

open Set Filter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticWeakEndpoint
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinFamily
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinVelocityWeakLimit
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointComponentOccurrenceMacroWrite
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointComponentOccurrenceMacroWrite.WholeRestartEndpointComponentMacroPhase
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointAlignedResponsibilityProcess
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointAlignedResponsibilityMacroWrite
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointAlignedResponsibilityNativeReachableWrite
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointPositiveTimeH1Reentry
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointAbsoluteWholeMildNativeContinuation
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointNativeReachableContinuation
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointNativeReachableContinuation.GeneratedWholeRestartVelocityEndpointRuntimeState
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartBoundedPreAccumulationPhysicalTrajectory
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationWholeNSVelocityJoin

noncomputable section

namespace GeneratedWholeRestartEndpointMacroStep

/-- The macro edge clock is literally the absolute source-selected endpoint
time, measured from the current's own zero clock. -/
theorem clockAdvance_eq_selectedAbsoluteTime
    {ν : Viscosity}
    {current next : GeneratedWholeRestartCurrent ν}
    (step : GeneratedWholeRestartEndpointMacroStep ν current next) :
    step.clockAdvance =
      (sourceGeneratedWholeRestartVelocityEndpointSelectedAbsoluteTime
        current step.elapsedBounded).1 := by
  cases step
  rw [
    sourceGeneratedWholeRestartVelocityEndpointSelectedAbsoluteTime_eq_nativeTemporal]
  rfl

theorem clockAdvance_pos
    {ν : Viscosity}
    {current next : GeneratedWholeRestartCurrent ν}
    (step : GeneratedWholeRestartEndpointMacroStep ν current next) :
    0 < step.clockAdvance := by
  linarith [step.half_lt_clockAdvance]

/-- Embed the exact stage clock interval into the already generated complete
absolute splice. -/
def physicalStageTime
    {ν : Viscosity}
    {current next : GeneratedWholeRestartCurrent ν}
    (step : GeneratedWholeRestartEndpointMacroStep ν current next)
    (time : Icc (0 : ℝ) step.clockAdvance) :
    Icc (0 : ℝ) (wholeRestartVelocityAccumulationTime current + 1) :=
  ⟨time.1, time.2.1, by
    calc
      time.1 ≤ step.clockAdvance := time.2.2
      _ =
          (sourceGeneratedWholeRestartVelocityEndpointSelectedAbsoluteTime
            current step.elapsedBounded).1 :=
        step.clockAdvance_eq_selectedAbsoluteTime
      _ ≤ wholeRestartVelocityAccumulationTime current + 1 :=
        (sourceGeneratedWholeRestartVelocityEndpointSelectedAbsoluteTime
          current step.elapsedBounded).2.2⟩

theorem physicalStageTime_continuous
    {ν : Viscosity}
    {current next : GeneratedWholeRestartCurrent ν}
    (step : GeneratedWholeRestartEndpointMacroStep ν current next) :
    Continuous step.physicalStageTime := by
  apply Continuous.subtype_mk
  exact continuous_subtype_val

/-- The actual complete-velocity path read by this exact recursive macro
edge, restricted to the interval ending at its written next current. -/
def physicalStage
    {ν : Viscosity}
    {current next : GeneratedWholeRestartCurrent ν}
    (step : GeneratedWholeRestartEndpointMacroStep ν current next) :
    Icc (0 : ℝ) step.clockAdvance → WholeRestartVelocityEndpointState :=
  fun time =>
    sourceGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice
      current step.elapsedBounded (step.physicalStageTime time)

def physicalStageZero
    {ν : Viscosity}
    {current next : GeneratedWholeRestartCurrent ν}
    (step : GeneratedWholeRestartEndpointMacroStep ν current next) :
    Icc (0 : ℝ) step.clockAdvance :=
  ⟨0, le_rfl, step.clockAdvance_pos.le⟩

def physicalStageTerminal
    {ν : Viscosity}
    {current next : GeneratedWholeRestartCurrent ν}
    (step : GeneratedWholeRestartEndpointMacroStep ν current next) :
    Icc (0 : ℝ) step.clockAdvance :=
  ⟨step.clockAdvance, step.clockAdvance_pos.le, le_rfl⟩

/-- The physical stage starts at the complete Biot--Savart velocity of the
literal macro source current. -/
theorem physicalStage_zero
    {ν : Viscosity}
    {current next : GeneratedWholeRestartCurrent ν}
    (step : GeneratedWholeRestartEndpointMacroStep ν current next) :
    step.physicalStage step.physicalStageZero =
      puncturedWholeVelocityEuclideanState current.initialState := by
  cases step with
  | advance bounded =>
      have accumulationPos :
          0 < wholeRestartVelocityAccumulationTime current := by
        simpa only [elapsedTime_zero] using
          elapsedTime_lt_wholeRestartVelocityAccumulationTime
            current bounded 0
      rw [physicalStage,
        sourceGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice_of_lt
          current bounded _ accumulationPos]
      unfold wholeRestartBoundedPreAccumulationVelocityTrajectory
      congr 1
      rw [
        wholeRestartBoundedPreAccumulationPhysicalTrajectory_eq_prefix
          current bounded _ 0]
      · rfl
      · change (0 : ℝ) ≤ elapsedTime current 0
        simp [elapsedTime_zero]

/-- The terminal value of the same stage is exactly the physical velocity
of the dependent target current written by the macro edge. -/
theorem physicalStage_terminal
    {ν : Viscosity}
    {current next : GeneratedWholeRestartCurrent ν}
    (step : GeneratedWholeRestartEndpointMacroStep ν current next) :
    step.physicalStage step.physicalStageTerminal =
      puncturedWholeVelocityEuclideanState next.initialState := by
  cases step with
  | advance bounded =>
      let advance :=
        GeneratedWholeRestartEndpointMacroStep.advance current bounded
      have timeEq :
          advance.physicalStageTime advance.physicalStageTerminal =
            wholeRestartBoundedAccumulationSelectedAbsoluteTime
              current bounded := by
        apply Subtype.ext
        exact advance.clockAdvance_eq_selectedAbsoluteTime
      have pathEq := congrArg
        (sourceGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice
          current bounded) timeEq
      have conditionalTerminal :
          sourceGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice
              current bounded
              (wholeRestartBoundedAccumulationSelectedAbsoluteTime
                current bounded) =
            puncturedWholeVelocityEuclideanState
              (sourceGeneratedWholeRestartVelocityEndpointNextCurrent
                current bounded).initialState := by
        simpa only [afterCurrent_zero] using
          sourceGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice_selected_eq_afterZeroInitial
            current bounded
      have stageConditional :
          advance.physicalStage advance.physicalStageTerminal =
            puncturedWholeVelocityEuclideanState
              (sourceGeneratedWholeRestartVelocityEndpointNextCurrent
                current bounded).initialState := by
        simpa only [physicalStage] using pathEq.trans conditionalTerminal
      have targetEq := congrArg
        (fun target : GeneratedWholeRestartCurrent ν =>
          puncturedWholeVelocityEuclideanState target.initialState)
        (sourceGeneratedWholeRestartVelocityEndpointNextCurrent_eq_rootCofinalPhysicalNext
          current bounded)
      exact stageConditional.trans targetEq

/-- On the post-accumulation part of this exact macro stage, every nonzero
physical Fourier row is the generated unforced heat--Duhamel write. -/
theorem physicalStage_row_mildIdentity_of_accumulation_le
    {ν : Viscosity}
    {current next : GeneratedWholeRestartCurrent ν}
    (step : GeneratedWholeRestartEndpointMacroStep ν current next)
    (time : Icc (0 : ℝ) step.clockAdvance)
    (timeAfter :
      wholeRestartVelocityAccumulationTime current ≤ time.1)
    (wave :
      ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger.NonzeroIntegerWavevector)
    (coordinate : ThreeDimensionalPeriodicCoarseFilterCore.Coordinate) :
    let ledger :=
      generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
        current step.elapsedBounded
    let endpoint :=
      sourceGeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt
        current step.elapsedBounded
    step.physicalStage time wave coordinate =
      ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteMildDuhamel.fixedWaveHeatDuhamelValue
          1 ν.coeff wave.1
          (wholeRestartVelocityEndpointCoefficient
            ledger.family.endpointReceipt.velocityEndpoint wave.1)
          (wholeVelocityLerayProjectionSpaceTime wave.1
            (endpoint.core.nonlinearLimit wave.1))
          (endpointAbsoluteToLocalTime
            (wholeRestartVelocityAccumulationTime current)
            ⟨time.1, timeAfter,
              (step.physicalStageTime time).2.2⟩)
        coordinate := by
  dsimp only
  exact
    sourceGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice_row_mildIdentity_of_ge
      current step.elapsedBounded (step.physicalStageTime time)
      timeAfter wave coordinate

/-- The internal old-run accumulation time as a point of this exact macro
stage. -/
def physicalStageAccumulation
    {ν : Viscosity}
    {current next : GeneratedWholeRestartCurrent ν}
    (step : GeneratedWholeRestartEndpointMacroStep ν current next) :
    Icc (0 : ℝ) step.clockAdvance :=
  ⟨wholeRestartVelocityAccumulationTime current, by
    constructor
    · have bounded := step.elapsedBounded
      unfold wholeRestartVelocityAccumulationTime
      exact le_ciSup bounded 0
    · rw [step.clockAdvance_eq_selectedAbsoluteTime]
      exact
        (sourceGeneratedWholeRestartVelocityEndpointAbsoluteWholeMildNativeContinuation
          current step.elapsedBounded).selectedAbsoluteTime_gt_accumulation.le⟩

/-- Zero kinetic defect closes the unique internal accumulation interface
strongly on the complete physical velocity carrier. -/
theorem physicalStage_continuousAt_accumulation_of_kineticDefect_eq_zero
    {ν : Viscosity}
    {current next : GeneratedWholeRestartCurrent ν}
    (step : GeneratedWholeRestartEndpointMacroStep ν current next)
    (defectZero :
      wholeRestartKineticWeakEndpointDefect current
          (generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
            current step.elapsedBounded).family.endpointReceipt.kineticReceipt.endpoint =
        0) :
    ContinuousAt step.physicalStage step.physicalStageAccumulation := by
  have spliceContinuous :=
    sourceGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice_continuousAt_start_of_kineticDefect_eq_zero
      current step.elapsedBounded defectZero
  have timeContinuous :
      ContinuousAt step.physicalStageTime step.physicalStageAccumulation :=
    step.physicalStageTime_continuous.continuousAt
  have timeEq :
      step.physicalStageTime step.physicalStageAccumulation =
        wholeRestartBoundedAccumulationAbsoluteVelocitySpliceStart
          current step.elapsedBounded := by
    apply Subtype.ext
    rfl
  rw [← timeEq] at spliceContinuous
  exact spliceContinuous.comp timeContinuous

/-- The complete aligned trace written by this exact physical macro edge. -/
def alignedTrace
    {ν : Viscosity}
    {current next : GeneratedWholeRestartCurrent ν}
    (step : GeneratedWholeRestartEndpointMacroStep ν current next) :
    WholeRestartEndpointAlignedResponsibilityTail :=
  wholeRestartEndpointAlignedMacroTraceLedger current step.elapsedBounded
    (wholeRestartEndpointComponentMacroUpdate accumulationRead)

/-- Positive kinetic defect cannot be silent in the aligned trace written by
this physical macro stage. -/
theorem alignedTrace_ne_zero_of_kineticDefect_pos
    {ν : Viscosity}
    {current next : GeneratedWholeRestartCurrent ν}
    (step : GeneratedWholeRestartEndpointMacroStep ν current next)
    (defectPos :
      0 < wholeRestartKineticWeakEndpointDefect current
        (generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
          current step.elapsedBounded).family.endpointReceipt.kineticReceipt.endpoint) :
    step.alignedTrace ≠ 0 :=
  wholeRestartEndpointAlignedMacroTraceLedger_ne_zero_of_defect_pos
    step.elapsedBounded defectPos

/-- Source-owned stage exhaustion on the common physical/residual carrier:
the internal interface is strongly closed, or the very same native response
writes a nonzero aligned responsibility. -/
theorem continuousAt_accumulation_or_alignedTrace_ne_zero
    {ν : Viscosity}
    {current next : GeneratedWholeRestartCurrent ν}
    (step : GeneratedWholeRestartEndpointMacroStep ν current next) :
    ContinuousAt step.physicalStage step.physicalStageAccumulation ∨
      step.alignedTrace ≠ 0 := by
  let receipt :=
    (generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
      current step.elapsedBounded).family.endpointReceipt.kineticReceipt
  rcases receipt.defect_disposition with defectPos | ⟨defectZero, _strong⟩
  · exact Or.inr (step.alignedTrace_ne_zero_of_kineticDefect_pos defectPos)
  · exact Or.inl
      (step.physicalStage_continuousAt_accumulation_of_kineticDefect_eq_zero
        defectZero)

end GeneratedWholeRestartEndpointMacroStep

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
end NavierStokes
end SaturationMonoid
