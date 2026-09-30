import H0mework.NavierStokes.EndpointWork.WrittenComplementNativeWholeWrite
import H0mework.NavierStokes.Restart.GlobalPhysicalResidualWrittenProcess

/-!
# Written complement responsibility on the active global residual

The endpoint-written kinetic coordinates, their internally selected changed
native edge, and the complete old-run pair ledger already belong to one
endpoint macro event.  This module identifies the same two written
coordinates with the active global physical residual process before any
Fourier or pair quotient.

Consequently their residual difference is exactly the collective unforced
velocity write on the finite native segment stored by the same receipt.  In
the pair branch every dynamic innovation is the literal endpoint-written
pair coordinate minus its source-owned frozen contact occurrence; the
receipt's causal split and native exhaustion therefore consume the active
global residual rather than a parallel existential.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

open Set Filter
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointComponentOccurrenceMacroWrite
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointComponentOccurrenceMacroWrite.WholeRestartEndpointComponentMacroPhase
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointAlignedResponsibilityProcess
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointAlignedResponsibilityMacroWrite
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEndpointCofinalPairDuhamelMacroWrite
open
  _root_.SaturationMonoid.NavierStokes.ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEndpointKineticAtomSourceAnchorNativePairMacroWriteBack
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEndpointKineticAtomWrittenComplementNativeWholeWrite
open
  _root_.SaturationMonoid.NavierStokes.ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEndpointKineticAtomCollectiveCausalGapWrite
open AffineRelaxation

noncomputable section

namespace GeneratedInfiniteWholeRestartEndpointMacroLineage

/-- The two physical residual coordinates selected by a written complement
receipt cancel their common accumulation endpoint and leave exactly the
finite native segment carried by that receipt. -/
theorem
    WrittenKineticComplementNativeRedirect.globalPhysicalResidualDifference_eq_collectiveWrite
    {ν : Viscosity}
    {lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage ν}
    {stage requestedWrittenIndex : ℕ}
    (receipt :
      WrittenKineticComplementNativeRedirect
        (lineage.step stage) requestedWrittenIndex) :
    lineage.globalStagePhysicalResidual stage receipt.writtenLater -
        lineage.globalStagePhysicalResidual stage receipt.writtenEarlier =
      wholeRestartCollectiveCausalVelocityWrite
        (lineage.current stage) receipt.segmentStart receipt.segmentSteps := by
  rw [lineage.globalStagePhysicalResidual_eq_endpointVelocityResidual,
    lineage.globalStagePhysicalResidual_eq_endpointVelocityResidual]
  unfold wholeRestartEndpointVelocityResidual
  dsimp only
  rw [wholeRestartCollectiveCausalVelocityWrite_eq_gap]
  rw [receipt.segmentFinish_eq, receipt.segmentStart_eq]
  abel

/-- The uniquely forced trace of the endpoint full-pair process has the
active global physical residual tail as its concrete aligned coordinate.
This is the same trace written by every receipt's full-pair ledger field. -/
theorem globalStagePhysicalResidualTail_eq_fullPairForcedTrace
    {ν : Viscosity}
    (lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage ν)
    (stage : ℕ) :
    wholeRestartAlignedResponsibilityToVelocityResidualTail
        ((linearResidualTrace wholeRestartEndpointFullPairMacroKeep
          (wholeRestartEndpointFullPairMacroPending
            (lineage.current stage)
            (lineage.step stage).elapsedBounded accumulationRead)).1) =
      (generatedGlobalStagePhysicalResidualEffectiveProcess
        lineage stage).residual 0 := by
  rw [wholeRestartEndpointFullPairMacro_trace_eq_responsibility]
  exact
    lineage.globalStagePhysicalResidualProcess_eq_writtenAlignedProcess
      stage 0

/-- The aligned component of the exact full-pair boundary trace retains the
whole physical tail norm, whose limiting square mass is the endpoint atom. -/
theorem fullPairForcedTrace_aligned_norm_sq_tendsto_stageDefect
    {ν : Viscosity}
    (lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage ν)
    (stage : ℕ) :
    Tendsto
      (fun index =>
        ‖wholeRestartAlignedResponsibilityToVelocityResidualTail
            ((linearResidualTrace wholeRestartEndpointFullPairMacroKeep
              (wholeRestartEndpointFullPairMacroPending
                (lineage.current stage)
                (lineage.step stage).elapsedBounded
                accumulationRead)).1) index‖ ^ 2)
      atTop
      (nhds (infiniteEndpointMacroStageKineticDefect lineage stage)) := by
  have forcedTracePoint :
      ∀ index : ℕ,
        wholeRestartAlignedResponsibilityToVelocityResidualTail
            ((linearResidualTrace wholeRestartEndpointFullPairMacroKeep
              (wholeRestartEndpointFullPairMacroPending
                (lineage.current stage)
                (lineage.step stage).elapsedBounded
                accumulationRead)).1) index =
          lineage.globalStagePhysicalResidual stage index := by
    intro index
    have pointEq :=
      congrFun
        (lineage.globalStagePhysicalResidualTail_eq_fullPairForcedTrace
          stage)
        index
    simpa only [generatedGlobalStagePhysicalResidualEffectiveProcess,
      globalStagePhysicalResidualTail, zero_add] using pointEq
  simpa only [forcedTracePoint] using
    lineage.globalStagePhysicalResidual_norm_sq_tendsto_stageDefect stage

/-- A positive endpoint atom makes the aligned full-pair forced trace fail
whole-tail settlement.  This is stronger than mere nonzeroness of a finite
trace coordinate and uses no observer-faithfulness premise. -/
theorem fullPairForcedTrace_aligned_norm_sq_not_tendsto_zero_of_stageDefect_pos
    {ν : Viscosity}
    (lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage ν)
    (stage : ℕ)
    (defectPositive :
      0 < infiniteEndpointMacroStageKineticDefect lineage stage) :
    ¬ Tendsto
      (fun index =>
        ‖wholeRestartAlignedResponsibilityToVelocityResidualTail
            ((linearResidualTrace wholeRestartEndpointFullPairMacroKeep
              (wholeRestartEndpointFullPairMacroPending
                (lineage.current stage)
                (lineage.step stage).elapsedBounded
                accumulationRead)).1) index‖ ^ 2)
      atTop (nhds 0) := by
  intro tendsZero
  have defectZero :
      infiniteEndpointMacroStageKineticDefect lineage stage = 0 :=
    tendsto_nhds_unique
      (lineage.fullPairForcedTrace_aligned_norm_sq_tendsto_stageDefect
        stage)
      tendsZero
  linarith

/-- One actual global macro stage writes the active physical residual and the
complete pair carrier in the same event.  The source-owned zero/positive
split then either closes the atom or, after every requested written
coordinate, returns a receipt whose two coordinates are literally a segment
of that active residual process.

No residual endpoint, edge, output, pair, branch, target, or nonzero witness
is supplied by the caller. -/
theorem
    globalStageFullPairMacroWrite_generates_zero_or_writtenComplement_activePhysicalResidual
    {ν : Viscosity}
    (lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage ν)
    (stage : ℕ) :
    (wholeRestartEndpointFullPairMacroFrame
        (lineage.current stage)
        (lineage.step stage).elapsedBounded
        (wholeRestartEndpointComponentMacroUpdate accumulationRead)).1 =
        lineage.current (stage + 1) ∧
      (generatedWholeRestartEndpointFullPairMacroEffectiveProcess
          (lineage.current stage)
          (lineage.step stage).elapsedBounded).residual
          ((generatedWholeRestartEndpointFullPairMacroEffectiveProcess
            (lineage.current stage)
            (lineage.step stage).elapsedBounded).update accumulationRead) =
        (generatedWholeRestartEndpointFullPairMacroEffectiveProcess
          (lineage.current stage)
          (lineage.step stage).elapsedBounded).keep
          ((generatedWholeRestartEndpointFullPairMacroEffectiveProcess
            (lineage.current stage)
            (lineage.step stage).elapsedBounded).residual accumulationRead) ∧
      wholeRestartEndpointFullPairMacroTraceLedger
          (lineage.current stage)
          (lineage.step stage).elapsedBounded
          (wholeRestartEndpointComponentMacroUpdate accumulationRead) =
        wholeRestartEndpointFullPairMacroTraceLedger
            (lineage.current stage)
            (lineage.step stage).elapsedBounded accumulationRead +
          linearResidualTrace wholeRestartEndpointFullPairMacroKeep
            (wholeRestartEndpointFullPairMacroPending
              (lineage.current stage)
              (lineage.step stage).elapsedBounded accumulationRead) ∧
      wholeRestartAlignedResponsibilityToVelocityResidualTail
          ((linearResidualTrace wholeRestartEndpointFullPairMacroKeep
            (wholeRestartEndpointFullPairMacroPending
            (lineage.current stage)
            (lineage.step stage).elapsedBounded
            accumulationRead)).1) =
        (generatedGlobalStagePhysicalResidualEffectiveProcess
          lineage stage).residual 0 ∧
      (infiniteEndpointMacroStageKineticDefect lineage stage = 0 ∨
        (0 < infiniteEndpointMacroStageKineticDefect lineage stage ∧
          ¬ Tendsto
            (fun index =>
              ‖wholeRestartAlignedResponsibilityToVelocityResidualTail
                  ((linearResidualTrace
                    wholeRestartEndpointFullPairMacroKeep
                    (wholeRestartEndpointFullPairMacroPending
                      (lineage.current stage)
                      (lineage.step stage).elapsedBounded
                      accumulationRead)).1) index‖ ^ 2)
            atTop (nhds 0) ∧
          ∀ requestedWrittenIndex : ℕ,
            ∃ receipt :
                WrittenKineticComplementNativeRedirect
                  (lineage.step stage) requestedWrittenIndex,
              lineage.globalStagePhysicalResidual
                    stage receipt.writtenLater -
                  lineage.globalStagePhysicalResidual
                    stage receipt.writtenEarlier =
                wholeRestartCollectiveCausalVelocityWrite
                  (lineage.current stage)
                  receipt.segmentStart receipt.segmentSteps)) := by
  obtain ⟨physicalWrite, atomZeroOrWritten⟩ :=
    wholeRestartEndpointMacroStep_generates_zero_or_writtenComplementNoSilent_nativeWholeWrite
      (lineage.step stage)
  refine ⟨physicalWrite, ?_, ?_, ?_, ?_⟩
  · change
      (generatedWholeRestartEndpointFullPairMacroEffectiveProcess
          (lineage.current stage)
          (lineage.step stage).elapsedBounded).residual endpointWritten =
        (generatedWholeRestartEndpointFullPairMacroEffectiveProcess
          (lineage.current stage)
          (lineage.step stage).elapsedBounded).keep
          ((generatedWholeRestartEndpointFullPairMacroEffectiveProcess
            (lineage.current stage)
            (lineage.step stage).elapsedBounded).residual accumulationRead)
    exact
      (generatedWholeRestartEndpointFullPairMacroEffectiveProcess
        (lineage.current stage)
        (lineage.step stage).elapsedBounded).residual_transport_law
          accumulationRead
  · exact
      wholeRestartEndpointFullPairMacro_ledger_writeBack
        (lineage.current stage)
        (lineage.step stage).elapsedBounded
  · exact lineage.globalStagePhysicalResidualTail_eq_fullPairForcedTrace stage
  · rcases atomZeroOrWritten with atomZero | written
    · exact Or.inl <| by
        rw [infiniteEndpointMacroStageKineticDefect,
          ← (lineage.step stage).physicalStageKineticEnergyAtom_eq_defect]
        exact atomZero
    · rcases written with ⟨atomPositive, written⟩
      have defectPositive :
          0 < infiniteEndpointMacroStageKineticDefect lineage stage := by
        rw [infiniteEndpointMacroStageKineticDefect,
          ← (lineage.step stage).physicalStageKineticEnergyAtom_eq_defect]
        exact atomPositive
      refine Or.inr ⟨defectPositive, ?_, ?_⟩
      · exact
          lineage.fullPairForcedTrace_aligned_norm_sq_not_tendsto_zero_of_stageDefect_pos
            stage defectPositive
      intro requestedWrittenIndex
      obtain ⟨receipt⟩ := written requestedWrittenIndex
      exact
        ⟨receipt,
          WrittenKineticComplementNativeRedirect.globalPhysicalResidualDifference_eq_collectiveWrite
            receipt⟩

end GeneratedInfiniteWholeRestartEndpointMacroLineage

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
end NavierStokes
end SaturationMonoid
