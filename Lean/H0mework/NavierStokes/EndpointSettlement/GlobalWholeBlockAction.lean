import H0mework.NavierStokes.EndpointSettlement.WholeBlockCausalAction
import H0mework.NavierStokes.MacroRuntime.GlobalStrongInterfaceObstruction

/-!
# Reduced-core whole-block action on the global unforced path

Every contact of a reduced-core scale lineage already lies on the bounded
pre-accumulation chart of the same endpoint macro event.  This module
identifies those contacts with literal times of the authoritative global
unforced velocity path, before any coordinate projection.

The source-generated adjacent whole-state gap, positive native write-square
action, kinetic boundary, and complete tangent/output-by-pair boundary are
therefore all statements about two actual sections of that one global path.
The same endpoint event also writes the next macro current.  No path, scale,
node, time, cutoff, branch, target state, or continuity certificate is
accepted by the source-facing theorem.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

open Set Filter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartBoundedPreAccumulationPhysicalTrajectory
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointAbsoluteWholeMildNativeContinuation
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointComponentOccurrenceMacroWrite
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointComponentOccurrenceMacroWrite.WholeRestartEndpointComponentMacroPhase
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEndpointKineticAtomSourceAnchorNativePairMacroWriteBack
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEndpointKineticAtomCollectiveCausalGapWrite

noncomputable section

namespace GeneratedInfiniteWholeRestartEndpointMacroLineage

/-- The literal local macro time of one native contact endpoint.  It is
generated from the current run and lies strictly before the same stage's
accumulation interface. -/
def actualContactStageTime
    {ν : Viscosity}
    (lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage ν)
    (stage index : ℕ) :
    Icc (0 : ℝ) (lineage.step stage).clockAdvance :=
  ⟨elapsedTime (lineage.current stage) (index + 1),
    (lineage.current stage).elapsedTime_nonneg (index + 1), by
      have accumulationLeClock :
          wholeRestartVelocityAccumulationTime (lineage.current stage) ≤
            (lineage.step stage).clockAdvance := by
        rw [(lineage.step stage).clockAdvance_eq_selectedAbsoluteTime]
        let continuation :=
          sourceGeneratedWholeRestartVelocityEndpointAbsoluteWholeMildNativeContinuation
            (lineage.current stage) (lineage.step stage).elapsedBounded
        exact continuation.selectedAbsoluteTime_gt_accumulation.le
      exact
        ((elapsedTime_lt_wholeRestartVelocityAccumulationTime
            (lineage.current stage) (lineage.step stage).elapsedBounded
            (index + 1)).trans_le accumulationLeClock).le⟩

/-- The same contact time on the single global macro clock. -/
def actualContactGlobalTime
    {ν : Viscosity}
    (lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage ν)
    (stage index : ℕ) : ℝ :=
  lineage.macroClock stage +
    elapsedTime (lineage.current stage) (index + 1)

/-- The local macro chart at a native contact time is exactly that contact's
complete physical velocity state. -/
theorem physicalStage_actualContactStageTime
    {ν : Viscosity}
    (lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage ν)
    (stage index : ℕ) :
    (lineage.step stage).physicalStage
        (lineage.actualContactStageTime stage index) =
      wholeRestartContactVelocityState (lineage.current stage) index := by
  rw [GeneratedWholeRestartEndpointMacroStep.physicalStage]
  rw [
    sourceGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice_of_lt]
  · simpa [actualContactStageTime,
      GeneratedWholeRestartEndpointMacroStep.physicalStageTime,
      wholeRestartContactEndpointPreAccumulationTime] using
      wholeRestartBoundedPreAccumulationVelocityTrajectory_contactEndpoint
        (lineage.current stage) (lineage.step stage).elapsedBounded index
  · simpa [actualContactStageTime,
      GeneratedWholeRestartEndpointMacroStep.physicalStageTime] using
      elapsedTime_lt_wholeRestartVelocityAccumulationTime
        (lineage.current stage) (lineage.step stage).elapsedBounded
        (index + 1)

/-- Every actual native contact is a literal section of the authoritative
global unforced velocity path. -/
theorem globalAbsoluteVelocityTrajectory_actualContact
    {ν : Viscosity}
    (lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage ν)
    (stage index : ℕ) :
    lineage.globalAbsoluteVelocityTrajectory
        (lineage.actualContactGlobalTime stage index) =
      wholeRestartContactVelocityState (lineage.current stage) index := by
  rw [actualContactGlobalTime]
  simpa [actualContactStageTime] using
    (lineage.globalAbsoluteVelocityTrajectory_eq_stage
      stage (lineage.actualContactStageTime stage index)).trans
        (lineage.physicalStage_actualContactStageTime stage index)

/-- The terminal clock of the same macro event is the actual complete
velocity state written into the next source current. -/
theorem globalAbsoluteVelocityTrajectory_macroEndpoint
    {ν : Viscosity}
    (lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage ν)
    (stage : ℕ) :
    lineage.globalAbsoluteVelocityTrajectory
        (lineage.macroClock (stage + 1)) =
      puncturedWholeVelocityEuclideanState
        (lineage.current (stage + 1)).initialState := by
  calc
    lineage.globalAbsoluteVelocityTrajectory
          (lineage.macroClock (stage + 1)) =
        lineage.finiteMacroAbsoluteVelocityTrajectory
          (stage + 1) (lineage.macroClock (stage + 1)) :=
      lineage.globalAbsoluteVelocityTrajectory_eq_prefix
        (stage + 1) le_rfl
    _ = puncturedWholeVelocityEuclideanState
          (lineage.current (stage + 1)).initialState :=
      lineage.finiteMacroAbsoluteVelocityTrajectory_endpoint (stage + 1)

/-- Source-generated scale occurrences remain strictly ordered on the actual
global physical clock. -/
theorem
    WholeRestartReducedCoreScaleLineage.actualContactGlobalTime_strictMono
    {ν : Viscosity}
    {lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage ν}
    {stage : ℕ}
    (scale : WholeRestartReducedCoreScaleLineage
      (lineage.current stage)) :
    StrictMono
      (fun node =>
        lineage.actualContactGlobalTime
          stage (scale.absoluteOccurrence node)) := by
  intro left right leftLtRight
  unfold actualContactGlobalTime
  simpa [Nat.succ_eq_add_one, add_comm] using
    add_lt_add_left
      (elapsedTime_strictMono (lineage.current stage)
        (Nat.succ_lt_succ
          (scale.absoluteOccurrence_strict leftLtRight)))
      (lineage.macroClock stage)

/-- The actual reduced-core contact endpoints approach the same global stage
accumulation interface that carries the kinetic completion defect. -/
theorem
    WholeRestartReducedCoreScaleLineage.actualContactGlobalTime_tendsto_interface
    {ν : Viscosity}
    {lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage ν}
    {stage : ℕ}
    (scale : WholeRestartReducedCoreScaleLineage
      (lineage.current stage)) :
    Tendsto
      (fun node =>
        lineage.actualContactGlobalTime
          stage (scale.absoluteOccurrence node))
      atTop (nhds (lineage.globalStageAccumulationTime stage)) := by
  have elapsedTendsto :
      Tendsto (elapsedTime (lineage.current stage)) atTop
        (nhds
          (wholeRestartVelocityAccumulationTime
            (lineage.current stage))) := by
    change Tendsto (elapsedTime (lineage.current stage)) atTop
      (nhds
        (⨆ index : ℕ, elapsedTime (lineage.current stage) index))
    exact
      tendsto_atTop_ciSup
        (elapsedTime_strictMono (lineage.current stage)).monotone
        (lineage.step stage).elapsedBounded
  have occurrenceSuccStrict :
      StrictMono (fun node => scale.absoluteOccurrence node + 1) := by
    intro left right leftLtRight
    exact Nat.add_lt_add_right
      (scale.absoluteOccurrence_strict leftLtRight) 1
  have sampled :=
    elapsedTendsto.comp occurrenceSuccStrict.tendsto_atTop
  simpa [actualContactGlobalTime, globalStageAccumulationTime] using
    tendsto_const_nhds.add sampled

/-- Action-local segment custody: on the entire physical interval between
two adjacent scale contacts, the global path is literally the same
source-native macro trajectory, not a second completion or a restarted
observer path. -/
theorem
    WholeRestartReducedCoreScaleLineage.globalPath_eq_physicalStageTrajectory_on_block
    {ν : Viscosity}
    {lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage ν}
    {stage : ℕ}
    (scale : WholeRestartReducedCoreScaleLineage
      (lineage.current stage))
    (node : ℕ) :
    Set.EqOn
      (fun localTime =>
        lineage.globalAbsoluteVelocityTrajectory
          (lineage.macroClock stage + localTime))
      (lineage.step stage).physicalStageTrajectory
      (Icc
        (elapsedTime (lineage.current stage)
          (scale.absoluteOccurrence node + 1))
        (elapsedTime (lineage.current stage)
          (scale.absoluteOccurrence (node + 1) + 1))) := by
  intro localTime timeMem
  have localTimeNonneg :
      0 ≤ localTime :=
    ((lineage.current stage).elapsedTime_nonneg
      (scale.absoluteOccurrence node + 1)).trans timeMem.1
  have localTimeLeClock :
      localTime ≤ (lineage.step stage).clockAdvance :=
    timeMem.2.trans
      (lineage.actualContactStageTime
        stage (scale.absoluteOccurrence (node + 1))).2.2
  let stageTime :
      Icc (0 : ℝ) (lineage.step stage).clockAdvance :=
    ⟨localTime, localTimeNonneg, localTimeLeClock⟩
  calc
    lineage.globalAbsoluteVelocityTrajectory
          (lineage.macroClock stage + localTime) =
        (lineage.step stage).physicalStage stageTime := by
      simpa only [stageTime] using
        lineage.globalAbsoluteVelocityTrajectory_eq_stage stage stageTime
    _ = (lineage.step stage).physicalStageTrajectory localTime := by
      symm
      simpa only [stageTime] using
        (lineage.step stage).physicalStageTrajectory_eq_stage stageTime

/-- The adjacent reduced-core block is the exact velocity write between two
sections of the same global unforced path. -/
theorem
    WholeRestartReducedCoreScaleLineage.globalPathWholeBlockWrite
    {ν : Viscosity}
    {lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage ν}
    {stage : ℕ}
    (scale : WholeRestartReducedCoreScaleLineage
      (lineage.current stage))
    (node : ℕ) :
    lineage.globalAbsoluteVelocityTrajectory
          (lineage.actualContactGlobalTime
            stage (scale.absoluteOccurrence (node + 1))) -
        lineage.globalAbsoluteVelocityTrajectory
          (lineage.actualContactGlobalTime
            stage (scale.absoluteOccurrence node)) =
      wholeRestartCollectiveCausalVelocityWrite
        (lineage.current stage) (scale.absoluteOccurrence node)
          (scale.nextScaleGap node) := by
  rw [lineage.globalAbsoluteVelocityTrajectory_actualContact,
    lineage.globalAbsoluteVelocityTrajectory_actualContact]
  exact (scale.wholeBlockCollectiveVelocityWrite_eq_gap node).symm

/-- The two global-path sections of every adjacent reduced-core block are
distinct. -/
theorem
    WholeRestartReducedCoreScaleLineage.globalPathWholeBlockWrite_ne_zero
    {ν : Viscosity}
    {lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage ν}
    {stage : ℕ}
    (scale : WholeRestartReducedCoreScaleLineage
      (lineage.current stage))
    (node : ℕ) :
    lineage.globalAbsoluteVelocityTrajectory
          (lineage.actualContactGlobalTime
            stage (scale.absoluteOccurrence (node + 1))) -
        lineage.globalAbsoluteVelocityTrajectory
          (lineage.actualContactGlobalTime
            stage (scale.absoluteOccurrence node)) ≠ 0 := by
  rw [scale.globalPathWholeBlockWrite node]
  exact scale.wholeBlockCollectiveVelocityWrite_ne_zero node

/-- Exact whole-block kinetic boundary, now written directly on the global
unforced path rather than a parallel contact-state observer. -/
theorem
    WholeRestartReducedCoreScaleLineage.globalPathWholeBlockKineticBoundary
    {ν : Viscosity}
    {lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage ν}
    {stage : ℕ}
    (scale : WholeRestartReducedCoreScaleLineage
      (lineage.current stage))
    (node : ℕ) :
    2 * scale.wholeBlockIncomingVelocityWork node +
        scale.wholeBlockNativeVelocitySquare node =
      ‖lineage.globalAbsoluteVelocityTrajectory
          (lineage.actualContactGlobalTime
            stage (scale.absoluteOccurrence (node + 1)))‖ ^ 2 -
        ‖lineage.globalAbsoluteVelocityTrajectory
          (lineage.actualContactGlobalTime
            stage (scale.absoluteOccurrence node))‖ ^ 2 := by
  rw [lineage.globalAbsoluteVelocityTrajectory_actualContact,
    lineage.globalAbsoluteVelocityTrajectory_actualContact]
  exact scale.wholeBlockKineticBoundary_telescope node

/-- The complete tangent/output-by-pair boundary is the same global-path
kinetic boundary. -/
theorem
    WholeRestartReducedCoreScaleLineage.globalPathWholeBlockComponentBoundary
    {ν : Viscosity}
    {lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage ν}
    {stage : ℕ}
    (scale : WholeRestartReducedCoreScaleLineage
      (lineage.current stage))
    (node : ℕ) :
    scale.wholeBlockComponentKineticBoundary node =
      ‖lineage.globalAbsoluteVelocityTrajectory
          (lineage.actualContactGlobalTime
            stage (scale.absoluteOccurrence (node + 1)))‖ ^ 2 -
        ‖lineage.globalAbsoluteVelocityTrajectory
          (lineage.actualContactGlobalTime
            stage (scale.absoluteOccurrence node))‖ ^ 2 := by
  rw [lineage.globalAbsoluteVelocityTrajectory_actualContact,
    lineage.globalAbsoluteVelocityTrajectory_actualContact]
  exact scale.wholeBlockComponentKineticBoundary_telescope node

/-- One reduced-core branch fused to the authoritative global path and to the
same endpoint event that writes the next macro current. -/
structure WholeRestartReducedCoreGlobalWholeBlockAction
    {ν : Viscosity}
    (lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage ν)
    (stage : ℕ) where
  scale :
    WholeRestartReducedCoreScaleLineage (lineage.current stage)
  endpoint_write :
    wholeRestartEndpointFullPairPhysicalMacroFrame
        (lineage.current stage) (lineage.step stage).elapsedBounded
        (wholeRestartEndpointComponentMacroUpdate accumulationRead) =
      (lineage.current (stage + 1),
        0,
        (wholeRestartEndpointFullPairMacroPending
            (lineage.current stage) (lineage.step stage).elapsedBounded
              accumulationRead,
          wholeRestartPhysicalVorticityTail
            (lineage.current stage) 0 0))
  global_endpoint_write :
    lineage.globalAbsoluteVelocityTrajectory
        (lineage.macroClock (stage + 1)) =
      puncturedWholeVelocityEuclideanState
        (lineage.current (stage + 1)).initialState
  contact_time_strict :
    StrictMono
      (fun node =>
        lineage.actualContactGlobalTime
          stage (scale.absoluteOccurrence node))
  contact_time_tendsto_interface :
    Tendsto
      (fun node =>
        lineage.actualContactGlobalTime
          stage (scale.absoluteOccurrence node))
      atTop (nhds (lineage.globalStageAccumulationTime stage))
  segment_custody :
    ∀ node : ℕ,
      Set.EqOn
        (fun localTime =>
          lineage.globalAbsoluteVelocityTrajectory
            (lineage.macroClock stage + localTime))
        (lineage.step stage).physicalStageTrajectory
        (Icc
          (elapsedTime (lineage.current stage)
            (scale.absoluteOccurrence node + 1))
          (elapsedTime (lineage.current stage)
            (scale.absoluteOccurrence (node + 1) + 1)))
  block_write :
    ∀ node : ℕ,
      lineage.globalAbsoluteVelocityTrajectory
            (lineage.actualContactGlobalTime
              stage (scale.absoluteOccurrence (node + 1))) -
          lineage.globalAbsoluteVelocityTrajectory
            (lineage.actualContactGlobalTime
              stage (scale.absoluteOccurrence node)) =
        wholeRestartCollectiveCausalVelocityWrite
          (lineage.current stage) (scale.absoluteOccurrence node)
            (scale.nextScaleGap node)
  block_write_ne_zero :
    ∀ node : ℕ,
      lineage.globalAbsoluteVelocityTrajectory
            (lineage.actualContactGlobalTime
              stage (scale.absoluteOccurrence (node + 1))) -
          lineage.globalAbsoluteVelocityTrajectory
            (lineage.actualContactGlobalTime
              stage (scale.absoluteOccurrence node)) ≠ 0
  block_square_pos :
    ∀ node : ℕ, 0 < scale.wholeBlockNativeVelocitySquare node
  block_work_neg :
    ∀ node : ℕ, scale.wholeBlockIncomingVelocityWork node < 0
  kinetic_boundary :
    ∀ node : ℕ,
      2 * scale.wholeBlockIncomingVelocityWork node +
          scale.wholeBlockNativeVelocitySquare node =
        ‖lineage.globalAbsoluteVelocityTrajectory
            (lineage.actualContactGlobalTime
              stage (scale.absoluteOccurrence (node + 1)))‖ ^ 2 -
          ‖lineage.globalAbsoluteVelocityTrajectory
            (lineage.actualContactGlobalTime
              stage (scale.absoluteOccurrence node))‖ ^ 2
  component_boundary :
    ∀ node : ℕ,
      scale.wholeBlockComponentKineticBoundary node =
        ‖lineage.globalAbsoluteVelocityTrajectory
            (lineage.actualContactGlobalTime
              stage (scale.absoluteOccurrence (node + 1)))‖ ^ 2 -
          ‖lineage.globalAbsoluteVelocityTrajectory
            (lineage.actualContactGlobalTime
              stage (scale.absoluteOccurrence node))‖ ^ 2

/-- Positive stage defect now source-generates a reduced-core action on the
actual global unforced path, a native gluing redirect, or the bounded-core
aggregate branch.  The reduced-core scale and every block witness are
generated internally. -/
theorem
    stageDefect_generates_zero_or_globalWholeBlockAction_or_nativeGluing_or_atomScaleAggregateLineage
    {ν : Viscosity}
    (lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage ν)
    (stage : ℕ) :
    infiniteEndpointMacroStageKineticDefect lineage stage = 0 ∨
      (0 < infiniteEndpointMacroStageKineticDefect lineage stage ∧
        (Nonempty
            (WholeRestartReducedCoreGlobalWholeBlockAction lineage stage) ∨
          wholeRestartNativeGluingResponsibility
              (lineage.current stage) ∨
          wholeRestartAtomScaleAggregateResponsibility
            (lineage.current stage)
            (infiniteEndpointMacroStageKineticDefect lineage stage / 2))) := by
  rcases
      lineage.stageDefect_generates_zero_or_reducedCoreScaleLineage_or_nativeGluing_or_atomScaleAggregateLineage
        stage with
    defectZero | ⟨defectPositive, reduced | nativeOrAggregate⟩
  · exact Or.inl defectZero
  · obtain ⟨scale⟩ := reduced
    obtain ⟨endpointWrite, _blockAction⟩ :=
      wholeRestartEndpointMacroStep_reducedCore_generates_wholeBlockCausalAction
        (lineage.step stage)
    exact Or.inr
      ⟨defectPositive, Or.inl
        ⟨{ scale := scale
           endpoint_write := endpointWrite
           global_endpoint_write :=
             lineage.globalAbsoluteVelocityTrajectory_macroEndpoint stage
           contact_time_strict := scale.actualContactGlobalTime_strictMono
           contact_time_tendsto_interface :=
             scale.actualContactGlobalTime_tendsto_interface
           segment_custody :=
             scale.globalPath_eq_physicalStageTrajectory_on_block
           block_write := scale.globalPathWholeBlockWrite
           block_write_ne_zero := scale.globalPathWholeBlockWrite_ne_zero
           block_square_pos := scale.wholeBlockNativeVelocitySquare_pos
           block_work_neg := scale.wholeBlockIncomingVelocityWork_neg
           kinetic_boundary := scale.globalPathWholeBlockKineticBoundary
           component_boundary :=
             scale.globalPathWholeBlockComponentBoundary }⟩⟩
  · exact Or.inr ⟨defectPositive, Or.inr nativeOrAggregate⟩

end GeneratedInfiniteWholeRestartEndpointMacroLineage

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
end NavierStokes
end SaturationMonoid
