import H0mework.NavierStokes.VelocityEndpoint.MacroPhysicalStage

/-!
# Global absolute velocity of an infinite endpoint-macro lineage

Each edge of an infinite endpoint-macro lineage already owns one bounded
absolute velocity splice.  This module truncates that splice at the edge's
source-selected physical time, joins the resulting charts at their literal
next-current initial states, and stabilizes the finite joins along the
source-generated unbounded macro clock.

The all-zero kinetic-defect branch is selected from the kinetic receipts'
own dispositions.  A caller supplies neither a path nor a partition,
cutoff, gluing equality, continuation witness, or defect branch.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

open scoped ENNReal

open Set Filter
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientFinitePhysicalTrajectoryEndpointSplice
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticWeakEndpoint
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointAbsoluteWholeMildNativeContinuation
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartBoundedPreAccumulationPhysicalTrajectory
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointNativeReachableContinuation
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointNativeReachableContinuation.GeneratedWholeRestartVelocityEndpointRuntimeState
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointComponentOccurrenceMacroWrite
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointComponentOccurrenceMacroWrite.WholeRestartEndpointComponentMacroPhase
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointAlignedResponsibilityNativeReachableWrite
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

noncomputable section

private theorem wholeRestartVelocityEndpointState_apply_continuous
    (wave : NonzeroIntegerWavevector) :
    Continuous
      (fun state : WholeRestartVelocityEndpointState => state wave) := by
  apply LipschitzWith.continuous (K := 1)
  rw [lipschitzWith_iff_dist_le_mul]
  intro left right
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  have bound :=
    lp.norm_apply_le_norm
      (by norm_num : (2 : ENNReal) ≠ 0) (left - right) wave
  rw [lp.coeFn_sub, Pi.sub_apply] at bound
  exact bound

/-- Every Fourier row of one complete bounded splice is continuous on its
whole absolute stage.  Hilbert-weak endpoint convergence closes the finite
row at the internal interface; no kinetic-defect branch is needed. -/
theorem
    sourceGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice_coordinate_continuous
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (wave : NonzeroIntegerWavevector) :
    Continuous fun time :
        Icc (0 : ℝ) (wholeRestartVelocityAccumulationTime initial + 1) =>
      sourceGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice
        initial elapsedBounded time wave := by
  rw [continuous_iff_continuousAt]
  intro time
  let start :=
    wholeRestartBoundedAccumulationAbsoluteVelocitySpliceStart
      initial elapsedBounded
  by_cases atStart : time = start
  · subst time
    exact
      (PiLp.continuous_toLp
        (2 : ENNReal) (fun _ : Coordinate => ℂ)).continuousAt.comp
          (continuousAt_pi.mpr fun coordinate =>
            sourceGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice_coordinate_continuousAt_start
              initial elapsedBounded wave coordinate)
  · by_cases before :
        time.1 < wholeRestartVelocityAccumulationTime initial
    · let beforeSet :
          Set
            (Icc (0 : ℝ)
              (wholeRestartVelocityAccumulationTime initial + 1)) :=
        {point | point.1 < wholeRestartVelocityAccumulationTime initial}
      let toPre :
          beforeSet →
            Ico (0 : ℝ) (wholeRestartVelocityAccumulationTime initial) :=
        fun point => ⟨point.1.1, point.1.2.1, point.2⟩
      have toPreContinuous : Continuous toPre := by
        apply Continuous.subtype_mk
        exact continuous_subtype_val.comp continuous_subtype_val
      have restrictedContinuous :
          Continuous fun point : beforeSet =>
            sourceGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice
              initial elapsedBounded point.1 wave := by
        have preContinuous :=
          (wholeRestartVelocityEndpointState_apply_continuous wave).comp
            ((wholeRestartBoundedPreAccumulationVelocityTrajectory_continuous
              initial elapsedBounded).comp toPreContinuous)
        apply preContinuous.congr
        intro point
        exact congrArg (fun state => state wave)
          (sourceGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice_of_lt
            initial elapsedBounded point.1 point.2).symm
      have continuousOnBefore :
          ContinuousOn
            (fun point :
                Icc (0 : ℝ)
                  (wholeRestartVelocityAccumulationTime initial + 1) =>
              sourceGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice
                initial elapsedBounded point wave)
            beforeSet := by
        rwa [continuousOn_iff_continuous_restrict]
      have beforeOpen : IsOpen beforeSet := by
        exact isOpen_lt continuous_subtype_val continuous_const
      exact continuousOnBefore.continuousAt
        (beforeOpen.mem_nhds before)
    · have after :
          wholeRestartVelocityAccumulationTime initial < time.1 := by
        have timeNe :
            time.1 ≠ wholeRestartVelocityAccumulationTime initial := by
          intro valueEq
          apply atStart
          apply Subtype.ext
          exact valueEq
        exact lt_of_le_of_ne (le_of_not_gt before) timeNe.symm
      let afterSet :
          Set
            (Icc (0 : ℝ)
              (wholeRestartVelocityAccumulationTime initial + 1)) :=
        {point | wholeRestartVelocityAccumulationTime initial < point.1}
      let toPost :
          afterSet →
            Icc (wholeRestartVelocityAccumulationTime initial)
              (wholeRestartVelocityAccumulationTime initial + 1) :=
        fun point => ⟨point.1.1, point.2.le, point.1.2.2⟩
      have toPostContinuous : Continuous toPost := by
        apply Continuous.subtype_mk
        exact continuous_subtype_val.comp continuous_subtype_val
      let continuation :=
        sourceGeneratedWholeRestartVelocityEndpointAbsoluteWholeMildNativeContinuation
          initial elapsedBounded
      have postContinuous :
          Continuous fun postTime :
              Icc (wholeRestartVelocityAccumulationTime initial)
                (wholeRestartVelocityAccumulationTime initial + 1) =>
            sourceGeneratedWholeRestartVelocityEndpointAbsolutePhysicalPath
              initial elapsedBounded postTime wave := by
        change Continuous fun postTime =>
          euclideanCoordinateRow
            (sourceGeneratedWholeRestartVelocityEndpointAbsoluteWholePath
              initial elapsedBounded postTime wave.1)
        exact
          (PiLp.continuous_toLp
            (2 : ENNReal) (fun _ : Coordinate => ℂ)).comp
            (continuation.absolutePath_coordinate_continuous wave.1)
      have restrictedContinuous :
          Continuous fun point : afterSet =>
            sourceGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice
              initial elapsedBounded point.1 wave := by
        have composed := postContinuous.comp toPostContinuous
        apply composed.congr
        intro point
        exact congrArg (fun state => state wave)
          (sourceGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice_of_ge
            initial elapsedBounded point.1 point.2.le).symm
      have continuousOnAfter :
          ContinuousOn
            (fun point :
                Icc (0 : ℝ)
                  (wholeRestartVelocityAccumulationTime initial + 1) =>
              sourceGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice
                initial elapsedBounded point wave)
            afterSet := by
        rwa [continuousOn_iff_continuous_restrict]
      have afterOpen : IsOpen afterSet := by
        exact isOpen_lt continuous_const continuous_subtype_val
      exact continuousOnAfter.continuousAt
        (afterOpen.mem_nhds after)

namespace GeneratedWholeRestartEndpointMacroStep

variable {nu : Viscosity}

/-- Total real-line extension of the canonical physical stage.  Projection
only extends the source-selected chart; it does not choose a cutoff. -/
def physicalStageTrajectory
    {current next : GeneratedWholeRestartCurrent nu}
    (step : GeneratedWholeRestartEndpointMacroStep nu current next) :
    ℝ → WholeRestartVelocityEndpointState :=
  fun time =>
    step.physicalStage
      (projIcc 0 step.clockAdvance
        step.clockAdvance_pos.le time)

theorem physicalStageTrajectory_eq_stage
    {current next : GeneratedWholeRestartCurrent nu}
    (step : GeneratedWholeRestartEndpointMacroStep nu current next)
    (time : Icc (0 : ℝ) step.clockAdvance) :
    step.physicalStageTrajectory time.1 = step.physicalStage time := by
  rw [physicalStageTrajectory,
    projIcc_of_mem step.clockAdvance_pos.le time.2]

/-- One exact truncated macro chart is continuous in every physical Fourier
row, including its source-generated accumulation interface. -/
theorem physicalStage_coordinate_continuous
    {current next : GeneratedWholeRestartCurrent nu}
    (step : GeneratedWholeRestartEndpointMacroStep nu current next)
    (wave : NonzeroIntegerWavevector) :
    Continuous fun time : Icc (0 : ℝ) step.clockAdvance =>
      step.physicalStage time wave := by
  exact
    (sourceGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice_coordinate_continuous
      current step.elapsedBounded wave).comp
        step.physicalStageTime_continuous

/-- The real-line extension of the same chart remains coordinatewise
continuous. -/
theorem physicalStageTrajectory_coordinate_continuous
    {current next : GeneratedWholeRestartCurrent nu}
    (step : GeneratedWholeRestartEndpointMacroStep nu current next)
    (wave : NonzeroIntegerWavevector) :
    Continuous fun time : ℝ =>
      step.physicalStageTrajectory time wave := by
  exact
    (step.physicalStage_coordinate_continuous wave).comp
        (continuous_projIcc
          (a := (0 : ℝ)) (b := step.clockAdvance)
          (h := step.clockAdvance_pos.le))

end GeneratedWholeRestartEndpointMacroStep

namespace GeneratedInfiniteWholeRestartEndpointMacroLineage

variable {nu : Viscosity}

@[simp] theorem macroClock_zero
    (lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage nu) :
    lineage.macroClock 0 = 0 := by
  simp [macroClock]

@[simp] theorem macroClock_succ
    (lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage nu)
    (length : ℕ) :
    lineage.macroClock (length + 1) =
      lineage.macroClock length + (lineage.step length).clockAdvance := by
  simp [macroClock, Finset.sum_range_succ]

theorem macroClock_nonneg
    (lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage nu)
    (length : ℕ) :
    0 ≤ lineage.macroClock length := by
  exact le_trans (by positivity : (0 : ℝ) ≤ (length : ℝ) / 2)
    (lineage.half_length_le_macroClock length)

theorem macroClock_strictMono
    (lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage nu) :
    StrictMono lineage.macroClock := by
  apply strictMono_nat_of_lt_succ
  intro length
  rw [macroClock_succ]
  exact lt_add_of_pos_right _ (by
    linarith [(lineage.step length).half_lt_clockAdvance])

theorem step_clockAdvance_nonneg
    (lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage nu)
    (index : ℕ) :
    0 ≤ (lineage.step index).clockAdvance := by
  linarith [(lineage.step index).half_lt_clockAdvance]

/-- Adjacent generated macro charts meet at one literal physical state. -/
theorem physicalStage_adjacent
    (lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage nu)
    (index : ℕ) :
    (lineage.step index).physicalStage
        (lineage.step index).physicalStageTerminal =
      (lineage.step (index + 1)).physicalStage
        (lineage.step (index + 1)).physicalStageZero := by
  rw [(lineage.step index).physicalStage_terminal,
    (lineage.step (index + 1)).physicalStage_zero]

private theorem endpointSplice_coordinate_continuous
    {E : Type*}
    [TopologicalSpace E]
    (joinTime : ℝ)
    (prior restart : ℝ → E)
    (priorContinuous : Continuous prior)
    (restartContinuous : Continuous restart)
    (sameValue : restart 0 = prior joinTime) :
    Continuous (endpointSplice joinTime prior restart) := by
  unfold endpointSplice
  apply Continuous.if
  · intro time frontierMem
    change time ∈ frontier (Iic joinTime) at frontierMem
    rw [frontier_Iic] at frontierMem
    have timeEq : time = joinTime := by
      simpa using frontierMem
    subst time
    simp [sameValue]
  · exact priorContinuous
  · exact restartContinuous.comp
      (continuous_id.sub continuous_const)

/-! ## Finite direct system of exact macro charts -/

/-- Join the first `length` source-generated endpoint macro charts on their
actual accumulated macro clock. -/
def finiteMacroAbsoluteVelocityTrajectory
    (lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage nu) :
    ℕ → ℝ → WholeRestartVelocityEndpointState
  | 0 => fun _ =>
      puncturedWholeVelocityEuclideanState
        (lineage.current 0).initialState
  | length + 1 =>
      endpointSplice
        (lineage.macroClock length)
        (finiteMacroAbsoluteVelocityTrajectory lineage length)
        (lineage.step length).physicalStageTrajectory

/-- Every finite macro prefix reaches the literal initial state of its
current endpoint. -/
theorem finiteMacroAbsoluteVelocityTrajectory_endpoint
    (lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage nu) :
    ∀ length : ℕ,
      lineage.finiteMacroAbsoluteVelocityTrajectory length
          (lineage.macroClock length) =
        puncturedWholeVelocityEuclideanState
          (lineage.current length).initialState
  | 0 => by simp [finiteMacroAbsoluteVelocityTrajectory]
  | length + 1 => by
      have joinLt :
          lineage.macroClock length <
            lineage.macroClock (length + 1) :=
        lineage.macroClock_strictMono (Nat.lt_succ_self length)
      rw [finiteMacroAbsoluteVelocityTrajectory,
        endpointSplice_of_lt _ _ _ _ joinLt,
        macroClock_succ]
      have localTime :
          lineage.macroClock length +
                (lineage.step length).clockAdvance -
              lineage.macroClock length =
            (lineage.step length).clockAdvance := by
        ring
      rw [localTime]
      calc
        (lineage.step length).physicalStageTrajectory
              (lineage.step length).clockAdvance =
            (lineage.step length).physicalStage
              (lineage.step length).physicalStageTerminal := by
          simpa [GeneratedWholeRestartEndpointMacroStep.physicalStageTerminal]
            using
              (lineage.step length).physicalStageTrajectory_eq_stage
                (lineage.step length).physicalStageTerminal
        _ = puncturedWholeVelocityEuclideanState
              (lineage.current (length + 1)).initialState :=
          (lineage.step length).physicalStage_terminal

/-- Adding one generated macro chart does not alter the prefix already
written before its join clock. -/
theorem finiteMacroAbsoluteVelocityTrajectory_succ_eq_of_le
    (lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage nu)
    (length : ℕ)
    {time : ℝ}
    (timeLe : time ≤ lineage.macroClock length) :
    lineage.finiteMacroAbsoluteVelocityTrajectory (length + 1) time =
      lineage.finiteMacroAbsoluteVelocityTrajectory length time := by
  rw [finiteMacroAbsoluteVelocityTrajectory]
  exact endpointSplice_of_le _ _ _ _ timeLe

/-- The finite macro paths form a nested literal direct system. -/
theorem finiteMacroAbsoluteVelocityTrajectory_eq_of_le
    (lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage nu)
    {shorter longer : ℕ}
    (indexLe : shorter ≤ longer)
    {time : ℝ}
    (timeLe : time ≤ lineage.macroClock shorter) :
    lineage.finiteMacroAbsoluteVelocityTrajectory longer time =
      lineage.finiteMacroAbsoluteVelocityTrajectory shorter time := by
  induction longer generalizing shorter with
  | zero =>
      have shorterEq : shorter = 0 := by omega
      subst shorter
      rfl
  | succ longer inductionHypothesis =>
      by_cases shorterEq : shorter = longer + 1
      · subst shorter
        rfl
      · have shorterLe : shorter ≤ longer := by omega
        calc
          lineage.finiteMacroAbsoluteVelocityTrajectory
                (longer + 1) time =
              lineage.finiteMacroAbsoluteVelocityTrajectory longer time :=
            lineage.finiteMacroAbsoluteVelocityTrajectory_succ_eq_of_le
              longer
              (timeLe.trans
                (lineage.macroClock_strictMono.monotone shorterLe))
          _ = lineage.finiteMacroAbsoluteVelocityTrajectory shorter time :=
            inductionHypothesis shorterLe timeLe

/-- Every generated local stage remains literally visible in each longer
finite prefix, including both adjacent endpoints. -/
theorem finiteMacroAbsoluteVelocityTrajectory_eq_stage
    (lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage nu)
    {length index : ℕ}
    (indexLt : index < length)
    (localTime : Icc (0 : ℝ) (lineage.step index).clockAdvance) :
    lineage.finiteMacroAbsoluteVelocityTrajectory length
        (lineage.macroClock index + localTime.1) =
      (lineage.step index).physicalStage localTime := by
  have globalTimeLe :
      lineage.macroClock index + localTime.1 ≤
        lineage.macroClock (index + 1) := by
    rw [macroClock_succ]
    linarith [localTime.2.2]
  calc
    lineage.finiteMacroAbsoluteVelocityTrajectory length
          (lineage.macroClock index + localTime.1) =
        lineage.finiteMacroAbsoluteVelocityTrajectory (index + 1)
          (lineage.macroClock index + localTime.1) :=
      lineage.finiteMacroAbsoluteVelocityTrajectory_eq_of_le
        (Nat.succ_le_of_lt indexLt) globalTimeLe
    _ = (lineage.step index).physicalStage localTime := by
      rcases eq_or_lt_of_le localTime.2.1 with localZero | localPos
      · have localTimeEq :
            localTime = (lineage.step index).physicalStageZero := by
          apply Subtype.ext
          exact localZero.symm
        rw [localTimeEq]
        change
          lineage.finiteMacroAbsoluteVelocityTrajectory (index + 1)
              (lineage.macroClock index + 0) =
            (lineage.step index).physicalStage
              (lineage.step index).physicalStageZero
        rw [add_zero, finiteMacroAbsoluteVelocityTrajectory,
          endpointSplice_of_le _ _ _ _ le_rfl,
          lineage.finiteMacroAbsoluteVelocityTrajectory_endpoint index,
          (lineage.step index).physicalStage_zero]
      · rw [finiteMacroAbsoluteVelocityTrajectory,
          endpointSplice_of_lt _ _ _ _ (lt_add_of_pos_right _ localPos)]
        have shifted :
            lineage.macroClock index + localTime.1 -
                lineage.macroClock index = localTime.1 := by
          ring
        rw [shifted,
          (lineage.step index).physicalStageTrajectory_eq_stage]

/-- Every finite macro prefix is globally continuous in each complete
physical Fourier row.  The possible kinetic defect lives only in the
simultaneous whole-`L²` tail, not in any fixed row or macro join. -/
theorem finiteMacroAbsoluteVelocityTrajectory_coordinate_continuous
    (lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage nu)
    (wave : NonzeroIntegerWavevector) :
    ∀ length : ℕ,
      Continuous fun time =>
        lineage.finiteMacroAbsoluteVelocityTrajectory length time wave
  | 0 => by
      change Continuous
        (fun _ : ℝ =>
          (puncturedWholeVelocityEuclideanState
            (lineage.current 0).initialState) wave)
      exact continuous_const
  | length + 1 => by
      have sameValue :
          (lineage.step length).physicalStageTrajectory 0 wave =
            lineage.finiteMacroAbsoluteVelocityTrajectory length
              (lineage.macroClock length) wave := by
        calc
          (lineage.step length).physicalStageTrajectory 0 wave =
              (lineage.step length).physicalStage
                  (lineage.step length).physicalStageZero wave := by
            simpa [GeneratedWholeRestartEndpointMacroStep.physicalStageZero]
              using congrArg (fun state => state wave)
                ((lineage.step length).physicalStageTrajectory_eq_stage
                  (lineage.step length).physicalStageZero)
          _ = lineage.finiteMacroAbsoluteVelocityTrajectory length
                (lineage.macroClock length) wave := by
            rw [(lineage.step length).physicalStage_zero,
              lineage.finiteMacroAbsoluteVelocityTrajectory_endpoint length]
      have joined :=
        endpointSplice_coordinate_continuous
          (lineage.macroClock length)
          (fun time =>
            lineage.finiteMacroAbsoluteVelocityTrajectory length time wave)
          (fun time =>
            (lineage.step length).physicalStageTrajectory time wave)
          (lineage.finiteMacroAbsoluteVelocityTrajectory_coordinate_continuous
            wave length)
          ((lineage.step length).physicalStageTrajectory_coordinate_continuous
            wave)
          sameValue
      change Continuous
        (fun time =>
          (endpointSplice
            (lineage.macroClock length)
            (lineage.finiteMacroAbsoluteVelocityTrajectory length)
            (lineage.step length).physicalStageTrajectory time) wave)
      apply Continuous.congr joined
      intro time
      by_cases timeLe : time ≤ lineage.macroClock length
      · simp [endpointSplice, timeLe]
      · simp [endpointSplice, timeLe]

/-! ## Stabilized global absolute velocity -/

/-- The unbounded generated macro clock covers every real time. -/
theorem macroClock_cofinal
    (lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage nu)
    (time : ℝ) :
    ∃ length : ℕ, time < lineage.macroClock length := by
  obtain ⟨value, ⟨length, rfl⟩, timeLt⟩ :=
    not_bddAbove_iff.mp lineage.macroClock_not_bddAbove time
  exact ⟨length, timeLt⟩

/-- A generated finite macro prefix ending strictly after the requested
absolute time. -/
def globalAbsoluteVelocityCoverIndex
    (lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage nu)
    (time : ℝ) : ℕ :=
  Classical.choose (lineage.macroClock_cofinal time)

theorem globalAbsoluteVelocityCoverIndex_spec
    (lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage nu)
    (time : ℝ) :
    time < lineage.macroClock
      (lineage.globalAbsoluteVelocityCoverIndex time) :=
  Classical.choose_spec (lineage.macroClock_cofinal time)

/-- The unique stabilized value of the finite source-generated macro
prefixes. -/
def globalAbsoluteVelocityTrajectory
    (lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage nu)
    (time : ℝ) : WholeRestartVelocityEndpointState :=
  lineage.finiteMacroAbsoluteVelocityTrajectory
    (lineage.globalAbsoluteVelocityCoverIndex time) time

/-- On every completed finite macro interval, the global path is literally
the already generated finite prefix. -/
theorem globalAbsoluteVelocityTrajectory_eq_prefix
    (lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage nu)
    (length : ℕ)
    {time : ℝ}
    (timeLe : time ≤ lineage.macroClock length) :
    lineage.globalAbsoluteVelocityTrajectory time =
      lineage.finiteMacroAbsoluteVelocityTrajectory length time := by
  let cover := lineage.globalAbsoluteVelocityCoverIndex time
  let upper := max cover length
  have timeLeCover : time ≤ lineage.macroClock cover :=
    (lineage.globalAbsoluteVelocityCoverIndex_spec time).le
  calc
    lineage.globalAbsoluteVelocityTrajectory time =
        lineage.finiteMacroAbsoluteVelocityTrajectory cover time := rfl
    _ = lineage.finiteMacroAbsoluteVelocityTrajectory upper time :=
      (lineage.finiteMacroAbsoluteVelocityTrajectory_eq_of_le
        (Nat.le_max_left cover length) timeLeCover).symm
    _ = lineage.finiteMacroAbsoluteVelocityTrajectory length time :=
      lineage.finiteMacroAbsoluteVelocityTrajectory_eq_of_le
        (Nat.le_max_right cover length) timeLe

/-- Every exact source-selected macro chart remains a literal chart of the
single stabilized global path. -/
theorem globalAbsoluteVelocityTrajectory_eq_stage
    (lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage nu)
    (index : ℕ)
    (localTime : Icc (0 : ℝ) (lineage.step index).clockAdvance) :
    lineage.globalAbsoluteVelocityTrajectory
        (lineage.macroClock index + localTime.1) =
      (lineage.step index).physicalStage localTime := by
  have timeLe :
      lineage.macroClock index + localTime.1 ≤
        lineage.macroClock (index + 1) := by
    rw [macroClock_succ]
    linarith [localTime.2.2]
  rw [lineage.globalAbsoluteVelocityTrajectory_eq_prefix
    (index + 1) timeLe]
  exact
    lineage.finiteMacroAbsoluteVelocityTrajectory_eq_stage
      (Nat.lt_succ_self index) localTime

/-- Every infinite source-owned macro lineage produces one globally
continuous physical Fourier row for every nonzero wave.  Positive endpoint
atoms therefore survive only in the nonuniform whole-`L²` tail. -/
theorem globalAbsoluteVelocityTrajectory_coordinate_continuous
    (lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage nu)
    (wave : NonzeroIntegerWavevector) :
    Continuous fun time =>
      lineage.globalAbsoluteVelocityTrajectory time wave := by
  rw [continuous_iff_continuousAt]
  intro time
  obtain ⟨length, timeLt⟩ := lineage.macroClock_cofinal time
  have prefixContinuous :=
    lineage.finiteMacroAbsoluteVelocityTrajectory_coordinate_continuous
      wave length
  apply prefixContinuous.continuousAt.congr_of_eventuallyEq
  · filter_upwards [Iio_mem_nhds timeLt] with later laterLt
    exact congrArg (fun state => state wave)
      (lineage.globalAbsoluteVelocityTrajectory_eq_prefix
        length laterLt.le)

end GeneratedInfiniteWholeRestartEndpointMacroLineage

/-! ## Source-owned zero/positive exhaustion -/

/-- The exact kinetic defect attached to one generated macro stage. -/
def infiniteEndpointMacroStageKineticDefect
    {nu : Viscosity}
    (lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage nu)
    (index : ℕ) : ℝ :=
  wholeRestartKineticWeakEndpointDefect (lineage.current index)
    (generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
      (lineage.current index)
      (lineage.step index).elapsedBounded).family.endpointReceipt.kineticReceipt.endpoint

/-- The complete source-owned global absolute velocity object of the
all-zero branch.  Its finite direct system, exact stage charts and global
coordinate continuity are retained in one receipt. -/
structure GeneratedInfiniteWholeRestartEndpointMacroGlobalAbsoluteVelocity
    {nu : Viscosity}
    (lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage nu) where
  stageDefectZero :
    ∀ index : ℕ,
      infiniteEndpointMacroStageKineticDefect lineage index = 0
  physicalPath : ℝ → WholeRestartVelocityEndpointState
  path_eq : physicalPath = lineage.globalAbsoluteVelocityTrajectory
  initial_eq :
    physicalPath 0 =
      puncturedWholeVelocityEuclideanState
        (lineage.current 0).initialState
  prefix_eq :
    ∀ length : ℕ,
      Set.EqOn physicalPath
        (lineage.finiteMacroAbsoluteVelocityTrajectory length)
        (Iic (lineage.macroClock length))
  stage_chart :
    ∀ (index : ℕ)
      (localTime : Icc (0 : ℝ) (lineage.step index).clockAdvance),
      physicalPath (lineage.macroClock index + localTime.1) =
        (lineage.step index).physicalStage localTime
  coordinate_continuous :
    ∀ wave : NonzeroIntegerWavevector,
      Continuous fun time => physicalPath time wave

private noncomputable def
    generatedInfiniteWholeRestartEndpointMacroGlobalAbsoluteVelocity_of_allZero
    {nu : Viscosity}
    (lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage nu)
    (defectZero :
      ∀ index : ℕ,
        infiniteEndpointMacroStageKineticDefect lineage index = 0) :
    GeneratedInfiniteWholeRestartEndpointMacroGlobalAbsoluteVelocity lineage where
  stageDefectZero := defectZero
  physicalPath := lineage.globalAbsoluteVelocityTrajectory
  path_eq := rfl
  initial_eq := by
    rw [lineage.globalAbsoluteVelocityTrajectory_eq_prefix 0 (by simp)]
    rfl
  prefix_eq := by
    intro length time timeMem
    exact lineage.globalAbsoluteVelocityTrajectory_eq_prefix
      length timeMem
  stage_chart := lineage.globalAbsoluteVelocityTrajectory_eq_stage
  coordinate_continuous := by
    intro wave
    exact lineage.globalAbsoluteVelocityTrajectory_coordinate_continuous wave

/-- Exhaustive source disposition of an infinite macro lineage: an actual
stage exposes positive kinetic defect, or every source receipt selects its
zero branch and the global absolute velocity path is generated. -/
inductive GeneratedInfiniteWholeRestartEndpointMacroKineticDisposition
    {nu : Viscosity}
    (lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage nu) : Type
  | positive
      (index : ℕ)
      (defectPositive :
        0 < infiniteEndpointMacroStageKineticDefect lineage index)
  | allZero
      (global :
        GeneratedInfiniteWholeRestartEndpointMacroGlobalAbsoluteVelocity
          lineage)

/-- The kinetic receipts themselves exhaust the zero/positive alternatives.
No branch law or global path is supplied to this producer. -/
noncomputable def generatedInfiniteWholeRestartEndpointMacroKineticDisposition
    {nu : Viscosity}
    (lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage nu) :
    GeneratedInfiniteWholeRestartEndpointMacroKineticDisposition lineage := by
  by_cases positive :
      ∃ index : ℕ,
        0 < infiniteEndpointMacroStageKineticDefect lineage index
  · exact .positive (Classical.choose positive)
      (Classical.choose_spec positive)
  · have defectZero :
        ∀ index : ℕ,
          infiniteEndpointMacroStageKineticDefect lineage index = 0 := by
      intro index
      let ledger :=
        generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
          (lineage.current index) (lineage.step index).elapsedBounded
      rcases ledger.family.endpointReceipt.kineticReceipt.defect_disposition with
        defectPositive | zeroDisposition
      · exact False.elim <| positive ⟨index, by
          simpa only [infiniteEndpointMacroStageKineticDefect, ledger] using
            defectPositive⟩
      · simpa only [infiniteEndpointMacroStageKineticDefect, ledger] using
          zeroDisposition.1
    exact .allZero
      (generatedInfiniteWholeRestartEndpointMacroGlobalAbsoluteVelocity_of_allZero
        lineage defectZero)

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
end NavierStokes
end SaturationMonoid
