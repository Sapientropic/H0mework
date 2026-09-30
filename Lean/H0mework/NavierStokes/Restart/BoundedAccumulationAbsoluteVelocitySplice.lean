import H0mework.NavierStokes.Restart.BoundedPreAccumulationVelocityStrongTrace
import H0mework.NavierStokes.VelocityEndpoint.NativeReachableContinuation
import H0mework.NavierStokes.VelocityEndpoint.PhysicalRightTrace

/-!
# Absolute physical-velocity splice across a bounded restart accumulation

The bounded native restart lineage already owns both halves of one absolute
physical history: its stabilized velocity trajectory on `[0, T)` and the
whole mild endpoint write on `[T, T + 1]`.  This module installs those two
pieces on the same complete nonzero-wave `L²` velocity carrier and the same
absolute clock.

The splice is generated from `initial` and its bounded elapsed-time law.  Its
post-accumulation value at the source-selected time is exactly the physical
initial state of the first native current beyond `T`.  No endpoint, path,
continuation, target state, branch, or gluing equality is supplied by a
caller.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice

open Set Filter
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticWeakEndpoint
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinFamily
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinVelocityWeakLimit
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartBoundedPreAccumulationPhysicalTrajectory
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticDefectZeroAbsoluteStrongTrace
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartBoundedPreAccumulationVelocityStrongTrace
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointAbsoluteWholeMildNativeContinuation
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointPhysicalRightTrace
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointNativeReachableContinuation

noncomputable section

variable {nu : Viscosity}

private theorem wholeRestartVelocityAccumulationTime_pos
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    0 < wholeRestartVelocityAccumulationTime initial := by
  simpa using
    elapsedTime_lt_wholeRestartVelocityAccumulationTime
      initial elapsedBounded 0

/-- The source-generated whole endpoint path, read on the complete physical
nonzero-wave Euclidean velocity carrier. -/
noncomputable def
    sourceGeneratedWholeRestartVelocityEndpointAbsolutePhysicalPath
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    Icc
        (wholeRestartVelocityAccumulationTime initial)
        (wholeRestartVelocityAccumulationTime initial + 1) ->
      WholeRestartVelocityEndpointState :=
  fun time =>
    puncturedEuclideanize
      (sourceGeneratedWholeRestartVelocityEndpointAbsoluteWholePath
        initial elapsedBounded time)

/-- The absolute endpoint path starts at the exact physical velocity endpoint
selected from the old actual run. -/
theorem
    sourceGeneratedWholeRestartVelocityEndpointAbsolutePhysicalPath_initial
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    let ledger :=
      generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
        initial elapsedBounded
    sourceGeneratedWholeRestartVelocityEndpointAbsolutePhysicalPath
        initial elapsedBounded
        ⟨wholeRestartVelocityAccumulationTime initial, by
          constructor <;> linarith⟩ =
      ledger.family.endpointReceipt.velocityEndpoint := by
  dsimp only
  exact
    sourceGeneratedWholeRestartVelocityEndpoint_absoluteInitialVelocity
      initial elapsedBounded

/-- One source-owned physical velocity history on the old absolute clock.
Before `T` it is literally the stabilized old native trajectory; at and after
`T` it is literally the generated whole-mild endpoint write. -/
noncomputable def
    sourceGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    Icc
        (0 : Real)
        (wholeRestartVelocityAccumulationTime initial + 1) ->
      WholeRestartVelocityEndpointState :=
  fun time =>
    if timeBefore :
        time.1 < wholeRestartVelocityAccumulationTime initial then
      wholeRestartBoundedPreAccumulationVelocityTrajectory
        initial elapsedBounded
        ⟨time.1, time.2.1, timeBefore⟩
    else
      sourceGeneratedWholeRestartVelocityEndpointAbsolutePhysicalPath
        initial elapsedBounded
        ⟨time.1, le_of_not_gt timeBefore, time.2.2⟩

/-- Literal conservativity below the accumulation endpoint. -/
theorem
    sourceGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice_of_lt
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (time :
      Icc
        (0 : Real)
        (wholeRestartVelocityAccumulationTime initial + 1))
    (timeBefore :
      time.1 < wholeRestartVelocityAccumulationTime initial) :
    sourceGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice
        initial elapsedBounded time =
      wholeRestartBoundedPreAccumulationVelocityTrajectory
        initial elapsedBounded
        ⟨time.1, time.2.1, timeBefore⟩ := by
  simp only [
    sourceGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice,
    dif_pos timeBefore]

/-- Literal conservativity on and after the accumulation endpoint. -/
theorem
    sourceGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice_of_ge
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (time :
      Icc
        (0 : Real)
        (wholeRestartVelocityAccumulationTime initial + 1))
    (timeAfter :
      wholeRestartVelocityAccumulationTime initial <= time.1) :
    sourceGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice
        initial elapsedBounded time =
      sourceGeneratedWholeRestartVelocityEndpointAbsolutePhysicalPath
        initial elapsedBounded
        ⟨time.1, timeAfter, time.2.2⟩ := by
  unfold
    sourceGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice
  rw [dif_neg (not_lt_of_ge timeAfter)]

/-- On the complete post-accumulation half of the splice, every nonzero
physical Fourier row satisfies the exact heat--Duhamel law generated by the
same endpoint Leray--Hopf lineage.  The local endpoint time is computed from
the absolute clock; it is not supplied by the caller. -/
theorem
    sourceGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice_row_mildIdentity_of_ge
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (time :
      Icc
        (0 : Real)
        (wholeRestartVelocityAccumulationTime initial + 1))
    (timeAfter :
      wholeRestartVelocityAccumulationTime initial <= time.1)
    (wave :
      ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger.NonzeroIntegerWavevector)
    (coordinate : Coordinate) :
    let ledger :=
      generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
        initial elapsedBounded
    let endpoint :=
      sourceGeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt
        initial elapsedBounded
    sourceGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice
          initial elapsedBounded time wave coordinate =
      ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteMildDuhamel.fixedWaveHeatDuhamelValue
          1 nu.coeff wave.1
          (wholeRestartVelocityEndpointCoefficient
            ledger.family.endpointReceipt.velocityEndpoint wave.1)
          (wholeVelocityLerayProjectionSpaceTime wave.1
            (endpoint.core.nonlinearLimit wave.1))
          (endpointAbsoluteToLocalTime
            (wholeRestartVelocityAccumulationTime initial)
            ⟨time.1, timeAfter, time.2.2⟩)
        coordinate := by
  dsimp only
  rw [
    sourceGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice_of_ge
      initial elapsedBounded time timeAfter]
  change
    sourceGeneratedWholeRestartVelocityEndpointAbsoluteWholePath
          initial elapsedBounded ⟨time.1, timeAfter, time.2.2⟩ wave.1
          coordinate = _
  exact congrFun
    ((sourceGeneratedWholeRestartVelocityEndpointAbsoluteWholeMildNativeContinuation
        initial elapsedBounded).absolutePath_row_mild_identity
      wave.1 wave.2 ⟨time.1, timeAfter, time.2.2⟩)
    coordinate

/-- The accumulation boundary as a point of the complete absolute splice
domain. -/
def wholeRestartBoundedAccumulationAbsoluteVelocitySpliceStart
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    Icc
        (0 : Real)
        (wholeRestartVelocityAccumulationTime initial + 1) :=
  ⟨wholeRestartVelocityAccumulationTime initial,
    (wholeRestartVelocityAccumulationTime_pos
      initial elapsedBounded).le,
    by linarith⟩

/-- At the actual boundary the splice writes the exact endpoint state; there
is no independently selected gluing value. -/
theorem
    sourceGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice_start
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    let ledger :=
      generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
        initial elapsedBounded
    sourceGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice
        initial elapsedBounded
        (wholeRestartBoundedAccumulationAbsoluteVelocitySpliceStart
          initial elapsedBounded) =
      ledger.family.endpointReceipt.velocityEndpoint := by
  dsimp only
  rw [
    sourceGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice_of_ge
      initial elapsedBounded _ le_rfl]
  exact
    sourceGeneratedWholeRestartVelocityEndpointAbsolutePhysicalPath_initial
      initial elapsedBounded

/-- In the zero kinetic-defect branch, the complete old physical trajectory
converges strongly to the literal boundary value written by the absolute
splice.  This is the whole-`L²` left gluing law, not a selected-subsequence or
finite-mode readout. -/
theorem
    sourceGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice_leftTendsto_start_of_kineticDefect_eq_zero
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (defectZero :
      wholeRestartKineticWeakEndpointDefect initial
        (generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
          initial elapsedBounded).family.endpointReceipt.kineticReceipt.endpoint =
        0) :
    Tendsto
      (fun time :
          Ico (0 : Real) (wholeRestartVelocityAccumulationTime initial) =>
        sourceGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice
          initial elapsedBounded
          ⟨time.1, time.2.1, by linarith [time.2.2]⟩)
      atTop
      (nhds
        (sourceGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice
          initial elapsedBounded
          (wholeRestartBoundedAccumulationAbsoluteVelocitySpliceStart
            initial elapsedBounded))) := by
  let ledger :=
    generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
      initial elapsedBounded
  have oldTrace :=
    wholeRestartBoundedPreAccumulationVelocityTrajectory_tendsto_endpoint_of_kineticDefect_eq_zero
      initial elapsedBounded defectZero
  have preEq :
      (fun time :
          Ico (0 : Real) (wholeRestartVelocityAccumulationTime initial) =>
        sourceGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice
          initial elapsedBounded
          ⟨time.1, time.2.1, by linarith [time.2.2]⟩) =
        wholeRestartBoundedPreAccumulationVelocityTrajectory
          initial elapsedBounded := by
    funext time
    exact
      sourceGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice_of_lt
        initial elapsedBounded _ time.2.2
  rw [preEq,
    sourceGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice_start]
  simpa only [ledger] using oldTrace

/-- Hilbert-weak endpoint convergence already glues every fixed physical
Fourier coordinate from the left to the literal value written at the
accumulation boundary. -/
theorem
    sourceGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice_coordinate_leftTendsto_start
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (wave :
      ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger.NonzeroIntegerWavevector)
    (coordinate : Coordinate) :
    Tendsto
      (fun time :
          Ico (0 : Real) (wholeRestartVelocityAccumulationTime initial) =>
        sourceGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice
          initial elapsedBounded
          ⟨time.1, time.2.1, by linarith [time.2.2]⟩
          wave coordinate)
      atTop
      (nhds
        (sourceGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice
          initial elapsedBounded
          (wholeRestartBoundedAccumulationAbsoluteVelocitySpliceStart
            initial elapsedBounded)
          wave coordinate)) := by
  let ledger :=
    generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
      initial elapsedBounded
  have oldTrace :=
    wholeRestartBoundedPreAccumulationVelocityTrajectory_coordinate_tendsto_endpoint
      initial elapsedBounded wave coordinate
  have preEq :
      (fun time :
          Ico (0 : Real) (wholeRestartVelocityAccumulationTime initial) =>
        sourceGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice
          initial elapsedBounded
          ⟨time.1, time.2.1, by linarith [time.2.2]⟩
          wave coordinate) =
        (fun time =>
          wholeRestartBoundedPreAccumulationVelocityTrajectory
            initial elapsedBounded time wave coordinate) := by
    funext time
    exact congrArg (fun state => state wave coordinate)
      (sourceGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice_of_lt
        initial elapsedBounded
        ⟨time.1, time.2.1, by linarith [time.2.2]⟩ time.2.2)
  rw [preEq,
    sourceGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice_start]
  simpa only [ledger] using oldTrace

/-- Every fixed physical Fourier coordinate is continuous through the
actual accumulation splice without assuming the kinetic defect vanishes.
Only the simultaneous whole-`L²` tail remains obstructed by that defect. -/
theorem
    sourceGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice_coordinate_continuousAt_start
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (wave :
      ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger.NonzeroIntegerWavevector)
    (coordinate : Coordinate) :
    ContinuousAt
      (fun time =>
        sourceGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice
          initial elapsedBounded time wave coordinate)
      (wholeRestartBoundedAccumulationAbsoluteVelocitySpliceStart
        initial elapsedBounded) := by
  rw [continuousAt_iff_continuous_left_right]
  constructor
  · rw [Metric.continuousWithinAt_iff]
    intro epsilon epsilonPos
    letI :
        Nonempty
          (Ico (0 : Real) (wholeRestartVelocityAccumulationTime initial)) :=
      ⟨⟨0, le_rfl, by
        simpa using
          elapsedTime_lt_wholeRestartVelocityAccumulationTime
            initial elapsedBounded 0⟩⟩
    obtain ⟨anchor, anchorClose⟩ :=
      (Metric.tendsto_atTop.mp
        (sourceGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice_coordinate_leftTendsto_start
          initial elapsedBounded wave coordinate)) epsilon epsilonPos
    let delta :=
      wholeRestartVelocityAccumulationTime initial - anchor.1
    have deltaPos : 0 < delta := by
      exact sub_pos.mpr anchor.2.2
    refine ⟨delta, deltaPos, ?_⟩
    intro time timeLe distanceLt
    have timeValueLe :
        time.1 <= wholeRestartVelocityAccumulationTime initial := by
      exact timeLe
    rcases lt_or_eq_of_le timeValueLe with timeBefore | timeAt
    · let preTime :
          Ico (0 : Real) (wholeRestartVelocityAccumulationTime initial) :=
        ⟨time.1, time.2.1, timeBefore⟩
      have anchorLe : anchor <= preTime := by
        apply Subtype.coe_le_coe.mp
        change anchor.1 <= time.1
        change
          |time.1 - wholeRestartVelocityAccumulationTime initial| <
            wholeRestartVelocityAccumulationTime initial - anchor.1 at distanceLt
        rw [abs_of_nonpos (sub_nonpos.mpr timeValueLe)] at distanceLt
        linarith
      simpa [preTime] using anchorClose preTime anchorLe
    · have timeEq :
          time =
            wholeRestartBoundedAccumulationAbsoluteVelocitySpliceStart
              initial elapsedBounded := by
        apply Subtype.ext
        exact timeAt
      subst time
      simpa only [dist_self] using epsilonPos
  · let start :=
      wholeRestartBoundedAccumulationAbsoluteVelocitySpliceStart
        initial elapsedBounded
    have startMem : start ∈ Ici start := by
      show start <= start
      exact le_rfl
    rw [continuousWithinAt_iff_continuousAt_restrict _ startMem]
    let toLocal :
        ↑(Ici start) -> Icc (0 : Real) 1 :=
      fun time =>
        ⟨time.1.1 - wholeRestartVelocityAccumulationTime initial, by
          have lower :
              wholeRestartVelocityAccumulationTime initial <= time.1.1 := by
            exact time.2
          constructor
          · linarith
          · linarith [time.1.2.2]⟩
    have toLocalContinuous : Continuous toLocal := by
      apply Continuous.subtype_mk
      exact
        (continuous_subtype_val.comp continuous_subtype_val).sub
          continuous_const
    have toLocalStart :
        toLocal ⟨start, startMem⟩ =
          (⟨0, by norm_num⟩ : Icc (0 : Real) 1) := by
      apply Subtype.ext
      simp [toLocal, start,
        wholeRestartBoundedAccumulationAbsoluteVelocitySpliceStart]
    have toLocalTendsto :
        Tendsto toLocal (nhds ⟨start, startMem⟩)
          (nhds (⟨0, by norm_num⟩ : Icc (0 : Real) 1)) := by
      rw [← toLocalStart]
      exact toLocalContinuous.continuousAt
    have rightTrace :=
      velocityEndpointWholeMildReadWrite_physical_tendsto_initial
        (sourceGeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt
          initial elapsedBounded)
    have composed := rightTrace.comp toLocalTendsto
    have coordinateEvaluationContinuous :
        Continuous
          (fun state : WholeRestartVelocityEndpointState =>
            state wave coordinate) := by
      apply LipschitzWith.continuous (K := 1)
      rw [lipschitzWith_iff_dist_le_mul]
      intro left right
      simp only [NNReal.coe_one, one_mul, dist_eq_norm]
      calc
        ‖left wave coordinate - right wave coordinate‖ <=
            ‖left wave - right wave‖ :=
          PiLp.norm_apply_le (left wave - right wave) coordinate
        _ <= ‖left - right‖ := by
          simpa only [Pi.sub_apply, lp.coeFn_sub] using
            lp.norm_apply_le_norm (by norm_num) (left - right) wave
    have evaluated :=
      (coordinateEvaluationContinuous.tendsto
        (generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
          initial elapsedBounded).family.endpointReceipt.velocityEndpoint).comp
        composed
    change
      Tendsto
        ((Ici start).restrict
          (fun time =>
            sourceGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice
              initial elapsedBounded time wave coordinate))
        (nhds ⟨start, startMem⟩)
        (nhds
          (sourceGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice
            initial elapsedBounded start wave coordinate))
    convert evaluated using 1
    · funext time
      have timeAfter :
          wholeRestartVelocityAccumulationTime initial <= time.1.1 := by
        exact time.2
      change
        sourceGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice
            initial elapsedBounded time.1 wave coordinate = _
      rw [
        sourceGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice_of_ge
          initial elapsedBounded time.1 timeAfter]
      rfl
    · apply congrArg nhds
      exact congrArg (fun state => state wave coordinate) <|
        sourceGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice_start
          initial elapsedBounded

/-- In the zero kinetic-defect branch, the old actual trajectory and the
generated endpoint whole-mild write meet strongly on the same complete
physical velocity carrier and the same absolute clock.  The right trace is
generated by the endpoint Galerkin kinetic ceiling; no tail, continuation,
target path, or gluing equality is supplied by a caller. -/
theorem
    sourceGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice_continuousAt_start_of_kineticDefect_eq_zero
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (defectZero :
      wholeRestartKineticWeakEndpointDefect initial
        (generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
          initial elapsedBounded).family.endpointReceipt.kineticReceipt.endpoint =
        0) :
    ContinuousAt
      (sourceGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice
        initial elapsedBounded)
      (wholeRestartBoundedAccumulationAbsoluteVelocitySpliceStart
        initial elapsedBounded) := by
  rw [continuousAt_iff_continuous_left_right]
  constructor
  · rw [Metric.continuousWithinAt_iff]
    intro epsilon epsilonPos
    letI :
        Nonempty
          (Ico (0 : Real) (wholeRestartVelocityAccumulationTime initial)) :=
      ⟨⟨0, le_rfl, by
        simpa using
          elapsedTime_lt_wholeRestartVelocityAccumulationTime
            initial elapsedBounded 0⟩⟩
    obtain ⟨anchor, anchorClose⟩ :=
      (Metric.tendsto_atTop.mp
        (sourceGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice_leftTendsto_start_of_kineticDefect_eq_zero
          initial elapsedBounded defectZero)) epsilon epsilonPos
    let delta :=
      wholeRestartVelocityAccumulationTime initial - anchor.1
    have deltaPos : 0 < delta := by
      exact sub_pos.mpr anchor.2.2
    refine ⟨delta, deltaPos, ?_⟩
    intro time timeLe distanceLt
    have timeValueLe :
        time.1 <= wholeRestartVelocityAccumulationTime initial := by
      exact timeLe
    rcases lt_or_eq_of_le timeValueLe with timeBefore | timeAt
    · let preTime :
          Ico (0 : Real) (wholeRestartVelocityAccumulationTime initial) :=
        ⟨time.1, time.2.1, timeBefore⟩
      have anchorLe : anchor <= preTime := by
        apply Subtype.coe_le_coe.mp
        change anchor.1 <= time.1
        change
          |time.1 - wholeRestartVelocityAccumulationTime initial| <
            wholeRestartVelocityAccumulationTime initial - anchor.1 at distanceLt
        rw [abs_of_nonpos (sub_nonpos.mpr timeValueLe)] at distanceLt
        linarith
      simpa [preTime] using anchorClose preTime anchorLe
    · have timeEq :
          time =
            wholeRestartBoundedAccumulationAbsoluteVelocitySpliceStart
              initial elapsedBounded := by
        apply Subtype.ext
        exact timeAt
      subst time
      simpa only [dist_self] using epsilonPos
  · let start :=
      wholeRestartBoundedAccumulationAbsoluteVelocitySpliceStart
        initial elapsedBounded
    have startMem : start ∈ Ici start := by
      show start <= start
      exact le_rfl
    rw [continuousWithinAt_iff_continuousAt_restrict _ startMem]
    let toLocal :
        ↑(Ici start) -> Icc (0 : Real) 1 :=
      fun time =>
        ⟨time.1.1 - wholeRestartVelocityAccumulationTime initial, by
          have lower :
              wholeRestartVelocityAccumulationTime initial <= time.1.1 := by
            exact time.2
          constructor
          · linarith
          · linarith [time.1.2.2]⟩
    have toLocalContinuous : Continuous toLocal := by
      apply Continuous.subtype_mk
      exact
        (continuous_subtype_val.comp continuous_subtype_val).sub
          continuous_const
    have toLocalStart :
        toLocal ⟨start, startMem⟩ =
          (⟨0, by norm_num⟩ : Icc (0 : Real) 1) := by
      apply Subtype.ext
      simp [toLocal, start,
        wholeRestartBoundedAccumulationAbsoluteVelocitySpliceStart]
    have toLocalTendsto :
        Tendsto toLocal (nhds ⟨start, startMem⟩)
          (nhds (⟨0, by norm_num⟩ : Icc (0 : Real) 1)) := by
      rw [← toLocalStart]
      exact toLocalContinuous.continuousAt
    have rightTrace :=
      velocityEndpointWholeMildReadWrite_physical_tendsto_initial
        (sourceGeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt
          initial elapsedBounded)
    have composed := rightTrace.comp toLocalTendsto
    change
      Tendsto
        ((Ici start).restrict
          (sourceGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice
            initial elapsedBounded))
        (nhds ⟨start, startMem⟩)
        (nhds
          (sourceGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice
            initial elapsedBounded start))
    convert composed using 1
    · funext time
      have timeAfter :
          wholeRestartVelocityAccumulationTime initial <= time.1.1 := by
        exact time.2
      change
        sourceGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice
            initial elapsedBounded time.1 = _
      rw [
        sourceGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice_of_ge
          initial elapsedBounded time.1 timeAfter]
      rfl
    · apply congrArg nhds
      change
        sourceGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice
            initial elapsedBounded start =
          (generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
            initial elapsedBounded).family.endpointReceipt.velocityEndpoint
      simpa only [start] using
        sourceGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice_start
          initial elapsedBounded

/-- The source-selected endpoint occurrence, embedded into the complete
absolute splice domain. -/
def wholeRestartBoundedAccumulationSelectedAbsoluteTime
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    Icc
        (0 : Real)
        (wholeRestartVelocityAccumulationTime initial + 1) :=
  ⟨(sourceGeneratedWholeRestartVelocityEndpointSelectedAbsoluteTime
      initial elapsedBounded).1,
    (wholeRestartVelocityAccumulationTime_pos initial elapsedBounded).le.trans
      (sourceGeneratedWholeRestartVelocityEndpointSelectedAbsoluteTime
        initial elapsedBounded).2.1,
    (sourceGeneratedWholeRestartVelocityEndpointSelectedAbsoluteTime
      initial elapsedBounded).2.2⟩

/-- The selected splice time is genuinely beyond the old accumulation
endpoint. -/
theorem
    wholeRestartBoundedAccumulationSelectedAbsoluteTime_gt_accumulation
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    wholeRestartVelocityAccumulationTime initial <
      (wholeRestartBoundedAccumulationSelectedAbsoluteTime
        initial elapsedBounded).1 :=
  (sourceGeneratedWholeRestartVelocityEndpointAbsoluteWholeMildNativeContinuation
    initial elapsedBounded).selectedAbsoluteTime_gt_accumulation

/-- At the first time selected beyond `T`, the absolute splice is exactly the
physical initial state of the generated native `after 0` current.  This is the
same-event macro projection needed by endpoint reachability: the endpoint
whole-mild write and the native successor do not merely have compatible
labels; they agree as complete physical velocity states. -/
theorem
    sourceGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice_selected_eq_afterZeroInitial
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    sourceGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice
        initial elapsedBounded
        (wholeRestartBoundedAccumulationSelectedAbsoluteTime
          initial elapsedBounded) =
      puncturedWholeVelocityEuclideanState
        ((GeneratedWholeRestartVelocityEndpointRuntimeState.afterCurrent
          initial elapsedBounded 0).initialState) := by
  let selected :=
    sourceGeneratedWholeRestartVelocityEndpointSelectedAbsoluteTime
      initial elapsedBounded
  let continuation :=
    sourceGeneratedWholeRestartVelocityEndpointAbsoluteWholeMildNativeContinuation
      initial elapsedBounded
  rw [
    sourceGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice_of_ge
      initial elapsedBounded _ continuation.selectedAbsoluteTime_gt_accumulation.le]
  apply lp.ext
  funext wave
  ext coordinate
  change
    sourceGeneratedWholeRestartVelocityEndpointAbsoluteWholePath
          initial elapsedBounded selected wave.1 coordinate =
      biotSavartVelocityCoefficient wave.1
          ((GeneratedWholeRestartVelocityEndpointRuntimeState.afterCurrent
            initial elapsedBounded 0).initialState wave.1)
        coordinate
  rw [GeneratedWholeRestartVelocityEndpointRuntimeState.afterCurrent_zero]
  exact congrFun
    (continuation.next_initial_biotSavart_absolutePath wave.1).symm
    coordinate

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice
end NavierStokes
end SaturationMonoid
