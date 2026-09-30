import H0mework.NavierStokes.VelocityEndpoint.AbsoluteWeakTraceGlue
import H0mework.NavierStokes.VelocityEndpoint.PositiveTimeH1Reentry

/-!
# Absolute whole-mild native continuation at a bounded restart accumulation

The source-generated endpoint write is naturally parameterized by local time
`t ∈ [0, 1]`.  The old native run is parameterized by the absolute physical
clock and accumulates at `T`.  This module performs the actual time
translation `t ↦ T + t`, without allowing a caller to choose either clock,
the endpoint path, or the next current.

On the translated interval `[T, T + 1]` the canonical whole path retains its
coordinate continuity and exact unforced mild identity.  Its initial row is
the weak trace selected from the old actual prefix endpoints.  At the
source-generated positive `H¹` time, the translated path lies strictly past
`T`; its curl is literally the initial state of the next native whole-restart
current, whose own unforced receipt starts at that state.

Thus a bounded old write-chain now generates a genuine positive-time
whole-flow write on the far side of its accumulation time.  The result does
not by itself assert that the old recursively generated elapsed-time range
has already been reindexed to include this new absolute interval.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointAbsoluteWholeMildNativeContinuation

open Set Filter
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteMildDuhamel
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartFinitePrefixDualSquareLedger
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint.GeneratedWholeRestartVelocityWeakEndpointAtAccumulation
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinFamily
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinVelocityWeakLimit
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointAbsoluteWeakTraceGlue
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointPositiveTimeH1Reentry

noncomputable section

/-! ## Canonical translation of the endpoint clock -/

/-- Translate a local endpoint time to the absolute interval beginning at
the old native run's accumulation time. -/
def endpointLocalToAbsoluteTime
    (accumulationTime : ℝ)
    (time : Icc (0 : ℝ) 1) :
    Icc accumulationTime (accumulationTime + 1) :=
  ⟨accumulationTime + time.1, by
    constructor <;> linarith [time.2.1, time.2.2]⟩

/-- Recover local endpoint time from its generated absolute clock. -/
def endpointAbsoluteToLocalTime
    (accumulationTime : ℝ)
    (time : Icc accumulationTime (accumulationTime + 1)) :
    Icc (0 : ℝ) 1 :=
  ⟨time.1 - accumulationTime, by
    constructor <;> linarith [time.2.1, time.2.2]⟩

@[simp] theorem endpointLocalToAbsoluteTime_value
    (accumulationTime : ℝ)
    (time : Icc (0 : ℝ) 1) :
    (endpointLocalToAbsoluteTime accumulationTime time).1 =
      accumulationTime + time.1 :=
  rfl

@[simp] theorem endpointAbsoluteToLocalTime_value
    (accumulationTime : ℝ)
    (time : Icc accumulationTime (accumulationTime + 1)) :
    (endpointAbsoluteToLocalTime accumulationTime time).1 =
      time.1 - accumulationTime :=
  rfl

@[simp] theorem endpointAbsoluteToLocalTime_localToAbsolute
    (accumulationTime : ℝ)
    (time : Icc (0 : ℝ) 1) :
    endpointAbsoluteToLocalTime accumulationTime
        (endpointLocalToAbsoluteTime accumulationTime time) =
      time := by
  ext
  simp

@[simp] theorem endpointLocalToAbsoluteTime_absoluteToLocal
    (accumulationTime : ℝ)
    (time : Icc accumulationTime (accumulationTime + 1)) :
    endpointLocalToAbsoluteTime accumulationTime
        (endpointAbsoluteToLocalTime accumulationTime time) =
      time := by
  ext
  simp

theorem endpointAbsoluteToLocalTime_continuous
    (accumulationTime : ℝ) :
    Continuous (endpointAbsoluteToLocalTime accumulationTime) := by
  apply Continuous.subtype_mk
  exact continuous_subtype_val.sub continuous_const

/-! ## Source-generated translated whole write -/

/-- The original root's cofinal whole-mild write translated to the canonical
accumulation-time coordinate.  The path itself is generated before a bounded
fibre identifies that coordinate with an actual finite boundary. -/
noncomputable def sourceGeneratedNativeTemporalAbsoluteWholePath
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    Icc
        (wholeRestartVelocityAccumulationTime initial)
        (wholeRestartVelocityAccumulationTime initial + 1) →
      ComplexVorticityHilbertState :=
  fun time =>
    (sourceGeneratedNativeTemporalWholeMildReadWriteReceipt initial).wholePath
      (endpointAbsoluteToLocalTime
        (wholeRestartVelocityAccumulationTime initial) time)

/-- The canonical pointwise whole mild endpoint write, now placed on the
old run's absolute physical clock. -/
noncomputable def
    sourceGeneratedWholeRestartVelocityEndpointAbsoluteWholePath
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    Icc
        (wholeRestartVelocityAccumulationTime initial)
        (wholeRestartVelocityAccumulationTime initial + 1) →
      ComplexVorticityHilbertState :=
  fun time =>
    (sourceGeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt
      initial elapsedBounded).wholePath
        (endpointAbsoluteToLocalTime
          (wholeRestartVelocityAccumulationTime initial) time)

/-- The generated positive `H¹` occurrence on the endpoint path, translated
to its literal absolute physical time. -/
noncomputable def
    sourceGeneratedWholeRestartVelocityEndpointSelectedAbsoluteTime
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    Icc
        (wholeRestartVelocityAccumulationTime initial)
        (wholeRestartVelocityAccumulationTime initial + 1) :=
  endpointLocalToAbsoluteTime
    (wholeRestartVelocityAccumulationTime initial)
    (sourceGeneratedWholeRestartVelocityEndpointPositiveTimeH1Slice
      initial elapsedBounded).time

/-- Absolute clock of the positive `H¹` occurrence selected by the original
cofinal root write. -/
noncomputable def sourceGeneratedNativeTemporalSelectedAbsoluteTime
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    Icc
        (wholeRestartVelocityAccumulationTime initial)
        (wholeRestartVelocityAccumulationTime initial + 1) :=
  endpointLocalToAbsoluteTime
    (wholeRestartVelocityAccumulationTime initial)
    (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time

/-! ## No-free-parameter continuation receipt -/

/-- The complete same-event endpoint continuation contract.  It binds the
old absolute prefix trace, the translated unforced whole-mild write, the
strictly post-accumulation `H¹` occurrence, and the next native current.
Every object is generated from `initial` and its bounded elapsed-time law. -/
structure
    GeneratedWholeRestartVelocityEndpointAbsoluteWholeMildNativeContinuation
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) where
  prefixEndpointTime_tendsto :
    let weak :=
      (generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
        initial elapsedBounded).family.endpointReceipt
    Tendsto
      (fun index => elapsedTime initial (weak.subsequence index + 1))
      atTop
      (nhds (wholeRestartVelocityAccumulationTime initial))
  prefixVelocity_weak_tendsto :
    let weak :=
      (generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
        initial elapsedBounded).family.endpointReceipt
    ∀ test : WholeRestartVelocityEndpointState,
      Tendsto
        (fun index =>
          inner ℂ
            (puncturedWholeVelocityEuclideanState
              (wholeRestartPrefixPhysicalTrajectory initial
                (weak.subsequence index + 1)
                (elapsedTime initial (weak.subsequence index + 1))))
            test)
        atTop
        (nhds (inner ℂ weak.velocityEndpoint test))
  absolutePath_initial_row :
    let weak :=
      (generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
        initial elapsedBounded).family.endpointReceipt
    ∀ output : IntegerWavevector,
      sourceGeneratedWholeRestartVelocityEndpointAbsoluteWholePath
          initial elapsedBounded
          ⟨wholeRestartVelocityAccumulationTime initial, by
            constructor <;> linarith⟩
          output =
        wholeRestartVelocityEndpointCoefficient
          weak.velocityEndpoint output
  absolutePath_coordinate_continuous :
    ∀ output : IntegerWavevector,
      Continuous fun time =>
        sourceGeneratedWholeRestartVelocityEndpointAbsoluteWholePath
          initial elapsedBounded time output
  absolutePath_row_mild_identity :
    let ledger :=
      generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
        initial elapsedBounded
    let endpoint :=
      generatedWholeRestartVelocityEndpointWholeMildReadWriteReceipt
        ledger.toCore
    ∀ (output : IntegerWavevector), output ≠ 0 →
      ∀ time :
        Icc
          (wholeRestartVelocityAccumulationTime initial)
          (wholeRestartVelocityAccumulationTime initial + 1),
        sourceGeneratedWholeRestartVelocityEndpointAbsoluteWholePath
            initial elapsedBounded time output =
          fixedWaveHeatDuhamelValue 1 nu.coeff output
            (wholeRestartVelocityEndpointCoefficient
              ledger.family.endpointReceipt.velocityEndpoint output)
            (wholeVelocityLerayProjectionSpaceTime output
              (endpoint.core.nonlinearLimit output))
            (endpointAbsoluteToLocalTime
              (wholeRestartVelocityAccumulationTime initial) time)
  selectedAbsoluteTime_gt_accumulation :
    wholeRestartVelocityAccumulationTime initial <
      (sourceGeneratedWholeRestartVelocityEndpointSelectedAbsoluteTime
        initial elapsedBounded).1
  next_duration_pos :
    0 < (sourceGeneratedWholeRestartVelocityEndpointNextCurrent
      initial elapsedBounded).duration
  next_receipt_initial :
    let next :=
      sourceGeneratedWholeRestartVelocityEndpointNextCurrent
        initial elapsedBounded
    next.receipt.wholePath
        ⟨0, ⟨le_rfl, next.receipt.requestedTimePos.le⟩⟩ =
      next.initialState
  next_initial_biotSavart_absolutePath :
    ∀ wave : IntegerWavevector,
      biotSavartVelocityCoefficient wave
          ((sourceGeneratedWholeRestartVelocityEndpointNextCurrent
            initial elapsedBounded).initialState wave) =
        sourceGeneratedWholeRestartVelocityEndpointAbsoluteWholePath
          initial elapsedBounded
          (sourceGeneratedWholeRestartVelocityEndpointSelectedAbsoluteTime
            initial elapsedBounded)
          wave

/-- A bounded native restart accumulation generates its absolute whole-mild
continuation and next native unforced current.  The construction accepts no
endpoint, local time, target solution, continuation path, or branch. -/
theorem
    sourceGeneratedWholeRestartVelocityEndpointAbsoluteWholeMildNativeContinuation
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    GeneratedWholeRestartVelocityEndpointAbsoluteWholeMildNativeContinuation
      initial elapsedBounded := by
  let ledger :=
    generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
      initial elapsedBounded
  let weak := ledger.family.endpointReceipt
  let endpoint :=
    generatedWholeRestartVelocityEndpointWholeMildReadWriteReceipt
      ledger.toCore
  let slice :=
    sourceGeneratedWholeRestartVelocityEndpointPositiveTimeH1Slice
      initial elapsedBounded
  let next :=
    sourceGeneratedWholeRestartVelocityEndpointNextCurrent
      initial elapsedBounded
  have traceGlue :=
    sourceGeneratedWholeRestartVelocityEndpoint_absoluteWeakTraceGlue
      initial elapsedBounded
  have nextSameEvent :=
    sourceGeneratedWholeRestartVelocityEndpointNextCurrent_sameEvent
      initial elapsedBounded
  refine
    { prefixEndpointTime_tendsto := ?_
      prefixVelocity_weak_tendsto := ?_
      absolutePath_initial_row := ?_
      absolutePath_coordinate_continuous := ?_
      absolutePath_row_mild_identity := ?_
      selectedAbsoluteTime_gt_accumulation := ?_
      next_duration_pos := ?_
      next_receipt_initial := ?_
      next_initial_biotSavart_absolutePath := ?_ }
  · simpa only [ledger, weak] using traceGlue.1
  · simpa only [ledger, weak] using traceGlue.2.1
  · dsimp only
    intro output
    change
      endpoint.wholePath
          (endpointAbsoluteToLocalTime
            (wholeRestartVelocityAccumulationTime initial)
            ⟨wholeRestartVelocityAccumulationTime initial, _⟩)
          output =
        wholeRestartVelocityEndpointCoefficient
          weak.velocityEndpoint output
    simpa only [endpointAbsoluteToLocalTime, sub_self] using
      traceGlue.2.2 output
  · intro output
    change Continuous fun time =>
      endpoint.wholePath
        (endpointAbsoluteToLocalTime
          (wholeRestartVelocityAccumulationTime initial) time)
        output
    exact
      (endpoint.coordinate_continuous output).comp
        (endpointAbsoluteToLocalTime_continuous
          (wholeRestartVelocityAccumulationTime initial))
  · dsimp only
    intro output outputNe time
    change
      endpoint.wholePath
          (endpointAbsoluteToLocalTime
            (wholeRestartVelocityAccumulationTime initial) time)
          output = _
    exact endpoint.row_mild_identity output outputNe _
  · change
      wholeRestartVelocityAccumulationTime initial <
        wholeRestartVelocityAccumulationTime initial + slice.time.1
    linarith [slice.time_pos]
  · simpa only [next] using nextSameEvent.1
  · dsimp only
    convert nextSameEvent.2.1 using 1
    all_goals rfl
  · intro wave
    change
      biotSavartVelocityCoefficient wave (next.initialState wave) =
        (sourceGeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt
          initial elapsedBounded).wholePath
          (endpointAbsoluteToLocalTime
            (wholeRestartVelocityAccumulationTime initial)
            (endpointLocalToAbsoluteTime
              (wholeRestartVelocityAccumulationTime initial) slice.time))
          wave
    simpa only [next, slice,
      endpointAbsoluteToLocalTime_localToAbsolute] using
      nextSameEvent.2.2 wave

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointAbsoluteWholeMildNativeContinuation
end NavierStokes
end SaturationMonoid
