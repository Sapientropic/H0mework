import Mathlib.MeasureTheory.Measure.Comap
import H0mework.NavierStokes.ShellGluing.NativeMacroWholeUnforcedCompiler
import H0mework.NavierStokes.WholeSpace.WholeContinuousMildSerrinOverlap

/-!
# A source-generated positive-time restart state on the actual whole flow

Every native macro contact now generates a whole unforced mild/Serrin path.
Its gradient ledger is finite in space-time, so the source can select an
actual positive physical time at which the whole state has finite vorticity
gradient mass.  At that same time the existing transverse and Fourier-reality
laws survive.  Restricting the original receipt to the selected time makes
the selected state the literal terminal endpoint of an actual unforced whole
prefix.

The selected time and all restart laws are conclusion data.  No restart time,
endpoint state, cutoff, branch, regularity certificate, target path, or
continuation witness is accepted from a caller.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
    ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeUnforcedPositiveTimeRestart

open scoped ENNReal

open Set MeasureTheory
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open
  ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeCriticalSerrin
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRedirectRuntime
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRedirectRuntime.GeneratedRedirectedCompleteRoundInfiniteLineage
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeUnforcedCompiler
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinOverlap

noncomputable section

private theorem commonTimeMeasure_eq_comap_volume
    (requestedTime : ℝ) :
    commonTimeMeasure requestedTime =
      Measure.comap
        (Subtype.val : Icc (0 : ℝ) requestedTime → ℝ)
        volume := by
  unfold commonTimeMeasure
  rw [MeasurableEmbedding.comap_restrict
    (MeasurableEmbedding.subtype_coe measurableSet_Icc)]
  simp

/-- A positive physical interval carries a nonzero common-time measure. -/
theorem commonTimeMeasure_ne_zero_of_pos
    (requestedTime : ℝ)
    (requestedTimePos : 0 < requestedTime) :
    commonTimeMeasure requestedTime ≠ 0 := by
  rw [commonTimeMeasure_eq_comap_volume]
  intro commonZero
  let embedding :
      MeasurableEmbedding
        (Subtype.val : Icc (0 : ℝ) requestedTime → ℝ) :=
    MeasurableEmbedding.subtype_coe measurableSet_Icc
  have mapped := embedding.map_comap volume
  rw [commonZero, Measure.map_zero] at mapped
  have univEq := congrArg (fun μ : Measure ℝ => μ Set.univ) mapped
  simp at univEq
  change (0 : ENNReal) = volume (Icc (0 : ℝ) requestedTime) at univEq
  rw [Real.volume_Icc, sub_zero] at univEq
  exact (ENNReal.ofReal_pos.mpr requestedTimePos).ne' univEq.symm

/-- Strictly positive times in the physical receipt interval. -/
def positiveCommonTimes (requestedTime : ℝ) :
    Set (Icc (0 : ℝ) requestedTime) :=
  {time | 0 < time.1}

theorem positiveCommonTimes_measurable
    (requestedTime : ℝ) :
    MeasurableSet (positiveCommonTimes requestedTime) := by
  exact measurableSet_Ioi.preimage measurable_subtype_coe

/-- Positive times occupy positive common-time measure; the generated
restart cannot collapse back to the initial instant. -/
theorem commonTimeMeasure_positiveCommonTimes_pos
    (requestedTime : ℝ)
    (requestedTimePos : 0 < requestedTime) :
    0 < commonTimeMeasure requestedTime
      (positiveCommonTimes requestedTime) := by
  rw [commonTimeMeasure_eq_comap_volume]
  rw [Measure.comap_apply Subtype.val Subtype.coe_injective
    (MeasurableEmbedding.subtype_coe measurableSet_Icc).measurableSet_image'
    volume (positiveCommonTimes_measurable requestedTime)]
  have imageEq :
      Subtype.val '' positiveCommonTimes requestedTime =
        Ioc (0 : ℝ) requestedTime := by
    ext time
    constructor
    · rintro ⟨source, sourcePositive, rfl⟩
      exact ⟨sourcePositive, source.2.2⟩
    · intro timeMem
      exact ⟨⟨time, ⟨timeMem.1.le, timeMem.2⟩⟩, timeMem.1, rfl⟩
  rw [imageEq, Real.volume_Ioc, sub_zero, ENNReal.ofReal_pos]
  exact requestedTimePos

/-- The source-owned late half of one physical receipt interval.  Selecting
from this set prevents the restart producer from hiding an artificial
zero-time accumulation inside `Classical.choose`. -/
def lateCommonTimes (requestedTime : ℝ) :
    Set (Icc (0 : ℝ) requestedTime) :=
  {time | requestedTime / 2 < time.1}

theorem lateCommonTimes_measurable
    (requestedTime : ℝ) :
    MeasurableSet (lateCommonTimes requestedTime) := by
  exact measurableSet_Ioi.preimage measurable_subtype_coe

/-- The late half of every positive receipt has positive common-time
measure, so the generated contact can be selected there while retaining all
almost-everywhere physical laws. -/
theorem commonTimeMeasure_lateCommonTimes_pos
    (requestedTime : ℝ)
    (requestedTimePos : 0 < requestedTime) :
    0 < commonTimeMeasure requestedTime
      (lateCommonTimes requestedTime) := by
  rw [commonTimeMeasure_eq_comap_volume]
  rw [Measure.comap_apply Subtype.val Subtype.coe_injective
    (MeasurableEmbedding.subtype_coe measurableSet_Icc).measurableSet_image'
    volume (lateCommonTimes_measurable requestedTime)]
  have imageEq :
      Subtype.val '' lateCommonTimes requestedTime =
        Ioc (requestedTime / 2) requestedTime := by
    ext time
    constructor
    · rintro ⟨source, sourceLate, rfl⟩
      exact ⟨sourceLate, source.2.2⟩
    · intro timeMem
      have timeNonneg : 0 ≤ time := by
        linarith [timeMem.1, requestedTimePos]
      exact
        ⟨⟨time, ⟨timeNonneg, timeMem.2⟩⟩,
          timeMem.1, rfl⟩
  rw [imageEq, Real.volume_Ioc, ENNReal.ofReal_pos]
  linarith

/-- One actual positive-time state selected from a generated whole unforced
receipt, carrying exactly the laws needed by the next whole-state source
contact. -/
structure GeneratedPositiveWholeRestartContact
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime) where
  time : Icc (0 : ℝ) requestedTime
  time_pos : 0 < time.1
  time_half_lt : requestedTime / 2 < time.1
  gradient_summable :
    Summable fun wave : IntegerWavevector =>
      integerWaveNormSq wave *
        complexCoordinateAmplitudeSq (receipt.wholePath time wave)
  transverse : WholeStateTransverse (receipt.wholePath time)
  reality : FiniteStateFourierReality (receipt.wholePath time)

namespace GeneratedPositiveWholeRestartContact

/-- The actual whole physical state written by the selected source event. -/
def physicalState
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    {receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime}
    (contact : GeneratedPositiveWholeRestartContact receipt) :
    ComplexVorticityHilbertState :=
  receipt.wholePath contact.time

/-- The actual restart state keeps the source-owned zero Fourier row. -/
@[simp] theorem physicalState_zero
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    {receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime}
    (contact : GeneratedPositiveWholeRestartContact receipt) :
    contact.physicalState 0 = 0 := by
  exact receipt.wholePath_zero_row contact.time

/-- The original whole receipt restricted to the source-selected positive
time.  Hence the new physical state is reached by an actual unforced whole
path, not inserted as a symbolic increment. -/
noncomputable def prefixReceipt
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    {receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime}
    (contact : GeneratedPositiveWholeRestartContact receipt) :
    WholeContinuousMildSerrinReceipt
      ν initialState contact.time.1 :=
  restrictWholeContinuousMildSerrinReceipt
    contact.time_pos contact.time.2.2 receipt

/-- The selected physical state is definitionally the terminal value of the
actual restricted unforced receipt. -/
theorem prefixReceipt_terminal
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    {receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime}
    (contact : GeneratedPositiveWholeRestartContact receipt) :
    (contact.prefixReceipt.wholePath
        ⟨contact.time.1, ⟨contact.time_pos.le, le_rfl⟩⟩) =
      contact.physicalState := by
  change
    receipt.wholePath
        (commonTimeInclusion contact.time.2.2
          ⟨contact.time.1, ⟨contact.time_pos.le, le_rfl⟩⟩) =
      receipt.wholePath contact.time
  congr 1

end GeneratedPositiveWholeRestartContact

/-- Every whole unforced receipt internally selects a genuine positive-time
restart state with finite whole gradient, transversality, and Fourier
reality. -/
noncomputable def generatedPositiveWholeRestartContact
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime) :
    GeneratedPositiveWholeRestartContact receipt := by
  let μ := commonTimeMeasure requestedTime
  let late := lateCommonTimes requestedTime
  have statePathAE :
      ∀ᵐ time ∂μ,
        receipt.stateLimit time = receipt.wholePath time := by
    have pathAE :=
      BoundedContinuousFunction.coeFn_toLp
        (p := (2 : ℝ≥0∞))
        (μ := μ) ℂ receipt.wholePath
    filter_upwards [pathAE] with time pathEq
    rw [receipt.wholePath_toLp_eq_stateLimit] at pathEq
    exact pathEq
  have gradientAE :
      ∀ᵐ time ∂μ,
        Summable fun wave : IntegerWavevector =>
          integerWaveNormSq wave *
            complexCoordinateAmplitudeSq
              (receipt.wholePath time wave) := by
    filter_upwards [
      wholePointwiseGradientDensity_ae_summable
        requestedTime receipt.stateLimit receipt.gradient_summable,
      statePathAE] with time gradient stateEq
    simpa only [stateEq] using gradient
  have goodAE :
      ∀ᵐ time ∂μ,
        (Summable fun wave : IntegerWavevector =>
          integerWaveNormSq wave *
            complexCoordinateAmplitudeSq
              (receipt.wholePath time wave)) ∧
        WholeStateTransverse (receipt.wholePath time) ∧
        FiniteStateFourierReality (receipt.wholePath time) := by
    filter_upwards [gradientAE, receipt.wholePath_eq_transverse_ae,
      receipt.transverse_fourierReality_ae] with
        time gradient pathEq reality
    have transverse := (receipt.transverseLimit time).2
    change WholeStateTransverse
      ((receipt.transverseLimit time).1) at transverse
    exact ⟨gradient, by simpa only [pathEq] using transverse,
      by simpa only [pathEq] using reality⟩
  have lateMeasure : 0 < μ late := by
    exact commonTimeMeasure_lateCommonTimes_pos
      requestedTime receipt.requestedTimePos
  have restrictedNe : μ.restrict late ≠ 0 := by
    intro restrictedZero
    have univEq := congrArg
      (fun measure : Measure (Icc (0 : ℝ) requestedTime) =>
        measure Set.univ) restrictedZero
    simp at univEq
    exact lateMeasure.ne' univEq
  letI : NeZero (μ.restrict late) := ⟨restrictedNe⟩
  have goodRestricted :
      ∀ᵐ time ∂μ.restrict late,
        (Summable fun wave : IntegerWavevector =>
          integerWaveNormSq wave *
            complexCoordinateAmplitudeSq
              (receipt.wholePath time wave)) ∧
        WholeStateTransverse (receipt.wholePath time) ∧
        FiniteStateFourierReality (receipt.wholePath time) :=
    ae_restrict_of_ae (s := late) goodAE
  have lateRestricted : ∀ᵐ time ∂μ.restrict late,
      time ∈ late :=
    ae_restrict_mem (lateCommonTimes_measurable requestedTime)
  let existence := (goodRestricted.and lateRestricted).exists
  let time := Classical.choose existence
  have timeSpec := Classical.choose_spec existence
  have timeHalf : requestedTime / 2 < time.1 := by
    dsimp only [time]
    simpa only [late, lateCommonTimes, Set.mem_setOf_eq] using
      timeSpec.2
  exact
    { time := time
      time_pos := by
        linarith [receipt.requestedTimePos, timeHalf]
      time_half_lt := timeHalf
      gradient_summable := timeSpec.1.1
      transverse := timeSpec.1.2.1
      reality := timeSpec.1.2.2 }

/-- The authoritative native-contact producer: the exact source current
generates an actual positive-time whole endpoint with the laws required for
the next whole-state read/write event. -/
noncomputable def generatedNativeMacroWholePositiveTimeRestartContactAt
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (index : ℕ) :
    GeneratedPositiveWholeRestartContact
      (generatedNativeMacroWholeUnforcedLocalUpdateAt lineage index) :=
  generatedPositiveWholeRestartContact
    (generatedNativeMacroWholeUnforcedLocalUpdateAt lineage index)

end

end
    ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeUnforcedPositiveTimeRestart
end NavierStokes
end SaturationMonoid
