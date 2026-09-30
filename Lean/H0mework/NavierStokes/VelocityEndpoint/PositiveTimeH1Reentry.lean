import H0mework.NavierStokes.VelocityEndpoint.WholeMildReadWrite
import H0mework.NavierStokes.Restart.WholeContinuousMildSerrin
import H0mework.NavierStokes.Galerkin.AmbientNorm
import H0mework.NavierStokes.WholeSpace.WholeSpaceTimeCriticalSerrin
import H0mework.NavierStokes.WholeSpace.WholeContinuousMildSerrinUniqueness

/-!
# A source-selected positive-time H1 slice of a whole velocity write

The source-generated continuous Fourier rows first assemble a canonical
pointwise whole velocity write.  Its almost-everywhere equality with the
Leray--Hopf core transports the complete gradient, zero-row, transverse and
reality laws to that actual path.  Those laws generate one late positive
time on the same pointwise write.

The selected velocity slice is then curled on the complete Fourier carrier.
The resulting vorticity is an actual `ℓ²` state, and Biot--Savart recovers
the selected velocity exactly.  No time, endpoint state, cutoff, target
solution, or continuation witness is accepted from a caller.

The curled state then enters the source-owned physical-seed compiler.  That
existing compiler generates a positive horizon, actual canonical Galerkin
orbits, their whole compactness closure and a genuine unforced mild/Serrin
receipt.  Thus the endpoint read writes the next native whole-flow current;
no target path, duration or continuation witness is accepted from a caller.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointPositiveTimeH1Reentry

open scoped ENNReal

open Set MeasureTheory
open ResponsibilityLifecycle
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinAmbientNorm
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointLerayHopfReceipt
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeGradientLowerSemicontinuity
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeCriticalSerrin
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinFamily
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeUnforcedPositiveTimeRestart
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationRoot
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartWholeContinuousMildSerrin
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness

noncomputable section

/-! ## Complete curl on the generated H1 domain -/

/-- The Fourier curl has the exact cutoff-free square bound required to
install it in the whole `ℓ²` vorticity carrier. -/
theorem fourierCurlCoefficient_norm_sq_le_gradientDensity
    (wave : IntegerWavevector)
    (velocity : ComplexCoordinateVector) :
    ‖fourierCurlCoefficient wave velocity‖ ^ 2 ≤
      (2 * Real.pi) ^ 2 *
        (integerWaveNormSq wave *
          complexCoordinateAmplitudeSq velocity) := by
  have ambientLe :=
    complexCoordinateVector_norm_sq_le_amplitudeSq
      (fourierCurlCoefficient wave velocity)
  have crossBound := complexWavevector_cross_normSq_le wave velocity
  have curlAmplitudeLe :
      complexCoordinateAmplitudeSq
          (fourierCurlCoefficient wave velocity) ≤
        (2 * Real.pi) ^ 2 *
          (integerWaveNormSq wave *
            complexCoordinateAmplitudeSq velocity) := by
    simp only [complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
    rw [fourierCurlCoefficient,
      complexCoordinateVectorNormSq_smul,
      Complex.normSq_mul, Complex.normSq_I,
      Complex.normSq_ofReal, one_mul]
    simpa only [pow_two, mul_assoc] using
      mul_le_mul_of_nonneg_left crossBound (sq_nonneg (2 * Real.pi))
  exact ambientLe.trans curlAmplitudeLe

/-- Curl a whole velocity state whose complete Fourier gradient is
summable.  The domain proof is part of the constructor, not an external
cutoff. -/
def wholeVelocityCurlState
    (velocity : ComplexVorticityHilbertState)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (velocity wave)) :
    ComplexVorticityHilbertState :=
  ⟨fun wave => fourierCurlCoefficient wave (velocity wave), by
    apply memℓp_gen
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      Summable.of_nonneg_of_le
        (fun wave => sq_nonneg
          ‖fourierCurlCoefficient wave (velocity wave)‖)
        (fun wave =>
          fourierCurlCoefficient_norm_sq_le_gradientDensity
            wave (velocity wave))
        (gradientSummable.mul_left ((2 * Real.pi) ^ 2))⟩

@[simp] theorem wholeVelocityCurlState_apply
    (velocity : ComplexVorticityHilbertState)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (velocity wave))
    (wave : IntegerWavevector) :
    wholeVelocityCurlState velocity gradientSummable wave =
      fourierCurlCoefficient wave (velocity wave) :=
  rfl

@[simp] theorem wholeVelocityCurlState_zero
    (velocity : ComplexVorticityHilbertState)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (velocity wave)) :
    wholeVelocityCurlState velocity gradientSummable 0 = 0 := by
  ext coordinate
  fin_cases coordinate <;>
    simp [wholeVelocityCurlState, fourierCurlCoefficient,
      complexWavevector, cross_apply]

/-- Curl is transverse without importing a target PDE law. -/
theorem wholeVelocityCurlState_transverse
    (velocity : ComplexVorticityHilbertState)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (velocity wave)) :
    WholeStateTransverse
      (wholeVelocityCurlState velocity gradientSummable) := by
  intro wave
  rw [wholeVelocityCurlState_apply, fourierCurlCoefficient,
    dotProduct_smul, dot_self_cross]
  simp

/-- Fourier reality survives the same complete curl compilation. -/
theorem wholeVelocityCurlState_reality
    (velocity : ComplexVorticityHilbertState)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (velocity wave))
    (reality : FiniteStateFourierReality velocity) :
    FiniteStateFourierReality
      (wholeVelocityCurlState velocity gradientSummable) := by
  intro wave
  rw [wholeVelocityCurlState_apply, wholeVelocityCurlState_apply,
    reality wave, fourierCurlCoefficient_waveNeg_vectorConj]

/-- On a transverse zero-mean velocity state, the generated curl loses no
physical information: Biot--Savart recovers every row exactly. -/
theorem biotSavart_wholeVelocityCurlState
    (velocity : ComplexVorticityHilbertState)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (velocity wave))
    (velocityZero : velocity 0 = 0)
    (velocityTransverse : WholeStateTransverse velocity)
    (wave : IntegerWavevector) :
    biotSavartVelocityCoefficient wave
        (wholeVelocityCurlState velocity gradientSummable wave) =
      velocity wave := by
  by_cases waveZero : wave = 0
  · subst wave
    simp [velocityZero]
  · rw [wholeVelocityCurlState_apply,
      biotSavartVelocityCoefficient_fourierCurlCoefficient
        wave (velocity wave) waveZero,
      transverseProjection, if_neg waveZero,
      velocityTransverse wave]
    simp

/-! ## Source-selected positive time on the canonical whole write -/

/-- One late actual time at which the whole velocity state lies in the
complete Fourier H1 domain, with the source-generated symmetry laws kept on
that same representative. -/
structure GeneratedPositiveVelocityH1Slice
    (state : Icc (0 : ℝ) 1 → ComplexVorticityHilbertState) where
  time : Icc (0 : ℝ) 1
  time_half_lt : (1 : ℝ) / 2 < time.1
  gradient_summable :
    Summable fun wave : IntegerWavevector =>
      integerWaveNormSq wave *
        complexCoordinateAmplitudeSq (state time wave)
  zero : state time 0 = 0
  transverse : WholeStateTransverse (state time)
  reality : FiniteStateFourierReality (state time)

namespace GeneratedPositiveVelocityH1Slice

theorem time_pos
    {state : Icc (0 : ℝ) 1 → ComplexVorticityHilbertState}
    (slice : GeneratedPositiveVelocityH1Slice state) :
    0 < slice.time.1 := by
  linarith [slice.time_half_lt]

/-- The complete vorticity state written by the selected velocity slice. -/
def vorticityState
    {state : Icc (0 : ℝ) 1 → ComplexVorticityHilbertState}
    (slice : GeneratedPositiveVelocityH1Slice state) :
    ComplexVorticityHilbertState :=
  wholeVelocityCurlState (state slice.time) slice.gradient_summable

@[simp] theorem vorticityState_zero
    {state : Icc (0 : ℝ) 1 → ComplexVorticityHilbertState}
    (slice : GeneratedPositiveVelocityH1Slice state) :
    slice.vorticityState 0 = 0 :=
  wholeVelocityCurlState_zero _ _

theorem vorticityState_transverse
    {state : Icc (0 : ℝ) 1 → ComplexVorticityHilbertState}
    (slice : GeneratedPositiveVelocityH1Slice state) :
    WholeStateTransverse slice.vorticityState :=
  wholeVelocityCurlState_transverse _ _

theorem vorticityState_reality
    {state : Icc (0 : ℝ) 1 → ComplexVorticityHilbertState}
    (slice : GeneratedPositiveVelocityH1Slice state) :
    FiniteStateFourierReality slice.vorticityState :=
  wholeVelocityCurlState_reality _ _ slice.reality

/-- The selected whole velocity is the exact physical Biot--Savart
projection of the generated vorticity state. -/
theorem biotSavart_vorticityState
    {state : Icc (0 : ℝ) 1 → ComplexVorticityHilbertState}
    (slice : GeneratedPositiveVelocityH1Slice state)
    (wave : IntegerWavevector) :
    biotSavartVelocityCoefficient wave (slice.vorticityState wave) =
      state slice.time wave :=
  biotSavart_wholeVelocityCurlState _ _ slice.zero
    slice.transverse wave

/-- The selected curl state is already the complete physical seed consumed
by the canonical local whole-flow compiler.  The viscosity is only the
generator index; no horizon or continuation datum is supplied here. -/
def toWholeRestartPhysicalSeed
    {ν : Viscosity}
    {state : Icc (0 : ℝ) 1 → ComplexVorticityHilbertState}
    (slice : GeneratedPositiveVelocityH1Slice state) :
    SourceOwnedWholeRestartPhysicalSeed ν where
  physicalState := slice.vorticityState
  physicalState_zero := slice.vorticityState_zero
  transverse := slice.vorticityState_transverse
  reality := slice.vorticityState_reality

@[simp] theorem wholeRestartPhysicalState_toWholeRestartPhysicalSeed
    {ν : Viscosity}
    {state : Icc (0 : ℝ) 1 → ComplexVorticityHilbertState}
    (slice : GeneratedPositiveVelocityH1Slice state) :
    wholeRestartPhysicalState
        (slice.toWholeRestartPhysicalSeed (ν := ν)) =
      slice.vorticityState :=
  rfl

end GeneratedPositiveVelocityH1Slice

/-- Finite whole gradient mass plus the actual almost-everywhere physical
laws generates one late positive H1 slice.  The caller does not choose the
time or the representative. -/
noncomputable def generatedPositiveVelocityH1Slice
    (state : Icc (0 : ℝ) 1 → ComplexVorticityHilbertState)
    (gradientAE :
      ∀ᵐ time ∂(commonTimeMeasure 1),
        Summable fun wave : IntegerWavevector =>
          integerWaveNormSq wave *
            complexCoordinateAmplitudeSq (state time wave))
    (transverseAE :
      ∀ᵐ time ∂(commonTimeMeasure 1),
        WholeStateTransverse (state time))
    (realityAE :
      ∀ᵐ time ∂(commonTimeMeasure 1),
        FiniteStateFourierReality (state time))
    (zeroAE :
      ∀ᵐ time ∂(commonTimeMeasure 1), state time 0 = 0) :
    GeneratedPositiveVelocityH1Slice state := by
  let μ := commonTimeMeasure 1
  let late := lateCommonTimes 1
  have goodAE :
      ∀ᵐ time ∂μ,
        (Summable fun wave : IntegerWavevector =>
          integerWaveNormSq wave *
            complexCoordinateAmplitudeSq (state time wave)) ∧
        state time 0 = 0 ∧
        WholeStateTransverse (state time) ∧
        FiniteStateFourierReality (state time) := by
    filter_upwards [gradientAE, zeroAE, transverseAE, realityAE] with
      time gradient zero transverse reality
    exact ⟨gradient, zero, transverse, reality⟩
  have lateMeasure : 0 < μ late := by
    exact commonTimeMeasure_lateCommonTimes_pos 1 (by norm_num)
  have restrictedNe : μ.restrict late ≠ 0 := by
    intro restrictedZero
    have univEq := congrArg
      (fun measure : Measure (Icc (0 : ℝ) 1) => measure Set.univ)
      restrictedZero
    simp at univEq
    exact lateMeasure.ne' univEq
  letI : NeZero (μ.restrict late) := ⟨restrictedNe⟩
  have goodRestricted :
      ∀ᵐ time ∂μ.restrict late,
        (Summable fun wave : IntegerWavevector =>
          integerWaveNormSq wave *
            complexCoordinateAmplitudeSq (state time wave)) ∧
        state time 0 = 0 ∧
        WholeStateTransverse (state time) ∧
        FiniteStateFourierReality (state time) :=
    ae_restrict_of_ae (s := late) goodAE
  have lateRestricted :
      ∀ᵐ time ∂μ.restrict late, time ∈ late :=
    ae_restrict_mem (lateCommonTimes_measurable 1)
  let existence := (goodRestricted.and lateRestricted).exists
  let time := Classical.choose existence
  have timeSpec := Classical.choose_spec existence
  exact
    { time := time
      time_half_lt := by
        dsimp only [time]
        simpa only [late, lateCommonTimes, Set.mem_setOf_eq] using
          timeSpec.2
      gradient_summable := timeSpec.1.1
      zero := timeSpec.1.2.1
      transverse := timeSpec.1.2.2.1
      reality := timeSpec.1.2.2.2 }

/-! ## Whole-mild endpoint consumption -/

/-- A generated whole-mild receipt produces its positive H1 slice from the
same Leray--Hopf lineage. -/
noncomputable def generatedPositiveVelocityH1SliceOfWholeMildReceipt
    {nu : Viscosity}
    {ledger :
      GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu}
    (receipt :
      GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt
        ledger) :
    GeneratedPositiveVelocityH1Slice receipt.wholePath := by
  have gradientStateAE :
      ∀ᵐ time ∂(commonTimeMeasure 1),
        Summable fun wave : IntegerWavevector =>
          integerWaveNormSq wave *
            complexCoordinateAmplitudeSq
              (receipt.core.stateLimit time wave) :=
    wholePointwiseGradientDensity_ae_summable
      1 receipt.core.stateLimit receipt.core.gradient_summable
  have gradientPathAE :
      ∀ᵐ time ∂(commonTimeMeasure 1),
        Summable fun wave : IntegerWavevector =>
          integerWaveNormSq wave *
            complexCoordinateAmplitudeSq
              (receipt.wholePath time wave) := by
    filter_upwards [gradientStateAE, receipt.stateLimit_ae] with
      time gradient pathEq
    rw [pathEq]
    exact gradient
  have zeroPathAE :
      ∀ᵐ time ∂(commonTimeMeasure 1),
        receipt.wholePath time 0 = 0 := by
    filter_upwards [receipt.core.zero_ae, receipt.stateLimit_ae] with
      time zeroEq pathEq
    rw [pathEq]
    exact zeroEq
  have transversePathAE :
      ∀ᵐ time ∂(commonTimeMeasure 1),
        WholeStateTransverse (receipt.wholePath time) := by
    filter_upwards [receipt.core.transverse_ae, receipt.stateLimit_ae] with
      time transverse pathEq
    rw [pathEq]
    exact transverse
  have realityPathAE :
      ∀ᵐ time ∂(commonTimeMeasure 1),
        FiniteStateFourierReality (receipt.wholePath time) := by
    filter_upwards [receipt.core.fourier_reality_ae,
      receipt.stateLimit_ae] with time reality pathEq
    rw [pathEq]
    exact reality
  exact
    generatedPositiveVelocityH1Slice receipt.wholePath gradientPathAE
      transversePathAE realityPathAE zeroPathAE

/-- The bounded-time endpoint presentation reads the positive H1 slice from
its generated whole-mild receipt. -/
noncomputable def
    sourceGeneratedWholeRestartVelocityEndpointPositiveTimeH1Slice
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    GeneratedPositiveVelocityH1Slice
      (sourceGeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt
        initial elapsedBounded).wholePath :=
  generatedPositiveVelocityH1SliceOfWholeMildReceipt
    (sourceGeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt
      initial elapsedBounded)

/-- The original cofinal root generates a positive H1 slice on its
pointwise whole-mild write. -/
noncomputable def sourceGeneratedNativeTemporalPositiveTimeH1Slice
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    GeneratedPositiveVelocityH1Slice
      (sourceGeneratedNativeTemporalWholeMildReadWriteReceipt
        initial).wholePath :=
  generatedPositiveVelocityH1SliceOfWholeMildReceipt
    (sourceGeneratedNativeTemporalWholeMildReadWriteReceipt initial)

/-- Same-event checkpoint: the selected state value, its H1 domain proof,
the curled vorticity, and exact Biot--Savart recovery all refer to the one
time occurrence generated by the same Leray--Hopf core receipt. -/
theorem
    sourceGeneratedWholeRestartVelocityEndpointPositiveTimeH1Slice_sameEvent
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    let receipt :=
      sourceGeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt
        initial elapsedBounded
    let slice :=
      sourceGeneratedWholeRestartVelocityEndpointPositiveTimeH1Slice
        initial elapsedBounded
    0 < slice.time.1 ∧
      receipt.wholePath slice.time 0 = 0 ∧
      WholeStateTransverse (receipt.wholePath slice.time) ∧
      FiniteStateFourierReality (receipt.wholePath slice.time) ∧
      Summable (fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq
            (receipt.wholePath slice.time wave)) ∧
      slice.vorticityState 0 = 0 ∧
      WholeStateTransverse slice.vorticityState ∧
      FiniteStateFourierReality slice.vorticityState ∧
      ∀ wave : IntegerWavevector,
        biotSavartVelocityCoefficient wave
            (slice.vorticityState wave) =
          receipt.wholePath slice.time wave := by
  dsimp only
  let slice :=
    sourceGeneratedWholeRestartVelocityEndpointPositiveTimeH1Slice
      initial elapsedBounded
  exact
    ⟨slice.time_pos, slice.zero, slice.transverse, slice.reality,
      slice.gradient_summable, slice.vorticityState_zero,
      slice.vorticityState_transverse, slice.vorticityState_reality,
      slice.biotSavart_vorticityState⟩

/-! ## Native local reentry producer -/

/-- The generated local reentry data after a positive H1 slice: a genuine
positive-time whole unforced receipt starting from the exact curled state.
No target path or continuation equality is stored as a field. -/
structure PositiveVelocityH1SliceNativeReentry
    {ν : Viscosity}
    {state : Icc (0 : ℝ) 1 → ComplexVorticityHilbertState}
    (slice : GeneratedPositiveVelocityH1Slice state) where
  duration : ℝ
  duration_pos : 0 < duration
  receipt :
    WholeContinuousMildSerrinReceipt
      ν slice.vorticityState duration

/-- The source-selected H1 slice enters the already existing whole-flow
compiler through its exact curled physical seed.  The compiler itself
generates the local horizon, every canonical Galerkin orbit, the whole
compactness limit and the unforced mild receipt. -/
noncomputable def generatedPositiveVelocityH1SliceNativeReentry
    {ν : Viscosity}
    {state : Icc (0 : ℝ) 1 → ComplexVorticityHilbertState}
    (slice : GeneratedPositiveVelocityH1Slice state) :
    PositiveVelocityH1SliceNativeReentry (ν := ν) slice := by
  let seed : SourceOwnedWholeRestartPhysicalSeed ν :=
    slice.toWholeRestartPhysicalSeed
  refine
    { duration := wholeRestartDuration seed
      duration_pos := wholeRestartDuration_pos seed
      receipt := ?_ }
  change
    WholeContinuousMildSerrinReceipt ν
      (wholeRestartPhysicalState seed) (wholeRestartDuration seed)
  exact
    generatedWholeRestartPhysicalSeedWholeContinuousMildSerrinReceipt seed

/-- Source-facing bounded-accumulation endpoint producer.  It performs the
whole chain from the canonical positive-time velocity write through curl to
the next actual positive-time unforced vorticity receipt. -/
noncomputable def
    sourceGeneratedWholeRestartVelocityEndpointPositiveTimeH1NativeReentry
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    PositiveVelocityH1SliceNativeReentry (ν := nu)
      (sourceGeneratedWholeRestartVelocityEndpointPositiveTimeH1Slice
        initial elapsedBounded) :=
  generatedPositiveVelocityH1SliceNativeReentry (ν := nu)
    (sourceGeneratedWholeRestartVelocityEndpointPositiveTimeH1Slice
      initial elapsedBounded)

/-- The original cofinal root feeds its positive H1 slice into the native
whole-flow compiler. -/
noncomputable def sourceGeneratedNativeTemporalPositiveTimeH1NativeReentry
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    PositiveVelocityH1SliceNativeReentry (ν := nu)
      (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial) :=
  generatedPositiveVelocityH1SliceNativeReentry (ν := nu)
    (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial)

namespace PositiveVelocityH1SliceNativeReentry

/-- The generated whole-mild receipt installs its own positive-time contact
as a native recursive current. -/
noncomputable def toGeneratedWholeRestartCurrent
    {ν : Viscosity}
    {state : Icc (0 : ℝ) 1 → ComplexVorticityHilbertState}
    {slice : GeneratedPositiveVelocityH1Slice state}
    (reentry : PositiveVelocityH1SliceNativeReentry (ν := ν) slice) :
    GeneratedWholeRestartCurrent ν where
  initialState := slice.vorticityState
  duration := reentry.duration
  receipt := reentry.receipt
  contact := generatedPositiveWholeRestartContact reentry.receipt

@[simp] theorem toGeneratedWholeRestartCurrent_initialState
    {ν : Viscosity}
    {state : Icc (0 : ℝ) 1 → ComplexVorticityHilbertState}
    {slice : GeneratedPositiveVelocityH1Slice state}
    (reentry : PositiveVelocityH1SliceNativeReentry (ν := ν) slice) :
    reentry.toGeneratedWholeRestartCurrent.initialState =
      slice.vorticityState :=
  rfl

@[simp] theorem toGeneratedWholeRestartCurrent_duration
    {ν : Viscosity}
    {state : Icc (0 : ℝ) 1 → ComplexVorticityHilbertState}
    {slice : GeneratedPositiveVelocityH1Slice state}
    (reentry : PositiveVelocityH1SliceNativeReentry (ν := ν) slice) :
    reentry.toGeneratedWholeRestartCurrent.duration = reentry.duration :=
  rfl

end PositiveVelocityH1SliceNativeReentry

/-- The bounded-accumulation endpoint read now writes the literal next
native whole-restart current.  Its initial state is the curl of the selected
canonical velocity occurrence, and its receipt is the actual unforced local
write generated from that same physical seed. -/
noncomputable def
    sourceGeneratedWholeRestartVelocityEndpointNextCurrent
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    GeneratedWholeRestartCurrent nu :=
  (sourceGeneratedWholeRestartVelocityEndpointPositiveTimeH1NativeReentry
    initial elapsedBounded).toGeneratedWholeRestartCurrent

/-- The original cofinal root generates its next strong local whole-restart
current after the positive H1 slice. -/
noncomputable def sourceGeneratedNativeTemporalPositiveTimeH1NextCurrent
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    GeneratedWholeRestartCurrent nu :=
  (sourceGeneratedNativeTemporalPositiveTimeH1NativeReentry
    initial).toGeneratedWholeRestartCurrent

/-- An exact cofinal occurrence executes its own endpoint payload through the
whole Galerkin ledger, the whole-mild compiler, and the positive-H1 native
reentry.  The occurrence is consumed; no endpoint or target current is
supplied separately. -/
noncomputable def
    generatedPositiveTimeH1NextCurrentOfNativeTemporalCofinalOccurrence
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (occurrence :
      (nativeTemporalSource initial).toRootSource.actual.OccurrenceAt
        (.cofinal : NativeTemporalCurrent initial)) :
    GeneratedWholeRestartCurrent nu := by
  rcases occurrence with ⟨support, event⟩
  change NativeTemporalRootEventAt initial .cofinal support at event
  cases event with
  | cofinal receipt =>
      let data : GeneratedWholeRestartVelocityEndpointData :=
        { velocityEndpoint := receipt.velocityEndpoint
          velocityEndpoint_transverse := receipt.velocityEndpoint_transverse
          velocityEndpoint_reality := receipt.velocityEndpoint_reality }
      let family :=
        generatedWholeRestartVelocityEndpointGalerkinFamilyCore nu data
      let ledger :=
        generatedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore
          family
      let whole :=
        generatedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger
      let slice := generatedPositiveVelocityH1SliceOfWholeMildReceipt whole
      exact
        (generatedPositiveVelocityH1SliceNativeReentry
          (ν := nu) slice).toGeneratedWholeRestartCurrent

/-- The original root's exact true-cofinal occurrence executes to the same
physical next current generated by the source-facing whole-flow pipeline. -/
@[simp] theorem
    nativeTemporalCofinalVisitAuthority_positiveTimeH1NextCurrent
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    generatedPositiveTimeH1NextCurrentOfNativeTemporalCofinalOccurrence
        initial (nativeTemporalCofinalVisitAuthority initial).toLedgerReadout.occurrence =
      sourceGeneratedNativeTemporalPositiveTimeH1NextCurrent initial := by
  rw [(nativeTemporalCofinalVisitAuthority initial).toLedgerReadout.occurrence_eq]
  change
    generatedPositiveTimeH1NextCurrentOfNativeTemporalCofinalOccurrence
        initial (nativeTemporalEmitted initial .cofinal) =
      sourceGeneratedNativeTemporalPositiveTimeH1NextCurrent initial
  rfl

@[simp] theorem sourceGeneratedWholeRestartVelocityEndpointNextCurrent_initialState
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    (sourceGeneratedWholeRestartVelocityEndpointNextCurrent
        initial elapsedBounded).initialState =
      (sourceGeneratedWholeRestartVelocityEndpointPositiveTimeH1Slice
        initial elapsedBounded).vorticityState :=
  rfl

/-- Whole-carrier commuting checkpoint for the endpoint write.  The same
source-selected velocity occurrence is curled into the next current, the
new unforced receipt starts literally at that curl state, and Biot--Savart
recovers the original pointwise velocity write on every Fourier row. -/
theorem sourceGeneratedWholeRestartVelocityEndpointNextCurrent_sameEvent
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    let endpoint :=
      sourceGeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt
        initial elapsedBounded
    let slice :=
      sourceGeneratedWholeRestartVelocityEndpointPositiveTimeH1Slice
        initial elapsedBounded
    let next :=
      sourceGeneratedWholeRestartVelocityEndpointNextCurrent
        initial elapsedBounded
    0 < next.duration ∧
      next.receipt.wholePath
          ⟨0, ⟨le_rfl, next.receipt.requestedTimePos.le⟩⟩ =
        slice.vorticityState ∧
      ∀ wave : IntegerWavevector,
        biotSavartVelocityCoefficient wave
            (next.initialState wave) =
          endpoint.wholePath slice.time wave := by
  dsimp only
  let slice :=
    sourceGeneratedWholeRestartVelocityEndpointPositiveTimeH1Slice
      initial elapsedBounded
  refine
    ⟨(sourceGeneratedWholeRestartVelocityEndpointPositiveTimeH1NativeReentry
        initial elapsedBounded).duration_pos, ?_, ?_⟩
  · convert
      (sourceGeneratedWholeRestartVelocityEndpointPositiveTimeH1NativeReentry
        initial elapsedBounded).receipt.wholePath_initial using 1
    all_goals rfl
  · intro wave
    rw [sourceGeneratedWholeRestartVelocityEndpointNextCurrent_initialState]
    exact slice.biotSavart_vorticityState wave

@[simp] theorem
    sourceGeneratedNativeTemporalPositiveTimeH1NextCurrent_initialState
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    (sourceGeneratedNativeTemporalPositiveTimeH1NextCurrent
        initial).initialState =
      (sourceGeneratedNativeTemporalPositiveTimeH1Slice
        initial).vorticityState :=
  rfl

/-- The original cofinal whole write, its positive H1 slice, and the next
strong local current commute on the same physical state. -/
theorem sourceGeneratedNativeTemporalPositiveTimeH1NextCurrent_sameEvent
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    let endpoint :=
      sourceGeneratedNativeTemporalWholeMildReadWriteReceipt initial
    let slice :=
      sourceGeneratedNativeTemporalPositiveTimeH1Slice initial
    let next :=
      sourceGeneratedNativeTemporalPositiveTimeH1NextCurrent initial
    0 < next.duration ∧
      next.receipt.wholePath
          ⟨0, ⟨le_rfl, next.receipt.requestedTimePos.le⟩⟩ =
        slice.vorticityState ∧
      ∀ wave : IntegerWavevector,
        biotSavartVelocityCoefficient wave
            (next.initialState wave) =
          endpoint.wholePath slice.time wave := by
  dsimp only
  let slice := sourceGeneratedNativeTemporalPositiveTimeH1Slice initial
  refine
    ⟨(sourceGeneratedNativeTemporalPositiveTimeH1NativeReentry
        initial).duration_pos, ?_, ?_⟩
  · convert
      (sourceGeneratedNativeTemporalPositiveTimeH1NativeReentry
        initial).receipt.wholePath_initial using 1
    all_goals rfl
  · intro wave
    rw [sourceGeneratedNativeTemporalPositiveTimeH1NextCurrent_initialState]
    exact slice.biotSavart_vorticityState wave

/-- The causally closed original root realizes its true-cofinal visit as the
same whole-ledger write consumed by the physical positive-time H¹ next current. -/
theorem sourceGeneratedNativeTemporalCofinalRootPhysicalExecution
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    let visit : SourceNativeTemporalVisitAt (nativeTemporalRoot initial) :=
      .cofinal (nativeTemporalCofinalVisit initial)
    let evolution := (nativeTemporalRoot initial).generatedAtTemporalVisit visit
    let next :=
      generatedPositiveTimeH1NextCurrentOfNativeTemporalCofinalOccurrence
        initial (nativeTemporalCofinalVisitAuthority initial).toLedgerReadout.occurrence
    evolution = (nativeTemporalCofinalVisitAuthority initial).toLedgerReadout ∧
      evolution.wholeLedgerWriteBack =
        nativeTemporalCofinalWrite initial ∧
      0 < next.duration ∧
      next.receipt.wholePath
          ⟨0, ⟨le_rfl, next.receipt.requestedTimePos.le⟩⟩ =
        (sourceGeneratedNativeTemporalPositiveTimeH1Slice
          initial).vorticityState ∧
      ∀ wave : IntegerWavevector,
        biotSavartVelocityCoefficient wave (next.initialState wave) =
          (sourceGeneratedNativeTemporalWholeMildReadWriteReceipt
            initial).wholePath
            (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time
            wave := by
  dsimp only
  refine ⟨rfl, rfl, ?_⟩
  rw [nativeTemporalCofinalVisitAuthority_positiveTimeH1NextCurrent]
  exact sourceGeneratedNativeTemporalPositiveTimeH1NextCurrent_sameEvent initial

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointPositiveTimeH1Reentry
end NavierStokes
end SaturationMonoid
