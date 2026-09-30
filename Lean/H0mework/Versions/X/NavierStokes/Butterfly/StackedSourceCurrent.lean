import H0mework.Versions.X.NavierStokes.Butterfly.StackedExpansionMaterial
import H0mework.NavierStokes.Accumulation.FullReceiptFourierConeAdvance
import H0mework.NavierStokes.Accumulation.ActualFourierConeAdvance

/-!
# Source-selected stacked butterfly current

The first stacked butterfly cell is installed as actual initial Fourier
material.  Its strict rational sideband reserves generate an open source
patch; the contact is selected inside that patch and then drives the full,
unchanged canonical next receipt through the inverse-sixth phase margin.

No theorem below identifies an actual endpoint with the rational seed.  The
rational table is used only at time zero to generate an open invariant patch.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 100000

open scoped BigOperators Topology

namespace SaturationMonoid
namespace NavierStokes
namespace RationalVorticityEvaluator
namespace ButterflyStackedSourceCurrent

open Set Filter
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinAmbientNorm
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientCanonicalExhaustiveGalerkinTarget
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartWholeContinuousMildSerrin
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSourcePairOccurrence
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairOccurrenceWork
open ThreeDimensionalVorticityCoefficientWholeTangentEnergyTransport
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinOverlap
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeUnforcedPositiveTimeRestart
open ThreeDimensionalVorticityCoefficientSourceOwnedLocalKernelAbsorption
open ThreeDimensionalVorticityCoefficientWholeStateSourceOwnedLocalBarrier
open ThreeDimensionalVorticityCoefficientFullReceiptFourierConeAdvance
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartActualFourierConeAdvance
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeTemporalEnstrophyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationNativeTurbulenceLaw
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellWholeReceiptEnergyWriteBack
open ThreeDimensionalVorticityCoefficientInstantaneousWholeNetPowerCapture
open ButterflyStackedExpansionMaterial

noncomputable section

def stackedSeedState : ComplexVorticityHilbertState :=
  butterflyFirstStackPhysicalState (-1)

def stackedPhysicalSeed :
    SourceOwnedWholeRestartPhysicalSeed butterflyGainViscosity where
  physicalState := stackedSeedState
  physicalState_zero := butterflyFirstStackPhysicalState_zero (-1)
  transverse := butterflyFirstStackPhysicalState_transverse (-1)
  reality := butterflyFirstStackPhysicalState_reality (-1)

@[simp] theorem stackedPhysicalSeed_state :
    wholeRestartPhysicalState stackedPhysicalSeed = stackedSeedState := rfl

def stackedReplay := generatedWholeRestartCanonicalReplay stackedPhysicalSeed

def stackedReceipt :=
  generatedWholeRestartWholeContinuousMildSerrinReceipt stackedReplay

theorem stackedSeedState_mass_eq :
    wholeVorticityEuclideanMass stackedSeedState = 173 / 2 :=
  butterflyFirstStackPhysicalState_negOne_mass_eq

theorem stackedPhysicalSeed_level_eq_eighty_eight :
    wholeRestartCoefficientLevel stackedPhysicalSeed = 88 := by
  unfold wholeRestartCoefficientLevel wholeRestartRawCoefficientCeiling
  rw [stackedPhysicalSeed_state, stackedSeedState_mass_eq]
  norm_num

theorem stackedPhysicalSeed_ceiling_eq_eighty_eight :
    wholeRestartCoefficientCeiling stackedPhysicalSeed = 88 := by
  unfold wholeRestartCoefficientCeiling
  rw [stackedPhysicalSeed_level_eq_eighty_eight]
  norm_num

def plusSideband : IntegerWavevector := axisWave 4 + pumpY
def minusSideband : IntegerWavevector := axisWave 4 - pumpY

def stackedSidebandModes : Finset IntegerWavevector :=
  {plusSideband, minusSideband}

def stackedSidebandCone : FiniteFourierPhaseCone where
  modes := stackedSidebandModes
  zeroNotMem := by decide
  axis := fun wave => stackedSeedState wave

def sourceReserveAt
    (state : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) : Real :=
  complexCoordinateRealInner (stackedSeedState wave) (state wave)

def sourceTangentWorkAt
    (state : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) : Real :=
  complexCoordinateRealInner (stackedSeedState wave)
    (wholeLatticeVorticityFourierTangentAt
      butterflyGainViscosity.coeff state wave)

def selfTangentWorkAt
    (state : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) : Real :=
  complexCoordinateRealInner (state wave)
    (wholeLatticeVorticityFourierTangentAt
      butterflyGainViscosity.coeff state wave)

theorem stackedSeedState_sideband_reserve_eq
    (wave : IntegerWavevector)
    (waveMem : wave ∈ stackedSidebandModes) :
    sourceReserveAt stackedSeedState wave = 121 / 8 := by
  have waveEq : wave = axisWave 4 + pumpY ∨
      wave = axisWave 4 - pumpY := by
    simpa only [stackedSidebandModes, plusSideband, minusSideband,
      Finset.mem_insert, Finset.mem_singleton] using waveMem
  unfold sourceReserveAt stackedSeedState
  rw [complexCoordinateRealInner_self,
    ← complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
  exact butterflyFirstStackPhysicalState_negOne_sideband_mass_eq wave waveEq

theorem stackedSeedState_sideband_work_eq
    (wave : IntegerWavevector)
    (waveMem : wave ∈ stackedSidebandModes) :
    sourceTangentWorkAt stackedSeedState wave = 10043 / 800 := by
  have waveEq : wave = axisWave 4 + pumpY ∨
      wave = axisWave 4 - pumpY := by
    simpa only [stackedSidebandModes, plusSideband, minusSideband,
      Finset.mem_insert, Finset.mem_singleton] using waveMem
  exact butterflyFirstStackPhysicalState_negOne_sideband_work_eq wave waveEq

def receiptReserveAt
    (wave : IntegerWavevector)
    (time : Icc (0 : Real) (wholeRestartDuration stackedPhysicalSeed)) : Real :=
  sourceReserveAt (stackedReceipt.wholePath time) wave

def receiptTangentWorkAt
    (wave : IntegerWavevector)
    (time : Icc (0 : Real) (wholeRestartDuration stackedPhysicalSeed)) : Real :=
  sourceTangentWorkAt (stackedReceipt.wholePath time) wave

def receiptSelfTangentWorkAt
    (wave : IntegerWavevector)
    (time : Icc (0 : Real) (wholeRestartDuration stackedPhysicalSeed)) : Real :=
  selfTangentWorkAt (stackedReceipt.wholePath time) wave

/-- Complete fixed-source power on the actual stacked receipt.  This reads
all rows of the finite source material, not only the two paying sidebands. -/
def stackedReceiptWholePowerAt (actual : Real) : Real :=
  actualProjectedWholeNetEnstrophyPower stackedReceipt
    butterflyFirstStackModes actual

theorem stackedReceiptWholePowerAt_continuous :
    Continuous stackedReceiptWholePowerAt := by
  exact actualProjectedWholeNetEnstrophyPower_continuous
    stackedReceipt butterflyFirstStackModes

theorem stackedReceiptWholePowerAt_zero_eq :
    stackedReceiptWholePowerAt 0 = 627 / 100 := by
  unfold stackedReceiptWholePowerAt
  rw [actualProjectedWholeNetEnstrophyPower_zero_eq_wholeTangentWork]
  change
    2 * ∑ wave ∈ butterflyFirstStackModes,
      complexCoordinateRealInner (stackedSeedState wave)
        (wholeLatticeVorticityFourierTangentAt
          butterflyGainViscosity.coeff stackedSeedState wave) = 627 / 100
  rw [show stackedSeedState = butterflyFirstStackPhysicalState (-1) by rfl]
  rw [butterflyFirstStackPhysicalWholeWork_eq,
    butterflyFirstStackWholeWork_negOne_eq]
  norm_num

/-- Source selection window in which the complete stacked material keeps
three units of power, leaving one full unit for the generated next replay. -/
theorem exists_stackedReceiptWholePowerTime :
    ∃ epsilon : Real, 0 < epsilon ∧
      ∀ actual : Real, 0 < actual → actual < epsilon →
        3 < stackedReceiptWholePowerAt actual := by
  let good : Set Real := {actual | (3 : Real) < stackedReceiptWholePowerAt actual}
  have zeroMem : (0 : Real) ∈ good := by
    change (3 : Real) < stackedReceiptWholePowerAt 0
    rw [stackedReceiptWholePowerAt_zero_eq]
    norm_num
  have goodOpen : IsOpen good :=
    isOpen_lt continuous_const stackedReceiptWholePowerAt_continuous
  obtain ⟨epsilon, epsilonPos, ballSubset⟩ :=
    Metric.isOpen_iff.mp goodOpen 0 zeroMem
  refine ⟨epsilon, epsilonPos, ?_⟩
  intro actual actualPos actualLt
  apply ballSubset
  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos actualPos]
  exact actualLt

noncomputable def stackedReceiptWholePowerTime : Real :=
  Classical.choose exists_stackedReceiptWholePowerTime

theorem stackedReceiptWholePowerTime_pos :
    0 < stackedReceiptWholePowerTime :=
  (Classical.choose_spec exists_stackedReceiptWholePowerTime).1

theorem stackedReceiptWholePowerTime_spec
    (actual : Real) (actualPos : 0 < actual)
    (actualLt : actual < stackedReceiptWholePowerTime) :
    3 < stackedReceiptWholePowerAt actual :=
  (Classical.choose_spec exists_stackedReceiptWholePowerTime).2
    actual actualPos actualLt

private theorem receiptStateRow_continuous
    (wave : IntegerWavevector) :
    Continuous fun time : Icc (0 : Real)
        (wholeRestartDuration stackedPhysicalSeed) =>
      stackedReceipt.wholePath time wave :=
  (lp.evalCLM ℂ
    (fun _ : IntegerWavevector => ComplexCoordinateVector)
    2 wave).continuous.comp stackedReceipt.wholePath.continuous

theorem receiptReserveAt_continuous (wave : IntegerWavevector) :
    Continuous (receiptReserveAt wave) := by
  unfold receiptReserveAt sourceReserveAt
  exact complexCoordinateRealInner_prod_continuous.comp
    (continuous_const.prodMk (receiptStateRow_continuous wave))

theorem receiptTangentWorkAt_continuous (wave : IntegerWavevector) :
    Continuous (receiptTangentWorkAt wave) := by
  let transversePath : Icc (0 : Real)
      (wholeRestartDuration stackedPhysicalSeed) →
      WholeTransverseVorticityState := fun time =>
    ⟨stackedReceipt.wholePath time,
      wholePath_transverse stackedReceipt time⟩
  have transversePathContinuous : Continuous transversePath :=
    stackedReceipt.wholePath.continuous.subtype_mk
      (wholePath_transverse stackedReceipt)
  have nonlinearContinuous : Continuous fun time =>
      wholeStateVorticityNonlinearCoefficientAt
        (transversePath time).1 wave :=
    (wholeStateVorticityNonlinearCoefficientAt_continuous wave).comp
      transversePathContinuous
  have viscousContinuous : Continuous fun time : Icc (0 : Real)
      (wholeRestartDuration stackedPhysicalSeed) =>
      (butterflyGainViscosity.coeff * integerWaveViscousMultiplier wave) •
        stackedReceipt.wholePath time wave := by
    have scaled := (receiptStateRow_continuous wave).const_smul
      (butterflyGainViscosity.coeff * integerWaveViscousMultiplier wave)
    apply scaled.congr
    intro time
    rfl
  have tangentContinuous : Continuous fun time : Icc (0 : Real)
      (wholeRestartDuration stackedPhysicalSeed) =>
      wholeLatticeVorticityFourierTangentAt
        butterflyGainViscosity.coeff
        (stackedReceipt.wholePath time) wave := by
    unfold wholeLatticeVorticityFourierTangentAt
    apply (nonlinearContinuous.sub viscousContinuous).congr
    intro time
    rfl
  unfold receiptTangentWorkAt sourceTangentWorkAt
  exact complexCoordinateRealInner_prod_continuous.comp
    (continuous_const.prodMk tangentContinuous)

theorem receiptSelfTangentWorkAt_continuous (wave : IntegerWavevector) :
    Continuous (receiptSelfTangentWorkAt wave) := by
  let transversePath : Icc (0 : Real)
      (wholeRestartDuration stackedPhysicalSeed) →
      WholeTransverseVorticityState := fun time =>
    ⟨stackedReceipt.wholePath time,
      wholePath_transverse stackedReceipt time⟩
  have transversePathContinuous : Continuous transversePath :=
    stackedReceipt.wholePath.continuous.subtype_mk
      (wholePath_transverse stackedReceipt)
  have nonlinearContinuous : Continuous fun time =>
      wholeStateVorticityNonlinearCoefficientAt
        (transversePath time).1 wave :=
    (wholeStateVorticityNonlinearCoefficientAt_continuous wave).comp
      transversePathContinuous
  have viscousContinuous : Continuous fun time : Icc (0 : Real)
      (wholeRestartDuration stackedPhysicalSeed) =>
      (butterflyGainViscosity.coeff * integerWaveViscousMultiplier wave) •
        stackedReceipt.wholePath time wave := by
    have scaled := (receiptStateRow_continuous wave).const_smul
      (butterflyGainViscosity.coeff * integerWaveViscousMultiplier wave)
    apply scaled.congr
    intro time
    rfl
  have tangentContinuous : Continuous fun time : Icc (0 : Real)
      (wholeRestartDuration stackedPhysicalSeed) =>
      wholeLatticeVorticityFourierTangentAt
        butterflyGainViscosity.coeff
        (stackedReceipt.wholePath time) wave := by
    unfold wholeLatticeVorticityFourierTangentAt
    apply (nonlinearContinuous.sub viscousContinuous).congr
    intro time
    rfl
  unfold receiptSelfTangentWorkAt selfTangentWorkAt
  exact complexCoordinateRealInner_prod_continuous.comp
    ((receiptStateRow_continuous wave).prodMk tangentContinuous)

private theorem wholeMass_continuous :
    Continuous wholeVorticityEuclideanMass := by
  have functionalEq :
      wholeVorticityEuclideanMass =
        fun state : ComplexVorticityHilbertState =>
          ∑ coordinate : Coordinate,
            ‖wholeStateCoordinateSliceCLM coordinate state‖ ^ 2 := by
    funext state
    exact wholeVorticityEuclideanMass_eq_coordinateSlices state
  rw [functionalEq]
  fun_prop

def StackedSourcePatchAt
    (time : Icc (0 : Real) (wholeRestartDuration stackedPhysicalSeed)) : Prop :=
  86 < wholeVorticityEuclideanMass (stackedReceipt.wholePath time) ∧
  wholeVorticityEuclideanMass (stackedReceipt.wholePath time) < 87 ∧
  ∀ wave ∈ stackedSidebandModes,
    15 < receiptReserveAt wave time ∧
    10 < receiptTangentWorkAt wave time ∧
    12 < receiptSelfTangentWorkAt wave time

theorem exists_stackedSourcePatch :
    ∃ epsilon : Real, 0 < epsilon ∧
      ∀ time : Icc (0 : Real) (wholeRestartDuration stackedPhysicalSeed),
        time.1 < epsilon → StackedSourcePatchAt time := by
  let zeroTime : Icc (0 : Real)
      (wholeRestartDuration stackedPhysicalSeed) :=
    ⟨0, ⟨le_rfl, (wholeRestartDuration_pos stackedPhysicalSeed).le⟩⟩
  let good : Set (Icc (0 : Real)
      (wholeRestartDuration stackedPhysicalSeed)) :=
    {time | StackedSourcePatchAt time}
  have massPathContinuous : Continuous fun time : Icc (0 : Real)
      (wholeRestartDuration stackedPhysicalSeed) =>
      wholeVorticityEuclideanMass (stackedReceipt.wholePath time) :=
    wholeMass_continuous.comp stackedReceipt.wholePath.continuous
  have goodOpen : IsOpen good := by
    unfold good StackedSourcePatchAt
    have massLower : IsOpen {time : Icc (0 : Real)
        (wholeRestartDuration stackedPhysicalSeed) |
      (86 : Real) < wholeVorticityEuclideanMass
        (stackedReceipt.wholePath time)} :=
      isOpen_lt continuous_const massPathContinuous
    have massUpper : IsOpen {time : Icc (0 : Real)
        (wholeRestartDuration stackedPhysicalSeed) |
      wholeVorticityEuclideanMass (stackedReceipt.wholePath time) <
        (87 : Real)} :=
      isOpen_lt massPathContinuous continuous_const
    have sidebandOpen : IsOpen {time : Icc (0 : Real)
        (wholeRestartDuration stackedPhysicalSeed) |
      ∀ wave ∈ stackedSidebandModes,
        15 < receiptReserveAt wave time ∧
        10 < receiptTangentWorkAt wave time ∧
        12 < receiptSelfTangentWorkAt wave time} := by
      let plusGood : Set (Icc (0 : Real)
          (wholeRestartDuration stackedPhysicalSeed)) :=
        {time | 15 < receiptReserveAt plusSideband time ∧
          10 < receiptTangentWorkAt plusSideband time ∧
          12 < receiptSelfTangentWorkAt plusSideband time}
      let minusGood : Set (Icc (0 : Real)
          (wholeRestartDuration stackedPhysicalSeed)) :=
        {time | 15 < receiptReserveAt minusSideband time ∧
          10 < receiptTangentWorkAt minusSideband time ∧
          12 < receiptSelfTangentWorkAt minusSideband time}
      have plusOpen : IsOpen plusGood :=
        (isOpen_lt continuous_const
          (receiptReserveAt_continuous plusSideband)).inter
        ((isOpen_lt continuous_const
          (receiptTangentWorkAt_continuous plusSideband)).inter
        (isOpen_lt continuous_const
          (receiptSelfTangentWorkAt_continuous plusSideband)))
      have minusOpen : IsOpen minusGood :=
        (isOpen_lt continuous_const
          (receiptReserveAt_continuous minusSideband)).inter
        ((isOpen_lt continuous_const
          (receiptTangentWorkAt_continuous minusSideband)).inter
        (isOpen_lt continuous_const
          (receiptSelfTangentWorkAt_continuous minusSideband)))
      rw [show {time : Icc (0 : Real)
          (wholeRestartDuration stackedPhysicalSeed) |
          ∀ wave ∈ stackedSidebandModes,
            15 < receiptReserveAt wave time ∧
            10 < receiptTangentWorkAt wave time ∧
            12 < receiptSelfTangentWorkAt wave time} =
          plusGood ∩ minusGood by
        ext time
        simp [plusGood, minusGood, stackedSidebandModes]]
      exact plusOpen.inter minusOpen
    exact massLower.inter (massUpper.inter sidebandOpen)
  have zeroMem : zeroTime ∈ good := by
    change StackedSourcePatchAt zeroTime
    have pathZero : stackedReceipt.wholePath zeroTime = stackedSeedState := by
      exact stackedReceipt.wholePath_initial
    rw [StackedSourcePatchAt, pathZero, stackedSeedState_mass_eq]
    refine ⟨by norm_num, by norm_num, ?_⟩
    intro wave waveMem
    have reserve := stackedSeedState_sideband_reserve_eq wave waveMem
    have work := stackedSeedState_sideband_work_eq wave waveMem
    unfold receiptReserveAt receiptTangentWorkAt
    rw [pathZero]
    exact ⟨by linarith, by linarith, by
      unfold receiptSelfTangentWorkAt selfTangentWorkAt
      rw [pathZero]
      unfold sourceTangentWorkAt at work
      linarith⟩
  obtain ⟨epsilon, epsilonPos, ballSubset⟩ :=
    Metric.isOpen_iff.mp goodOpen zeroTime zeroMem
  refine ⟨epsilon, epsilonPos, ?_⟩
  intro time timeLt
  apply ballSubset
  rw [Metric.mem_ball]
  change dist time.1 zeroTime.1 < epsilon
  simpa only [zeroTime, Real.dist_eq, sub_zero,
    abs_of_nonneg time.2.1] using timeLt

def stackedSourcePatchTime : Real :=
  Classical.choose exists_stackedSourcePatch

theorem stackedSourcePatchTime_pos : 0 < stackedSourcePatchTime :=
  (Classical.choose_spec exists_stackedSourcePatch).1

/-- The exact first dyadic receiver is generated by the actual whole path,
not installed in the rational seed.  Its nonzero source tangent therefore
creates a source-owned punctured persistence horizon. -/
theorem exists_stackedAxisEightPersistenceTime :
    ∃ epsilon : Real, 0 < epsilon ∧
      ∀ actual : Real, 0 < actual → actual < epsilon →
        actualWholeContinuousHeatDuhamelPath stackedReceipt
          butterflyFirstStackAxisEight actual ≠ 0 := by
  have tangentPos : 0 <
      ‖wholeLatticeVorticityFourierTangentAt
        butterflyGainViscosity.coeff stackedSeedState
        butterflyFirstStackAxisEight‖ := by
    exact (by norm_num : (0 : Real) < 120 / 17).trans_le
      butterflyFirstStackPhysicalTangent_negOne_axisEight_norm_ge
  have tangentNe :
      wholeLatticeVorticityFourierTangentAt
        butterflyGainViscosity.coeff stackedSeedState
        butterflyFirstStackAxisEight ≠ 0 :=
    norm_pos_iff.mp tangentPos
  have derivative := actualWholeContinuousHeatDuhamelPath_hasDerivAt_zero
    stackedReceipt butterflyFirstStackAxisEight
  have punctured := derivative.eventually_ne tangentNe
    (c := (0 : ComplexCoordinateVector))
  have nearZero :
      ∀ᶠ actual in nhds (0 : Real), actual ≠ 0 →
        actualWholeContinuousHeatDuhamelPath stackedReceipt
          butterflyFirstStackAxisEight actual ≠ 0 :=
    eventually_nhdsWithin_iff.mp punctured
  obtain ⟨epsilon, epsilonPos, withinBall⟩ :=
    Metric.eventually_nhds_iff.mp nearZero
  refine ⟨epsilon, epsilonPos, ?_⟩
  intro actual actualPos actualLt
  apply withinBall
  · rw [Real.dist_eq, sub_zero, abs_of_pos actualPos]
    exact actualLt
  · exact actualPos.ne'

def stackedAxisEightPersistenceTime : Real :=
  Classical.choose exists_stackedAxisEightPersistenceTime

theorem stackedAxisEightPersistenceTime_pos :
    0 < stackedAxisEightPersistenceTime :=
  (Classical.choose_spec exists_stackedAxisEightPersistenceTime).1

theorem exists_stackedAxisEightPlusYPersistenceTime :
    ∃ epsilon : Real, 0 < epsilon ∧
      ∀ actual : Real, 0 < actual → actual < epsilon →
        actualWholeContinuousHeatDuhamelPath stackedReceipt
          butterflyFirstStackAxisEightPlusY actual ≠ 0 := by
  have tangentNe :
      wholeLatticeVorticityFourierTangentAt
        butterflyGainViscosity.coeff stackedSeedState
        butterflyFirstStackAxisEightPlusY ≠ 0 := by
    change wholeLatticeVorticityFourierTangentAt
      butterflyGainViscosity.coeff (butterflyFirstStackPhysicalState (-1))
        butterflyFirstStackAxisEightPlusY ≠ 0
    rw [butterflyFirstStackPhysicalTangent_negOne_axisEightPlusY_eq]
    intro rowZero
    have coordinateZero := congrFun rowZero 0
    norm_num [GaussianRatVector.toComplex, GaussianRat.toComplex,
      realRow, realGaussian, Matrix.cons_val_zero] at coordinateZero
  have derivative := actualWholeContinuousHeatDuhamelPath_hasDerivAt_zero
    stackedReceipt butterflyFirstStackAxisEightPlusY
  have punctured := derivative.eventually_ne tangentNe
    (c := (0 : ComplexCoordinateVector))
  have nearZero :
      ∀ᶠ actual in nhds (0 : Real), actual ≠ 0 →
        actualWholeContinuousHeatDuhamelPath stackedReceipt
          butterflyFirstStackAxisEightPlusY actual ≠ 0 :=
    eventually_nhdsWithin_iff.mp punctured
  obtain ⟨epsilon, epsilonPos, withinBall⟩ :=
    Metric.eventually_nhds_iff.mp nearZero
  refine ⟨epsilon, epsilonPos, ?_⟩
  intro actual actualPos actualLt
  apply withinBall
  · rw [Real.dist_eq, sub_zero, abs_of_pos actualPos]
    exact actualLt
  · exact actualPos.ne'

theorem exists_stackedAxisEightMinusYPersistenceTime :
    ∃ epsilon : Real, 0 < epsilon ∧
      ∀ actual : Real, 0 < actual → actual < epsilon →
        actualWholeContinuousHeatDuhamelPath stackedReceipt
          butterflyFirstStackAxisEightMinusY actual ≠ 0 := by
  have tangentNe :
      wholeLatticeVorticityFourierTangentAt
        butterflyGainViscosity.coeff stackedSeedState
        butterflyFirstStackAxisEightMinusY ≠ 0 := by
    change wholeLatticeVorticityFourierTangentAt
      butterflyGainViscosity.coeff (butterflyFirstStackPhysicalState (-1))
        butterflyFirstStackAxisEightMinusY ≠ 0
    rw [butterflyFirstStackPhysicalTangent_negOne_axisEightMinusY_eq]
    intro rowZero
    have coordinateZero := congrFun rowZero 0
    norm_num [GaussianRatVector.toComplex, GaussianRat.toComplex,
      realRow, realGaussian, Matrix.cons_val_zero] at coordinateZero
  have derivative := actualWholeContinuousHeatDuhamelPath_hasDerivAt_zero
    stackedReceipt butterflyFirstStackAxisEightMinusY
  have punctured := derivative.eventually_ne tangentNe
    (c := (0 : ComplexCoordinateVector))
  have nearZero :
      ∀ᶠ actual in nhds (0 : Real), actual ≠ 0 →
        actualWholeContinuousHeatDuhamelPath stackedReceipt
          butterflyFirstStackAxisEightMinusY actual ≠ 0 :=
    eventually_nhdsWithin_iff.mp punctured
  obtain ⟨epsilon, epsilonPos, withinBall⟩ :=
    Metric.eventually_nhds_iff.mp nearZero
  refine ⟨epsilon, epsilonPos, ?_⟩
  intro actual actualPos actualLt
  apply withinBall
  · rw [Real.dist_eq, sub_zero, abs_of_pos actualPos]
    exact actualLt
  · exact actualPos.ne'

def stackedAxisEightPlusYPersistenceTime : Real :=
  Classical.choose exists_stackedAxisEightPlusYPersistenceTime

def stackedAxisEightMinusYPersistenceTime : Real :=
  Classical.choose exists_stackedAxisEightMinusYPersistenceTime

theorem stackedAxisEightPlusYPersistenceTime_pos :
    0 < stackedAxisEightPlusYPersistenceTime :=
  (Classical.choose_spec exists_stackedAxisEightPlusYPersistenceTime).1

theorem stackedAxisEightMinusYPersistenceTime_pos :
    0 < stackedAxisEightMinusYPersistenceTime :=
  (Classical.choose_spec exists_stackedAxisEightMinusYPersistenceTime).1

def stackedChildFacePersistenceTime : Real :=
  min stackedAxisEightPersistenceTime
    (min stackedAxisEightPlusYPersistenceTime
      stackedAxisEightMinusYPersistenceTime)

theorem stackedChildFacePersistenceTime_pos :
    0 < stackedChildFacePersistenceTime := by
  exact lt_min stackedAxisEightPersistenceTime_pos
    (lt_min stackedAxisEightPlusYPersistenceTime_pos
      stackedAxisEightMinusYPersistenceTime_pos)

/-! ## Source-generated quantitative child-face valuation -/

private def stackedChildFaceStatePath
    (wave : IntegerWavevector) : Real → ComplexCoordinateVector :=
  actualWholeContinuousHeatDuhamelPath stackedReceipt wave

private def stackedChildFaceTangentPath
    (wave : IntegerWavevector) : Real → ComplexCoordinateVector := fun actual =>
  actualWholeContinuousNonlinearRow stackedReceipt wave actual -
    (butterflyGainViscosity.coeff * integerWaveViscousMultiplier wave) •
      stackedChildFaceStatePath wave actual

private def stackedChildFaceNetPowerPath
    (wave : IntegerWavevector) (actual : Real) : Real :=
  2 * complexCoordinateRealInner
    (stackedChildFaceStatePath wave actual)
    (stackedChildFaceTangentPath wave actual)

private theorem stackedChildFace_seedRow_zero
    (wave : IntegerWavevector)
    (waveMem : wave ∈ butterflyFirstStackChildFaceModes) :
    stackedSeedState wave = 0 := by
  simp only [butterflyFirstStackChildFaceModes, Finset.mem_insert,
    Finset.mem_singleton] at waveMem
  rcases waveMem with rfl | rfl | rfl
  · exact butterflyFirstStackPhysicalState_negOne_axisEight_zero
  · exact butterflyFirstStackPhysicalState_negOne_axisEightPlusY_zero
  · exact butterflyFirstStackPhysicalState_negOne_axisEightMinusY_zero

private theorem stackedChildFace_seedTangent_ne_zero
    (wave : IntegerWavevector)
    (waveMem : wave ∈ butterflyFirstStackChildFaceModes) :
    wholeLatticeVorticityFourierTangentAt
        butterflyGainViscosity.coeff stackedSeedState wave ≠ 0 := by
  simp only [butterflyFirstStackChildFaceModes, Finset.mem_insert,
    Finset.mem_singleton] at waveMem
  rcases waveMem with rfl | rfl | rfl
  · change wholeLatticeVorticityFourierTangentAt
      butterflyGainViscosity.coeff (butterflyFirstStackPhysicalState (-1))
        butterflyFirstStackAxisEight ≠ 0
    rw [butterflyFirstStackPhysicalTangent_negOne_axisEight_eq]
    intro rowZero
    have coordinateZero := congrFun rowZero 1
    norm_num [GaussianRatVector.toComplex, GaussianRat.toComplex,
      realRow, realGaussian, Matrix.cons_val_one] at coordinateZero
  · change wholeLatticeVorticityFourierTangentAt
      butterflyGainViscosity.coeff (butterflyFirstStackPhysicalState (-1))
        butterflyFirstStackAxisEightPlusY ≠ 0
    rw [butterflyFirstStackPhysicalTangent_negOne_axisEightPlusY_eq]
    intro rowZero
    have coordinateZero := congrFun rowZero 0
    norm_num [GaussianRatVector.toComplex, GaussianRat.toComplex,
      realRow, realGaussian, Matrix.cons_val_zero] at coordinateZero
  · change wholeLatticeVorticityFourierTangentAt
      butterflyGainViscosity.coeff (butterflyFirstStackPhysicalState (-1))
        butterflyFirstStackAxisEightMinusY ≠ 0
    rw [butterflyFirstStackPhysicalTangent_negOne_axisEightMinusY_eq]
    intro rowZero
    have coordinateZero := congrFun rowZero 0
    norm_num [GaussianRatVector.toComplex, GaussianRat.toComplex,
      realRow, realGaussian, Matrix.cons_val_zero] at coordinateZero

private theorem stackedChildFaceStatePath_zero
    (wave : IntegerWavevector)
    (waveMem : wave ∈ butterflyFirstStackChildFaceModes) :
    stackedChildFaceStatePath wave 0 = 0 := by
  unfold stackedChildFaceStatePath actualWholeContinuousHeatDuhamelPath
    heatDuhamelComplexCoordinatePath intervalIntegralComplexCoordinatePath
  simp [stackedPhysicalSeed_state,
    stackedChildFace_seedRow_zero wave waveMem]

private theorem stackedChildFaceTangentPath_zero
    (wave : IntegerWavevector)
    (waveMem : wave ∈ butterflyFirstStackChildFaceModes) :
    stackedChildFaceTangentPath wave 0 =
      wholeLatticeVorticityFourierTangentAt
        butterflyGainViscosity.coeff stackedSeedState wave := by
  unfold stackedChildFaceTangentPath
  rw [actualWholeContinuousNonlinearRow_zero,
    stackedChildFaceStatePath_zero wave waveMem, smul_zero, sub_zero]
  unfold wholeLatticeVorticityFourierTangentAt
  rw [stackedChildFace_seedRow_zero wave waveMem, smul_zero, sub_zero]
  rfl

private theorem stackedChildFaceStatePath_hasDerivAt_zero
    (wave : IntegerWavevector) :
    HasDerivAt (stackedChildFaceStatePath wave)
      (wholeLatticeVorticityFourierTangentAt
        butterflyGainViscosity.coeff stackedSeedState wave) 0 :=
  actualWholeContinuousHeatDuhamelPath_hasDerivAt_zero stackedReceipt wave

private theorem stackedChildFaceStatePath_continuous
    (wave : IntegerWavevector) :
    Continuous (stackedChildFaceStatePath wave) := by
  rw [continuous_iff_continuousAt]
  intro actual
  exact
    (heatDuhamelComplexCoordinatePath_hasDerivAt_of_continuous
      (stackedSeedState wave)
      (actualWholeContinuousNonlinearRow stackedReceipt wave)
      (butterflyGainViscosity.coeff *
        integerWaveViscousMultiplier wave)
      0 actual
      (actualWholeContinuousNonlinearRow_continuous
        stackedReceipt wave)).continuousAt

private theorem stackedChildFaceTangentPath_continuous
    (wave : IntegerWavevector) :
    Continuous (stackedChildFaceTangentPath wave) := by
  unfold stackedChildFaceTangentPath
  have viscousContinuous : Continuous fun actual =>
      (butterflyGainViscosity.coeff * integerWaveViscousMultiplier wave) •
        stackedChildFaceStatePath wave actual := by
    change Continuous
      (((butterflyGainViscosity.coeff *
        integerWaveViscousMultiplier wave) : Real) •
          stackedChildFaceStatePath wave)
    exact (stackedChildFaceStatePath_continuous wave).const_smul _
  exact (actualWholeContinuousNonlinearRow_continuous
    stackedReceipt wave).sub viscousContinuous

private theorem complexCoordinateRealInner_real_smul_left_child
    (scalar : Real)
    (left right : ComplexCoordinateVector) :
    complexCoordinateRealInner (scalar • left) right =
      scalar * complexCoordinateRealInner left right := by
  unfold complexCoordinateRealInner
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro coordinate _
  simp only [Pi.smul_apply, Complex.smul_re, Complex.smul_im]
  ring

/-- Every row of the complete child face carries positive actual physical
power on one common source-generated right neighborhood.  The statement is
about the actual whole path, not a Taylor table. -/
private theorem stackedChildFaceNetPowerPath_eventually_pos :
    ∀ᶠ actual in 𝓝[>] (0 : Real),
      ∀ wave ∈ butterflyFirstStackChildFaceModes,
        0 < stackedChildFaceNetPowerPath wave actual := by
  have rowEventually : ∀ wave ∈ butterflyFirstStackChildFaceModes,
      ∀ᶠ actual in 𝓝[>] (0 : Real),
        0 < stackedChildFaceNetPowerPath wave actual := by
    intro wave waveMem
    let q := wholeLatticeVorticityFourierTangentAt
      butterflyGainViscosity.coeff stackedSeedState wave
    have qNormPos : 0 < complexCoordinateVectorNormSq q :=
      (complexCoordinateVectorNormSq_pos_iff q).mpr
        (stackedChildFace_seedTangent_ne_zero wave waveMem)
    have slopeTendsto :
        Tendsto (fun actual =>
          actual⁻¹ • stackedChildFaceStatePath wave actual)
          (𝓝[>] (0 : Real)) (𝓝 q) := by
      simpa only [stackedChildFaceStatePath_zero wave waveMem,
        zero_add, sub_zero] using
        (stackedChildFaceStatePath_hasDerivAt_zero wave).tendsto_slope_zero_right
    have tangentTendsto : Tendsto (stackedChildFaceTangentPath wave)
        (𝓝[>] (0 : Real)) (𝓝 q) := by
      have whole : ContinuousAt (stackedChildFaceTangentPath wave) 0 :=
        (stackedChildFaceTangentPath_continuous wave).continuousAt
      have restricted := whole.mono_left
        (show 𝓝[>] (0 : Real) ≤ 𝓝 (0 : Real) from inf_le_left)
      simpa only [q, stackedChildFaceTangentPath_zero wave waveMem] using
        restricted
    let scaled : Real → Real := fun actual =>
      2 * complexCoordinateRealInner
        (actual⁻¹ • stackedChildFaceStatePath wave actual)
        (stackedChildFaceTangentPath wave actual)
    have pairingContinuous : Continuous
        (fun pair : ComplexCoordinateVector × ComplexCoordinateVector =>
          2 * complexCoordinateRealInner pair.1 pair.2) :=
      continuous_const.mul complexCoordinateRealInner_prod_continuous
    have scaledTendsto : Tendsto scaled (𝓝[>] (0 : Real))
        (𝓝 (2 * complexCoordinateVectorNormSq q)) := by
      have paired := pairingContinuous.continuousAt.tendsto.comp
        (slopeTendsto.prodMk_nhds tangentTendsto)
      simpa only [scaled, Function.comp_def,
        complexCoordinateRealInner_self] using paired
    have scaledEventually :
        ∀ᶠ actual in 𝓝[>] (0 : Real),
          complexCoordinateVectorNormSq q < scaled actual :=
      scaledTendsto.eventually
        (eventually_gt_nhds (by linarith :
          complexCoordinateVectorNormSq q <
            2 * complexCoordinateVectorNormSq q))
    filter_upwards [scaledEventually, self_mem_nhdsWithin] with
        actual scaledLower actualPos
    have actualPos' : 0 < actual := actualPos
    have scaledIdentity :
        actual * scaled actual =
          stackedChildFaceNetPowerPath wave actual := by
      unfold scaled stackedChildFaceNetPowerPath
      rw [complexCoordinateRealInner_real_smul_left_child]
      field_simp [ne_of_gt actualPos']
    have scaledPos : 0 < scaled actual := qNormPos.trans scaledLower
    rw [← scaledIdentity]
    exact mul_pos actualPos' scaledPos
  have axis := rowEventually butterflyFirstStackAxisEight (by simp
    [butterflyFirstStackChildFaceModes])
  have plus := rowEventually butterflyFirstStackAxisEightPlusY (by simp
    [butterflyFirstStackChildFaceModes])
  have minus := rowEventually butterflyFirstStackAxisEightMinusY (by simp
    [butterflyFirstStackChildFaceModes])
  filter_upwards [axis, plus, minus] with actual axisPos plusPos minusPos
  intro wave waveMem
  simp only [butterflyFirstStackChildFaceModes, Finset.mem_insert,
    Finset.mem_singleton] at waveMem
  rcases waveMem with rfl | rfl | rfl
  · exact axisPos
  · exact plusPos
  · exact minusPos

theorem exists_stackedChildFaceNetPowerTime :
    ∃ epsilon : Real, 0 < epsilon ∧
      ∀ actual : Real, 0 < actual → actual < epsilon →
        ∀ wave ∈ butterflyFirstStackChildFaceModes,
          0 < stackedChildFaceNetPowerPath wave actual := by
  have nearZero := eventually_nhdsWithin_iff.mp
    stackedChildFaceNetPowerPath_eventually_pos
  obtain ⟨epsilon, epsilonPos, withinBall⟩ :=
    Metric.eventually_nhds_iff.mp nearZero
  refine ⟨epsilon, epsilonPos, ?_⟩
  intro actual actualPos actualLt
  apply withinBall
  · rw [Real.dist_eq, sub_zero, abs_of_pos actualPos]
    exact actualLt
  · exact actualPos

noncomputable def stackedChildFaceNetPowerTime : Real :=
  Classical.choose exists_stackedChildFaceNetPowerTime

theorem stackedChildFaceNetPowerTime_pos :
    0 < stackedChildFaceNetPowerTime :=
  (Classical.choose_spec exists_stackedChildFaceNetPowerTime).1

def stackedChildFaceSourceWindow : Real :=
  min stackedChildFacePersistenceTime stackedChildFaceNetPowerTime

theorem stackedChildFaceSourceWindow_pos :
    0 < stackedChildFaceSourceWindow :=
  lt_min stackedChildFacePersistenceTime_pos
    stackedChildFaceNetPowerTime_pos

def stackedCompleteSourceWindow : Real :=
  min stackedChildFaceSourceWindow stackedReceiptWholePowerTime

theorem stackedCompleteSourceWindow_pos :
    0 < stackedCompleteSourceWindow :=
  lt_min stackedChildFaceSourceWindow_pos
    stackedReceiptWholePowerTime_pos

def stackedShortDuration : Real :=
  min
      (min (wholeRestartDuration stackedPhysicalSeed)
        stackedSourcePatchTime)
      stackedCompleteSourceWindow / 2

theorem stackedShortDuration_pos : 0 < stackedShortDuration := by
  unfold stackedShortDuration
  exact half_pos (lt_min
    (lt_min (wholeRestartDuration_pos stackedPhysicalSeed)
      stackedSourcePatchTime_pos)
    stackedCompleteSourceWindow_pos)

theorem stackedShortDuration_lt_completeSourceWindow :
    stackedShortDuration < stackedCompleteSourceWindow := by
  unfold stackedShortDuration
  exact (half_lt_self (lt_min
    (lt_min (wholeRestartDuration_pos stackedPhysicalSeed)
      stackedSourcePatchTime_pos)
    stackedCompleteSourceWindow_pos)).trans_le (min_le_right _ _)

theorem stackedShortDuration_le_full :
    stackedShortDuration ≤ wholeRestartDuration stackedPhysicalSeed := by
  unfold stackedShortDuration
  exact (half_le_self (lt_min
    (lt_min (wholeRestartDuration_pos stackedPhysicalSeed)
      stackedSourcePatchTime_pos)
    stackedCompleteSourceWindow_pos).le).trans
      ((min_le_left _ _).trans (min_le_left _ _))

theorem stackedShortDuration_lt_patch :
    stackedShortDuration < stackedSourcePatchTime := by
  unfold stackedShortDuration
  exact (half_lt_self (lt_min
    (lt_min (wholeRestartDuration_pos stackedPhysicalSeed)
      stackedSourcePatchTime_pos)
    stackedCompleteSourceWindow_pos)).trans_le
      ((min_le_left _ _).trans (min_le_right _ _))

theorem stackedShortDuration_lt_axisEightPersistence :
    stackedShortDuration < stackedAxisEightPersistenceTime := by
  exact stackedShortDuration_lt_completeSourceWindow.trans_le
    ((min_le_left _ _).trans
      ((min_le_left _ _).trans (by
        unfold stackedChildFacePersistenceTime
        exact min_le_left _ _)))

theorem stackedShortDuration_lt_axisEightPlusYPersistence :
    stackedShortDuration < stackedAxisEightPlusYPersistenceTime := by
  exact stackedShortDuration_lt_completeSourceWindow.trans_le
    ((min_le_left _ _).trans
      ((min_le_left _ _).trans (by
        unfold stackedChildFacePersistenceTime
        exact (min_le_right _ _).trans (min_le_left _ _))))

theorem stackedShortDuration_lt_axisEightMinusYPersistence :
    stackedShortDuration < stackedAxisEightMinusYPersistenceTime := by
  exact stackedShortDuration_lt_completeSourceWindow.trans_le
    ((min_le_left _ _).trans
      ((min_le_left _ _).trans (by
        unfold stackedChildFacePersistenceTime
        exact (min_le_right _ _).trans (min_le_right _ _))))

theorem stackedShortDuration_lt_childFaceNetPowerTime :
    stackedShortDuration < stackedChildFaceNetPowerTime := by
  exact stackedShortDuration_lt_completeSourceWindow.trans_le
    ((min_le_left _ _).trans (min_le_right _ _))

theorem stackedShortDuration_lt_wholePowerTime :
    stackedShortDuration < stackedReceiptWholePowerTime := by
  exact stackedShortDuration_lt_completeSourceWindow.trans_le
    (min_le_right _ _)

def stackedShortReceipt : WholeContinuousMildSerrinReceipt
    butterflyGainViscosity stackedSeedState stackedShortDuration :=
  restrictWholeContinuousMildSerrinReceipt stackedShortDuration_pos
    stackedShortDuration_le_full stackedReceipt

def stackedShortContact :=
  generatedPositiveWholeRestartContact stackedShortReceipt

def stackedShortCurrent :
    GeneratedWholeRestartCurrent butterflyGainViscosity where
  initialState := stackedSeedState
  duration := stackedShortDuration
  receipt := stackedShortReceipt
  contact := stackedShortContact

def stackedShortContactFullTime :
    Icc (0 : Real) (wholeRestartDuration stackedPhysicalSeed) :=
  commonTimeInclusion stackedShortDuration_le_full stackedShortContact.time

theorem stackedShortContact_state_eq_full :
    stackedShortContact.physicalState =
    stackedReceipt.wholePath stackedShortContactFullTime := rfl

theorem stackedShortContact_wholePower_gt_three :
    (3 : Real) < stackedReceiptWholePowerAt stackedShortContact.time.1 := by
  exact stackedReceiptWholePowerTime_spec
    stackedShortContact.time.1 stackedShortContact.time_pos
    (stackedShortContact.time.2.2.trans_lt
      stackedShortDuration_lt_wholePowerTime)

/-- The selected complete-source power becomes the literal time-zero
instruction of the generated successor receipt. -/
theorem stackedShortCurrent_nextReceipt_wholePower_zero_gt_three :
    (3 : Real) < actualProjectedWholeNetEnstrophyPower
      stackedShortCurrent.nextReceipt butterflyFirstStackModes 0 := by
  have sourcePower := stackedShortContact_wholePower_gt_three
  unfold stackedReceiptWholePowerAt at sourcePower
  have nextStateZero :
      (actualWholeProjectedTransversePath
        stackedShortCurrent.nextReceipt 0).1 =
          stackedShortContact.physicalState := by
    change stackedShortCurrent.nextReceipt.wholePath
        (Set.projIcc (0 : Real)
          (wholeRestartDuration stackedShortCurrent.contact)
          stackedShortCurrent.nextReceipt.requestedTimePos.le 0) = _
    rw [Set.projIcc_of_mem
      stackedShortCurrent.nextReceipt.requestedTimePos.le
      ⟨le_rfl, stackedShortCurrent.nextReceipt.requestedTimePos.le⟩]
    exact stackedShortCurrent.nextReceipt.wholePath_initial
  have sourceState :
      (actualWholeProjectedTransversePath stackedReceipt
        stackedShortContact.time.1).1 =
          stackedShortContact.physicalState := by
    have timeMem : stackedShortContact.time.1 ∈
        Set.Icc (0 : Real) (wholeRestartDuration stackedPhysicalSeed) :=
      ⟨stackedShortContact.time_pos.le,
        stackedShortContact.time.2.2.trans stackedShortDuration_le_full⟩
    change stackedReceipt.wholePath
        (Set.projIcc (0 : Real)
          (wholeRestartDuration stackedPhysicalSeed)
          (wholeRestartDuration_pos stackedPhysicalSeed).le
          stackedShortContact.time.1) = _
    rw [Set.projIcc_of_mem
      (wholeRestartDuration_pos stackedPhysicalSeed).le
      timeMem]
    change stackedReceipt.wholePath
      (⟨stackedShortContact.time.1, timeMem⟩ :
        Set.Icc (0 : Real) (wholeRestartDuration stackedPhysicalSeed)) = _
    convert stackedShortContact_state_eq_full.symm using 1
    apply Subtype.ext
    rfl
  have powerEq :
      actualProjectedWholeNetEnstrophyPower
          stackedShortCurrent.nextReceipt butterflyFirstStackModes 0 =
        actualProjectedWholeNetEnstrophyPower stackedReceipt
          butterflyFirstStackModes stackedShortContact.time.1 := by
    unfold actualProjectedWholeNetEnstrophyPower
      actualProjectedWholeEnstrophyPower
      actualProjectedWholeViscousEnstrophyPower
    rw [nextStateZero, sourceState]
  rwa [powerEq]

/-- The source-selected actual current already owns the first generated
dyadic receiver.  The seed row at `axisWave 8` is zero, so this is genuine
PDE-generated material rather than a retained table entry. -/
theorem stackedShortContact_axisEight_ne_zero :
    stackedShortContact.physicalState butterflyFirstStackAxisEight ≠ 0 := by
  have axisNe : butterflyFirstStackAxisEight ≠ 0 := by decide
  have generated :=
    (Classical.choose_spec exists_stackedAxisEightPersistenceTime).2
      stackedShortContact.time.1 stackedShortContact.time_pos
      (stackedShortContact.time.2.2.trans_lt
        stackedShortDuration_lt_axisEightPersistence)
  have pathEq := wholePath_wave_eq_actualWholeContinuousHeatDuhamelPath
    stackedReceipt butterflyFirstStackAxisEight axisNe
      stackedShortContactFullTime
  rw [stackedShortContact_state_eq_full, pathEq]
  exact generated

theorem stackedShortContact_axisEightPlusY_ne_zero :
    stackedShortContact.physicalState
      butterflyFirstStackAxisEightPlusY ≠ 0 := by
  have waveNe : butterflyFirstStackAxisEightPlusY ≠ 0 := by decide
  have generated :=
    (Classical.choose_spec exists_stackedAxisEightPlusYPersistenceTime).2
      stackedShortContact.time.1 stackedShortContact.time_pos
      (stackedShortContact.time.2.2.trans_lt
        stackedShortDuration_lt_axisEightPlusYPersistence)
  have pathEq := wholePath_wave_eq_actualWholeContinuousHeatDuhamelPath
    stackedReceipt butterflyFirstStackAxisEightPlusY waveNe
      stackedShortContactFullTime
  rw [stackedShortContact_state_eq_full, pathEq]
  exact generated

theorem stackedShortContact_axisEightMinusY_ne_zero :
    stackedShortContact.physicalState
      butterflyFirstStackAxisEightMinusY ≠ 0 := by
  have waveNe : butterflyFirstStackAxisEightMinusY ≠ 0 := by decide
  have generated :=
    (Classical.choose_spec exists_stackedAxisEightMinusYPersistenceTime).2
      stackedShortContact.time.1 stackedShortContact.time_pos
      (stackedShortContact.time.2.2.trans_lt
        stackedShortDuration_lt_axisEightMinusYPersistence)
  have pathEq := wholePath_wave_eq_actualWholeContinuousHeatDuhamelPath
    stackedReceipt butterflyFirstStackAxisEightMinusY waveNe
      stackedShortContactFullTime
  rw [stackedShortContact_state_eq_full, pathEq]
  exact generated

/-- The concrete root contact now owns the complete first child face rather
than a single receiver row. -/
theorem stackedShortContact_childFace_active :
    stackedShortContact.physicalState butterflyFirstStackAxisEight ≠ 0 ∧
      stackedShortContact.physicalState
          butterflyFirstStackAxisEightPlusY ≠ 0 ∧
      stackedShortContact.physicalState
          butterflyFirstStackAxisEightMinusY ≠ 0 :=
  ⟨stackedShortContact_axisEight_ne_zero,
    stackedShortContact_axisEightPlusY_ne_zero,
    stackedShortContact_axisEightMinusY_ne_zero⟩

/-- The source selector now preserves the quantitative valuation of the
same three generated rows.  This is the actual selected contact used by the
restart emitter and whole ledger. -/
theorem stackedShortContact_childFace_netPower_pos :
    ∀ wave ∈ butterflyFirstStackChildFaceModes,
      0 < instantaneousWholeNetPowerRow butterflyGainViscosity
        stackedShortCurrent.contact.physicalState wave := by
  intro wave waveMem
  have pathPositive :=
    (Classical.choose_spec exists_stackedChildFaceNetPowerTime).2
      stackedShortContact.time.1 stackedShortContact.time_pos
      (stackedShortContact.time.2.2.trans_lt
        stackedShortDuration_lt_childFaceNetPowerTime)
      wave waveMem
  change 0 < stackedChildFaceNetPowerPath wave
    stackedShortContact.time.1 at pathPositive
  have waveNe : wave ≠ 0 := by
    simp only [butterflyFirstStackChildFaceModes, Finset.mem_insert,
      Finset.mem_singleton] at waveMem
    rcases waveMem with rfl | rfl | rfl <;> decide
  have stateRowEq :
      stackedChildFaceStatePath wave stackedShortContact.time.1 =
        stackedReceipt.wholePath stackedShortContactFullTime wave := by
    symm
    exact wholePath_wave_eq_actualWholeContinuousHeatDuhamelPath
      stackedReceipt wave waveNe stackedShortContactFullTime
  have projectedStateEq :
      (actualWholeProjectedTransversePath stackedReceipt
        stackedShortContact.time.1).1 =
        stackedReceipt.wholePath stackedShortContactFullTime := by
    change stackedReceipt.wholePath
        (Set.projIcc (0 : Real)
          (wholeRestartDuration stackedPhysicalSeed)
          (wholeRestartDuration_pos stackedPhysicalSeed).le
          stackedShortContact.time.1) = _
    have timeMem : stackedShortContact.time.1 ∈
        Icc (0 : Real) (wholeRestartDuration stackedPhysicalSeed) :=
      ⟨stackedShortContact.time_pos.le,
        stackedShortContact.time.2.2.trans stackedShortDuration_le_full⟩
    rw [Set.projIcc_of_mem
      (wholeRestartDuration_pos stackedPhysicalSeed).le timeMem]
    congr 1
  change 0 < instantaneousWholeNetPowerRow butterflyGainViscosity
    stackedShortContact.physicalState wave
  rw [stackedShortContact_state_eq_full]
  unfold stackedChildFaceNetPowerPath stackedChildFaceTangentPath at pathPositive
  unfold actualWholeContinuousNonlinearRow at pathPositive
  rw [stateRowEq, projectedStateEq] at pathPositive
  rw [complexCoordinateRealInner_sub_right] at pathPositive
  unfold instantaneousWholeNetPowerRow
  linarith

theorem stackedShortContact_sourcePatch :
    86 < wholeVorticityEuclideanMass
        stackedShortCurrent.contact.physicalState ∧
      wholeVorticityEuclideanMass
          stackedShortCurrent.contact.physicalState < 87 ∧
      ∀ wave ∈ stackedSidebandModes,
        15 < sourceReserveAt
            stackedShortCurrent.contact.physicalState wave ∧
          10 < sourceTangentWorkAt
            stackedShortCurrent.contact.physicalState wave ∧
          12 < selfTangentWorkAt
            stackedShortCurrent.contact.physicalState wave := by
  have generated :=
    (Classical.choose_spec exists_stackedSourcePatch).2
      stackedShortContactFullTime
      (stackedShortContact.time.2.2.trans_lt stackedShortDuration_lt_patch)
  rw [StackedSourcePatchAt] at generated
  unfold receiptReserveAt receiptTangentWorkAt
    receiptSelfTangentWorkAt at generated
  change
    86 < wholeVorticityEuclideanMass stackedShortContact.physicalState ∧
      wholeVorticityEuclideanMass stackedShortContact.physicalState < 87 ∧
      ∀ wave ∈ stackedSidebandModes,
        15 < sourceReserveAt stackedShortContact.physicalState wave ∧
        10 < sourceTangentWorkAt stackedShortContact.physicalState wave ∧
        12 < selfTangentWorkAt stackedShortContact.physicalState wave
  rw [stackedShortContact_state_eq_full]
  exact generated

theorem stackedShortCurrent_level_eq_eighty_eight :
    wholeRestartCoefficientLevel stackedShortCurrent.contact = 88 := by
  unfold wholeRestartCoefficientLevel wholeRestartRawCoefficientCeiling
  rw [Nat.ceil_eq_iff (by norm_num : (88 : Nat) ≠ 0)]
  norm_num
  constructor <;> linarith [stackedShortContact_sourcePatch.1,
    stackedShortContact_sourcePatch.2.1]

theorem stackedShortCurrent_ceiling_eq_eighty_eight :
    wholeRestartCoefficientCeiling stackedShortCurrent.contact = 88 := by
  unfold wholeRestartCoefficientCeiling
  rw [stackedShortCurrent_level_eq_eighty_eight]
  norm_num

theorem butterflyGainBarrierSeventhCoefficient_gt_one :
    1 < sourceOwnedWholeStateBarrierSeventhCoefficient
      butterflyGainViscosity := by
  unfold sourceOwnedWholeStateBarrierSeventhCoefficient
    sourceOwnedLocalQuadraticFifthCoefficient
    sourceOwnedLocalKernelRadiusSlope
    biotSavartSerrinConstant
    butterflyGainViscosity
  field_simp [Real.pi_ne_zero]
  norm_num

theorem stackedSideband_integerWaveNormSq_eq
    (wave : IntegerWavevector)
    (waveMem : wave ∈ stackedSidebandModes) :
    integerWaveNormSq wave = 17 := by
  simp only [stackedSidebandModes, plusSideband, minusSideband,
    Finset.mem_insert, Finset.mem_singleton] at waveMem
  rcases waveMem with rfl | rfl <;>
    simp [integerWaveNormSq, axisWave, pumpY, Fin.sum_univ_succ] <;>
    norm_num

theorem stackedSideband_inverseSixthUpper_lt_one
    (wave : IntegerWavevector)
    (waveMem : wave ∈ stackedSidebandModes) :
    fullReplayEulerTubeInverseSixthUpper stackedShortCurrent wave < 1 := by
  have waveNormSq := stackedSideband_integerWaveNormSq_eq wave waveMem
  have viscousMultiplier :
      butterflyGainViscosity.coeff * integerWaveViscousMultiplier wave =
        (17 / 100 : Real) := by
    unfold integerWaveViscousMultiplier
    rw [waveNormSq]
    calc
      butterflyGainViscosity.coeff * ((2 * Real.pi) ^ 2 * 17) =
          (butterflyGainViscosity.coeff * (2 * Real.pi) ^ 2) * 17 := by ring
      _ = (1 / 100 : Real) * 17 := by
        rw [butterflyGainViscosity_scaled]
        norm_num
      _ = 17 / 100 := by ring
  have sqrtLe : Real.sqrt (17 : Real) ≤ 17 :=
    Real.sqrt_le_self_iff.mpr (Or.inr (by norm_num))
  unfold fullReplayEulerTubeInverseSixthUpper
  rw [stackedShortCurrent_ceiling_eq_eighty_eight,
    waveNormSq, viscousMultiplier]
  apply (div_lt_one (mul_pos
    (sourceOwnedWholeStateBarrierSeventhCoefficient_pos _)
    (pow_pos (by norm_num) 6))).2
  nlinarith [butterflyGainBarrierSeventhCoefficient_gt_one]

theorem stackedSideband_axis_norm_lt_four
    (wave : IntegerWavevector)
    (waveMem : wave ∈ stackedSidebandModes) :
    ‖stackedSidebandCone.axis wave‖ < 4 := by
  have waveEq : wave = axisWave 4 + pumpY ∨
      wave = axisWave 4 - pumpY := by
    simpa only [stackedSidebandModes, plusSideband, minusSideband,
      Finset.mem_insert, Finset.mem_singleton] using waveMem
  have amplitude :=
    butterflyFirstStackPhysicalState_negOne_sideband_mass_eq wave waveEq
  change complexCoordinateAmplitudeSq (stackedSeedState wave) = 121 / 8
    at amplitude
  have normSqLe := complexCoordinateVector_norm_sq_le_amplitudeSq
    (stackedSeedState wave)
  change ‖stackedSeedState wave‖ < 4
  change ‖stackedSeedState wave‖ ^ 2 ≤ _ at normSqLe
  have bound : ‖stackedSeedState wave‖ ^ 2 ≤ 121 / 8 :=
    normSqLe.trans_eq amplitude
  nlinarith [norm_nonneg (stackedSeedState wave), bound]

/-- The actual selected current, not the rational seed, owns the full-horizon
source margin on its two paying sidebands. -/
theorem stackedShortCurrent_inverseSixthMargin :
    fullReplayPhaseConeHasInverseSixthMargin
      stackedSidebandCone stackedShortCurrent := by
  intro wave waveMem
  have patch := stackedShortContact_sourcePatch.2.2 wave waveMem
  have workPositive :
      0 ≤ complexCoordinateRealInner
        (stackedSidebandCone.axis wave)
        (wholeLatticeVorticityFourierTangentAt
          butterflyGainViscosity.coeff
          stackedShortCurrent.contact.physicalState wave) := by
    change 0 ≤ sourceTangentWorkAt
      stackedShortCurrent.contact.physicalState wave
    linarith [patch.2.1]
  refine ⟨workPositive, ?_⟩
  have upperNonneg : 0 ≤
      fullReplayEulerTubeInverseSixthUpper stackedShortCurrent wave := by
    unfold fullReplayEulerTubeInverseSixthUpper
    apply div_nonneg
    · exact add_nonneg (by positivity)
        (mul_nonneg butterflyGainViscosity.coeff_pos.le
          (by
            unfold integerWaveViscousMultiplier
            exact mul_nonneg (sq_nonneg _)
              (integerWaveNormSq_nonneg wave)))
    · exact mul_nonneg
        (sourceOwnedWholeStateBarrierSeventhCoefficient_pos _).le
        (pow_nonneg
          (wholeRestartCoefficientCeiling_pos _).le 6)
  have upperLt := stackedSideband_inverseSixthUpper_lt_one wave waveMem
  have axisNormLt := stackedSideband_axis_norm_lt_four wave waveMem
  have sourceReserve : 15 <
      complexCoordinateRealInner (stackedSidebandCone.axis wave)
        (stackedShortCurrent.contact.physicalState wave) := by
    exact patch.1
  nlinarith [norm_nonneg (stackedSidebandCone.axis wave)]

/-- First actual recurrence step: the same source-generated phase cone holds
at every point of the unchanged canonical successor receipt. -/
theorem stackedShortCurrent_fullReceipt_sidebandCone
    (time : Icc (0 : Real)
      (wholeRestartDuration stackedShortCurrent.contact)) :
    stackedSidebandCone.Holds
      (stackedShortCurrent.nextReceipt.wholePath time) := by
  apply finiteFourierPhaseCone_fullReceipt_holds_of_eulerMargin
  exact fullReplayPhaseConeHasEulerMargin_of_sourceMargin
    stackedSidebandCone stackedShortCurrent
    (fullReplayPhaseConeHasSourceMargin_of_inverseSixth
      stackedSidebandCone stackedShortCurrent
      stackedShortCurrent_inverseSixthMargin)

theorem stackedShortCurrent_nextContact_sidebandCone :
    stackedSidebandCone.Holds
      stackedShortCurrent.nextContact.physicalState := by
  exact stackedShortCurrent_fullReceipt_sidebandCone
    stackedShortCurrent.nextContact.time

end
end ButterflyStackedSourceCurrent
end RationalVorticityEvaluator
end NavierStokes
end SaturationMonoid
