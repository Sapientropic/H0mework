import H0mework.NavierStokes.Butterfly.NextPairMaterial
import H0mework.NavierStokes.Crossing.TangentCoercivity
import H0mework.NavierStokes.Restart.PreQuotientNonlinearWork
import H0mework.NavierStokes.Crossing.MassPersistence
import H0mework.NavierStokes.Fourier.WholeVelocityPairDiagonalBudget
import H0mework.NavierStokes.KineticRestart.KineticDefectZeroVelocityCompletion

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.RationalVorticityEvaluator

open scoped BigOperators ENNReal Topology Interval
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedPathInfiniteNonlinearNegativeOneTimeBudget
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPreQuotientNonlinearWork
open ThreeDimensionalVorticityCoefficientFiniteSupportWholeActionTube
open ThreeDimensionalVorticityCoefficientWholeActionTube
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSourcePairOccurrence
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticDissipationLedger
open ThreeDimensionalVorticityCoefficientGeneratedPathInfiniteNonlinearNegativeOneTimeBudget
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientCanonicalExhaustiveGalerkinTarget
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingMassPersistence
open ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartFinitePrefixDualSquareLedger
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellWholeReceiptEnergyWriteBack
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientWholeKineticDifferenceCancellation
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticDefectZeroVelocityCompletion
open ThreeDimensionalVorticityCoefficientWholeVelocityFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientFiniteGalerkinAmbientNorm
open ThreeDimensionalVorticityCoefficientFiniteKineticDifferenceCancellation
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelKineticTriadRedirect

noncomputable section

def butterflyPhysicalTime : ℝ :=
  wholeRestartDuration (butterflyPhysicalSeed butterflyViscosity)

def butterflyPhysicalDomain : Set ℝ :=
  Set.Icc 0 butterflyPhysicalTime

def butterflyKineticPath (actual : ℝ) :=
  puncturedWholeVorticityKineticEuclideanState
    (actualWholeProjectedTransversePath
      (butterflyReceipt butterflyViscosity) actual).1

def butterflyKineticInitial :=
  puncturedWholeVorticityKineticEuclideanState
    (butterflyPhysicalState 1)

theorem butterflySeedGradientSummable :
    Summable fun wave : IntegerWavevector =>
      integerWaveNormSq wave *
        complexCoordinateAmplitudeSq (butterflyPhysicalState 1 wave) :=
  summable_wholeStateVorticityGradientDensity_of_supported
    butterflySeedModes (butterflyPhysicalState 1)
    (butterflyPhysicalState_supported 1)

def butterflyKineticTangent :=
  puncturedWholeUnforcedNegativeOneEuclideanState
    butterflyViscosity.coeff (butterflyPhysicalState 1)
    (butterflyPhysicalState_transverse 1)
    butterflySeedGradientSummable

theorem butterflyPhysicalRow_hasDerivWithinAt
    (wave : IntegerWavevector) (waveNonzero : wave ≠ 0) :
    HasDerivWithinAt
      (fun actual =>
        (actualWholeProjectedTransversePath
          (butterflyReceipt butterflyViscosity) actual).1 wave)
      (butterflyPhysicalActionState wave)
      butterflyPhysicalDomain 0 := by
  have generated :=
    actualWholeContinuousHeatDuhamelPath_hasDerivAt_zero
      (butterflyReceipt butterflyViscosity) wave
  have tangentEq :
      wholeStateVorticityNonlinearCoefficientAt
            (butterflyPhysicalState 1) wave -
          (butterflyViscosity.coeff *
            integerWaveViscousMultiplier wave) •
            butterflyPhysicalState 1 wave =
        butterflyPhysicalActionState wave := by
    rw [butterflyPhysicalActionState,
      wholeFiniteSupportActionState_apply_eq_wholeTangent
        butterflyViscosity.coeff butterflySeedModes
        (butterflyPhysicalState 1)
        (butterflyPhysicalState_supported 1) wave]
    rfl
  have generatedTangentEq :
      wholeStateVorticityNonlinearCoefficientAt
            (wholeRestartPhysicalState
              (butterflyPhysicalSeed butterflyViscosity)) wave -
          (butterflyViscosity.coeff *
            integerWaveViscousMultiplier wave) •
            wholeRestartPhysicalState
              (butterflyPhysicalSeed butterflyViscosity) wave =
        butterflyPhysicalActionState wave := by
    simpa only [butterflyPhysicalSeed_wholeState] using tangentEq
  have adjusted := generated.congr_deriv generatedTangentEq
  have pathEq : ∀ actual ∈ butterflyPhysicalDomain,
      (actualWholeProjectedTransversePath
          (butterflyReceipt butterflyViscosity) actual).1 wave =
        actualWholeContinuousHeatDuhamelPath
          (butterflyReceipt butterflyViscosity) wave actual := by
    intro actual actualMem
    have actualMem' : actual ∈ Set.Icc (0 : ℝ)
        (wholeRestartDuration
          (butterflyPhysicalSeed butterflyViscosity)) := by
      exact actualMem
    change
      (butterflyReceipt butterflyViscosity).wholePath
          (Set.projIcc 0
            (wholeRestartDuration
              (butterflyPhysicalSeed butterflyViscosity))
            (butterflyReceipt butterflyViscosity).requestedTimePos.le
            actual) wave =
        actualWholeContinuousHeatDuhamelPath
          (butterflyReceipt butterflyViscosity) wave actual
    rw [Set.projIcc_of_mem
      (butterflyReceipt butterflyViscosity).requestedTimePos.le
      actualMem']
    exact wholePath_wave_eq_actualWholeContinuousHeatDuhamelPath
      (butterflyReceipt butterflyViscosity) wave waveNonzero
      ⟨actual, actualMem'⟩
  have zeroMem : (0 : ℝ) ∈ butterflyPhysicalDomain := by
    exact ⟨le_rfl, (wholeRestartDuration_pos
      (butterflyPhysicalSeed butterflyViscosity)).le⟩
  exact adjusted.hasDerivWithinAt.congr pathEq (pathEq 0 zeroMem)

def butterflyKineticCross (actual : ℝ) : ℝ :=
  ∑ wave ∈ butterflySeedModes,
    complexCoordinateRealInner
      (finiteStateVelocityCoefficient (butterflyPhysicalState 1) wave)
      (finiteStateVelocityCoefficient
        (actualWholeProjectedTransversePath
          (butterflyReceipt butterflyViscosity) actual).1 wave)

theorem butterflyKineticCross_hasDerivWithinAt :
    HasDerivWithinAt butterflyKineticCross
      (finiteStateVorticityKineticPairing butterflySeedModes
        (butterflyPhysicalState 1) butterflyPhysicalActionState)
      butterflyPhysicalDomain 0 := by
  unfold butterflyKineticCross finiteStateVorticityKineticPairing
  apply HasDerivWithinAt.fun_sum
  intro wave waveMem
  have waveNonzero : wave ≠ 0 := fun waveZero =>
    butterflySeedModes_zero_not_mem (waveZero ▸ waveMem)
  have rowDerivative :=
    butterflyPhysicalRow_hasDerivWithinAt wave waveNonzero
  have velocityDerivative :
      HasDerivWithinAt
        (fun actual =>
          finiteStateVelocityCoefficient
            (actualWholeProjectedTransversePath
              (butterflyReceipt butterflyViscosity) actual).1 wave)
        (biotSavartVelocityCoefficient wave
          (butterflyPhysicalActionState wave))
        butterflyPhysicalDomain 0 := by
    exact (biotSavartVelocityCLM wave).hasFDerivAt.comp_hasDerivWithinAt
      0 rowDerivative
  exact
    (complexCoordinateRealInnerRightCLM
      (finiteStateVelocityCoefficient
        (butterflyPhysicalState 1) wave)).hasFDerivAt.comp_hasDerivWithinAt
      0 velocityDerivative

theorem butterflyPhysicalActionState_eq_finiteGenerator_on_seed
    (wave : IntegerWavevector) (waveMem : wave ∈ butterflySeedModes) :
    butterflyPhysicalActionState wave =
      finiteStateVorticityGenerator butterflySeedModes
        butterflyViscosity.coeff (butterflyPhysicalState 1) wave := by
  rw [butterflyPhysicalActionState,
    wholeFiniteSupportActionState_apply_eq_wholeTangent
      butterflyViscosity.coeff butterflySeedModes
      (butterflyPhysicalState 1)
      (butterflyPhysicalState_supported 1) wave]
  unfold wholeLatticeVorticityFourierTangentAt
  rw [wholeStateVorticityNonlinearCoefficientAt_eq_finite_of_supported
    butterflySeedModes (butterflyPhysicalState 1)
    (butterflyPhysicalState_supported 1) wave]
  rw [finiteStateVorticityGenerator_apply, if_pos waveMem]

theorem butterflyKineticPairing_action_eq :
    finiteStateVorticityKineticPairing butterflySeedModes
        (butterflyPhysicalState 1) butterflyPhysicalActionState =
      -butterflyViscosity.coeff *
        wholeVorticityEuclideanMass (butterflyPhysicalState 1) := by
  have actionEq :
      finiteStateVorticityKineticPairing butterflySeedModes
          (butterflyPhysicalState 1) butterflyPhysicalActionState =
        finiteStateVorticityKineticPairing butterflySeedModes
          (butterflyPhysicalState 1)
          (finiteStateVorticityGenerator butterflySeedModes
            butterflyViscosity.coeff (butterflyPhysicalState 1)) := by
    unfold finiteStateVorticityKineticPairing
    apply Finset.sum_congr rfl
    intro wave waveMem
    rw [butterflyPhysicalActionState_eq_finiteGenerator_on_seed
      wave waveMem]
  rw [actionEq]
  have cancellation := finiteStateVorticityGeneratorKineticPairing_eq
    butterflySeedModes butterflySeedModes_zero_not_mem
    (fun wave waveMem => butterflySeedModes_waveNeg_mem wave waveMem)
    butterflyViscosity.coeff (butterflyPhysicalState 1)
    (fun wave waveMem => butterflyPhysicalState_transverse 1 wave)
    (fun wave waveMem => butterflyPhysicalState_reality 1 wave)
  rw [cancellation]
  congr 1
  rw [wholeVorticityEuclideanMass_eq_finite_of_supported
    butterflySeedModes (butterflyPhysicalState 1)
    (butterflyPhysicalState_supported 1)]
  unfold finiteStateVorticityMass
    finiteStateVorticityCoefficientEnstrophy
  apply Finset.sum_congr rfl
  intro wave waveMem
  exact complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq
    (butterflyPhysicalState 1 wave)

theorem butterflyKineticCross_hasDerivWithinAt_explicit :
    HasDerivWithinAt butterflyKineticCross
      (-butterflyViscosity.coeff *
        wholeVorticityEuclideanMass (butterflyPhysicalState 1))
      butterflyPhysicalDomain 0 :=
  butterflyKineticCross_hasDerivWithinAt.congr_deriv
    butterflyKineticPairing_action_eq

def butterflyKineticMassPath (actual : ℝ) : ℝ :=
  puncturedWholeVorticityKineticMass
    (actualWholeProjectedTransversePath
      (butterflyReceipt butterflyViscosity) actual).1

def butterflyPhysicalDensity (actual : ℝ) : ℝ :=
  wholeVorticityEuclideanMass
    (wholeRestartReceiptPhysicalTrajectory
      (butterflyReceipt butterflyViscosity) actual)

theorem butterflyPhysicalDensity_continuous :
    Continuous butterflyPhysicalDensity := by
  rw [continuous_iff_continuousAt]
  intro actual
  exact tendsto_wholeVorticityEuclideanMass
    (wholeRestartReceiptPhysicalTrajectory_continuous
      (butterflyReceipt butterflyViscosity)).continuousAt

@[simp] theorem butterflyPhysicalDensity_zero :
    butterflyPhysicalDensity 0 =
      wholeVorticityEuclideanMass (butterflyPhysicalState 1) := by
  unfold butterflyPhysicalDensity
  rw [wholeRestartReceiptPhysicalTrajectory_zero]
  rfl

theorem butterflyKineticMassPath_eq_energyTrace
    (actual : ℝ) (actualMem : actual ∈ butterflyPhysicalDomain) :
    butterflyKineticMassPath actual =
      puncturedWholeVorticityKineticMass (butterflyPhysicalState 1) -
        2 * butterflyViscosity.coeff *
          ∫ earlier in (0 : ℝ)..actual,
            butterflyPhysicalDensity earlier := by
  have actualMem' :
      actual ∈ Set.Icc (0 : ℝ)
        (wholeRestartDuration
          (butterflyPhysicalSeed butterflyViscosity)) := by
    simpa only [butterflyPhysicalDomain, butterflyPhysicalTime] using actualMem
  let time : Set.Icc (0 : ℝ)
      (wholeRestartDuration
        (butterflyPhysicalSeed butterflyViscosity)) :=
    ⟨actual, actualMem'⟩
  have ledger :=
    generatedWholeRestartWholeContinuousMildSerrinReceipt_kineticDissipation_eq
      (butterflyReplay butterflyViscosity) time
  have prefixEq :=
    wholePrefixVorticityMass_receipt_eq_intervalIntegral
      (butterflyReceipt butterflyViscosity) time
  have projectionEq :
      (actualWholeProjectedTransversePath
        (butterflyReceipt butterflyViscosity) actual).1 =
        (butterflyReceipt butterflyViscosity).wholePath time := by
    change
      (butterflyReceipt butterflyViscosity).wholePath
          (Set.projIcc 0
            (wholeRestartDuration
              (butterflyPhysicalSeed butterflyViscosity))
            (butterflyReceipt butterflyViscosity).requestedTimePos.le
            actual) =
        (butterflyReceipt butterflyViscosity).wholePath time
    rw [Set.projIcc_of_mem
      (butterflyReceipt butterflyViscosity).requestedTimePos.le actualMem']
  change
    puncturedWholeVorticityKineticMass
          ((butterflyReceipt butterflyViscosity).wholePath time) +
        2 * butterflyViscosity.coeff *
          wholePrefixVorticityMass time
            (butterflyReceipt butterflyViscosity).stateLimit =
      puncturedWholeVorticityKineticMass
        (wholeRestartPhysicalState
          (butterflyPhysicalSeed butterflyViscosity)) at ledger
  rw [prefixEq] at ledger
  dsimp only [time] at ledger
  unfold butterflyKineticMassPath butterflyPhysicalDensity
  rw [projectionEq]
  dsimp only [time]
  simp only [butterflyPhysicalSeed_wholeState] at ledger
  rw [eq_sub_iff_add_eq]
  exact ledger

theorem butterflyKineticMassPath_hasDerivWithinAt :
    HasDerivWithinAt butterflyKineticMassPath
      (-2 * butterflyViscosity.coeff *
        wholeVorticityEuclideanMass (butterflyPhysicalState 1))
      butterflyPhysicalDomain 0 := by
  have integralDerivative :
      HasDerivAt
        (fun actual =>
          ∫ earlier in (0 : ℝ)..actual,
            butterflyPhysicalDensity earlier)
        (butterflyPhysicalDensity 0) 0 :=
    intervalIntegral.integral_hasDerivAt_right
      (butterflyPhysicalDensity_continuous.intervalIntegrable 0 0)
      (butterflyPhysicalDensity_continuous.stronglyMeasurableAtFilter
        volume (nhds 0))
      butterflyPhysicalDensity_continuous.continuousAt
  have traceDerivative :=
    (integralDerivative.const_mul
      (-2 * butterflyViscosity.coeff)).const_add
        (puncturedWholeVorticityKineticMass
          (butterflyPhysicalState 1))
  have traceWithin :
      HasDerivWithinAt
        (fun actual =>
          puncturedWholeVorticityKineticMass
              (butterflyPhysicalState 1) +
            -2 * butterflyViscosity.coeff *
              ∫ earlier in (0 : ℝ)..actual,
                butterflyPhysicalDensity earlier)
        (-2 * butterflyViscosity.coeff * butterflyPhysicalDensity 0)
        butterflyPhysicalDomain 0 :=
    traceDerivative.hasDerivWithinAt
  have traceWithin' :
      HasDerivWithinAt
        (fun actual =>
          puncturedWholeVorticityKineticMass
              (butterflyPhysicalState 1) +
            -2 * butterflyViscosity.coeff *
              ∫ earlier in (0 : ℝ)..actual,
                butterflyPhysicalDensity earlier)
        (-2 * butterflyViscosity.coeff *
          wholeVorticityEuclideanMass (butterflyPhysicalState 1))
        butterflyPhysicalDomain 0 :=
    traceWithin.congr_deriv (by
      rw [butterflyPhysicalDensity_zero])
  apply traceWithin'.congr
  · intro actual actualMem
    rw [butterflyKineticMassPath_eq_energyTrace actual actualMem]
    ring
  · rw [butterflyKineticMassPath_eq_energyTrace 0]
    ring
    exact ⟨le_rfl, (wholeRestartDuration_pos
      (butterflyPhysicalSeed butterflyViscosity)).le⟩

theorem puncturedKineticCoefficient_re_inner_eq_div
    (left right : ComplexVorticityHilbertState)
    (wave : NonzeroIntegerWavevector) :
    (inner ℂ
        (puncturedWholeVorticityKineticEuclideanCoefficient left wave)
        (puncturedWholeVorticityKineticEuclideanCoefficient right wave)).re =
      complexCoordinateRealInner (left wave.1) (right wave.1) /
        integerWaveViscousMultiplier wave.1 := by
  have multiplierPos :
      0 < integerWaveViscousMultiplier wave.1 :=
    integerWaveViscousMultiplier_pos wave
  have multiplierNe :
      integerWaveViscousMultiplier wave.1 ≠ 0 := multiplierPos.ne'
  have sqrtPos :
      0 < Real.sqrt (integerWaveViscousMultiplier wave.1) :=
    Real.sqrt_pos.2 multiplierPos
  change
    (inner ℂ
      ((Real.sqrt (integerWaveViscousMultiplier wave.1))⁻¹ •
        euclideanCoordinateRow (left wave.1))
      ((Real.sqrt (integerWaveViscousMultiplier wave.1))⁻¹ •
        euclideanCoordinateRow (right wave.1))).re = _
  generalize hLeft : left wave.1 = leftRow at *
  generalize hRight : right wave.1 = rightRow at *
  generalize hMultiplier :
    integerWaveViscousMultiplier wave.1 = multiplier at *
  generalize hRoot : Real.sqrt multiplier = root at *
  generalize hInverseRoot : root⁻¹ = inverseRoot at *
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  rw [inner_smul_left, inner_smul_right]
  generalize hRowInner :
    inner ℂ (euclideanCoordinateRow leftRow)
      (euclideanCoordinateRow rightRow) = rowInner at *
  have conjugateScalar :
      starRingEnd ℂ (inverseRoot : ℂ) = (inverseRoot : ℂ) := by simp
  have normalizedProduct :
      starRingEnd ℂ (inverseRoot : ℂ) *
          ((inverseRoot : ℂ) * rowInner) =
        ((inverseRoot : ℂ) * (inverseRoot : ℂ)) * rowInner := by
    rw [conjugateScalar]
    ring
  have scalarSquare :
      (inverseRoot : ℂ) * (inverseRoot : ℂ) =
        ((1 / multiplier : ℝ) : ℂ) := by
    norm_cast
    rw [← hInverseRoot, ← hRoot]
    field_simp [sqrtPos.ne', multiplierNe]
    rw [Real.sq_sqrt multiplierPos.le]
  have rowInnerRe :
      rowInner.re = complexCoordinateRealInner leftRow rightRow := by
    rw [← hRowInner]
    exact euclideanCoordinateRow_re_inner _ _
  calc
    (starRingEnd ℂ (inverseRoot : ℂ) *
        ((inverseRoot : ℂ) * rowInner)).re =
        (((inverseRoot : ℂ) * (inverseRoot : ℂ)) * rowInner).re :=
      congrArg Complex.re normalizedProduct
    _ = (((1 / multiplier : ℝ) : ℂ) * rowInner).re := by
      rw [scalarSquare]
    _ = (1 / multiplier) * rowInner.re := by
      rw [Complex.mul_re]
      simp
    _ = complexCoordinateRealInner leftRow rightRow / multiplier := by
      rw [rowInnerRe]
      ring

theorem puncturedKineticCoefficient_re_inner_eq_velocity
    (left right : ComplexVorticityHilbertState)
    (wave : NonzeroIntegerWavevector)
    (leftTransverse : complexWavevector wave.1 ⬝ᵥ left wave.1 = 0) :
    (inner ℂ
        (puncturedWholeVorticityKineticEuclideanCoefficient left wave)
        (puncturedWholeVorticityKineticEuclideanCoefficient right wave)).re =
      complexCoordinateRealInner
        (finiteStateVelocityCoefficient left wave.1)
        (finiteStateVelocityCoefficient right wave.1) := by
  rw [puncturedKineticCoefficient_re_inner_eq_div]
  exact (complexCoordinateRealInner_biotSavartVelocityCoefficient
    wave.1 wave.2 (left wave.1) (right wave.1) leftTransverse).symm

def butterflySeedNonzeroEmbedding :
    {wave // wave ∈ butterflySeedModes} ↪ NonzeroIntegerWavevector where
  toFun wave :=
    ⟨wave.1, fun waveZero =>
      butterflySeedModes_zero_not_mem (waveZero ▸ wave.2)⟩
  inj' := by
    intro left right equal
    exact Subtype.ext
      (congrArg (fun wave : NonzeroIntegerWavevector => wave.1) equal)

def butterflySeedNonzeroModes : Finset NonzeroIntegerWavevector :=
  butterflySeedModes.attach.map butterflySeedNonzeroEmbedding

theorem mem_butterflySeedNonzeroModes
    (wave : NonzeroIntegerWavevector) :
    wave ∈ butterflySeedNonzeroModes ↔ wave.1 ∈ butterflySeedModes := by
  constructor
  · intro waveMem
    rw [butterflySeedNonzeroModes, Finset.mem_map] at waveMem
    obtain ⟨source, sourceMem, sourceEq⟩ := waveMem
    have valueEq : source.1 = wave.1 :=
      congrArg Subtype.val sourceEq
    exact valueEq ▸ source.2
  · intro waveMem
    rw [butterflySeedNonzeroModes, Finset.mem_map]
    refine ⟨⟨wave.1, waveMem⟩, by simp, ?_⟩
    apply Subtype.ext
    rfl

theorem butterflyKineticInner_eq_cross (actual : ℝ) :
    (inner ℂ butterflyKineticInitial
        (butterflyKineticPath actual)).re =
      butterflyKineticCross actual := by
  rw [lp.inner_eq_tsum]
  rw [Complex.re_tsum
    (lp.summable_inner butterflyKineticInitial
      (butterflyKineticPath actual))]
  rw [tsum_eq_sum (s := butterflySeedNonzeroModes)]
  · rw [butterflySeedNonzeroModes, Finset.sum_map]
    unfold butterflyKineticCross
    rw [← Finset.sum_attach butterflySeedModes]
    apply Finset.sum_congr rfl
    intro source sourceMem
    let wave := source.1
    have waveMem : wave ∈ butterflySeedModes := source.2
    change
      (inner ℂ
        (puncturedWholeVorticityKineticEuclideanCoefficient
          (butterflyPhysicalState 1)
          (butterflySeedNonzeroEmbedding source))
        (puncturedWholeVorticityKineticEuclideanCoefficient
          (actualWholeProjectedTransversePath
            (butterflyReceipt butterflyViscosity) actual).1
          (butterflySeedNonzeroEmbedding source))).re = _
    exact puncturedKineticCoefficient_re_inner_eq_velocity
      (butterflyPhysicalState 1)
      (actualWholeProjectedTransversePath
        (butterflyReceipt butterflyViscosity) actual).1
      (butterflySeedNonzeroEmbedding source)
      (butterflyPhysicalState_transverse 1 wave)
  · intro wave waveNotMem
    have waveNotSeed : wave.1 ∉ butterflySeedModes := by
      intro waveMem
      exact waveNotMem ((mem_butterflySeedNonzeroModes wave).2 waveMem)
    have rowZero :=
      butterflyPhysicalState_supported 1 wave.1 waveNotSeed
    change
      (inner ℂ
        (puncturedWholeVorticityKineticEuclideanCoefficient
          (butterflyPhysicalState 1) wave)
        (puncturedWholeVorticityKineticEuclideanCoefficient
          (actualWholeProjectedTransversePath
            (butterflyReceipt butterflyViscosity) actual).1 wave)).re = 0
    unfold puncturedWholeVorticityKineticEuclideanCoefficient
    rw [rowZero]
    have euclideanZero :
        euclideanCoordinateRow (0 : ComplexCoordinateVector) = 0 := by
      ext coordinate
      simp
    rw [euclideanZero, smul_zero, inner_zero_left]
    rfl

def butterflyKineticIncrementSq (actual : ℝ) : ℝ :=
  ‖butterflyKineticInitial - butterflyKineticPath actual‖ ^ 2

theorem butterflyKineticIncrementSq_eq_trace (actual : ℝ) :
    butterflyKineticIncrementSq actual =
      butterflyKineticMassPath actual -
        2 * butterflyKineticCross actual +
          puncturedWholeVorticityKineticMass
            (butterflyPhysicalState 1) := by
  unfold butterflyKineticIncrementSq
  rw [norm_sub_sq (𝕜 := ℂ)]
  have innerEq :
      RCLike.re (inner ℂ butterflyKineticInitial
        (butterflyKineticPath actual)) =
        butterflyKineticCross actual := by
    change
      (inner ℂ butterflyKineticInitial
        (butterflyKineticPath actual)).re = _
    exact butterflyKineticInner_eq_cross actual
  rw [innerEq]
  unfold butterflyKineticInitial butterflyKineticPath
  rw [puncturedWholeVorticityKineticEuclideanState_norm_sq,
    puncturedWholeVorticityKineticEuclideanState_norm_sq]
  unfold butterflyKineticMassPath
  ring

theorem butterflyKineticIncrementSq_hasDerivWithinAt_zero :
    HasDerivWithinAt butterflyKineticIncrementSq 0
      butterflyPhysicalDomain 0 := by
  have doubledCrossDerivative :
      HasDerivWithinAt
        (fun actual => 2 * butterflyKineticCross actual)
        (2 * (-butterflyViscosity.coeff *
          wholeVorticityEuclideanMass (butterflyPhysicalState 1)))
        butterflyPhysicalDomain 0 := by
    exact butterflyKineticCross_hasDerivWithinAt_explicit.const_mul 2
  have subTraceDerivative :=
    butterflyKineticMassPath_hasDerivWithinAt.sub doubledCrossDerivative
  have traceDerivative := subTraceDerivative.const_add
    (puncturedWholeVorticityKineticMass (butterflyPhysicalState 1))
  have reorderedTraceDerivative :
      HasDerivWithinAt
        (fun actual =>
          butterflyKineticMassPath actual -
            2 * butterflyKineticCross actual +
              puncturedWholeVorticityKineticMass
                (butterflyPhysicalState 1))
        (-2 * butterflyViscosity.coeff *
              wholeVorticityEuclideanMass (butterflyPhysicalState 1) -
            2 * (-butterflyViscosity.coeff *
              wholeVorticityEuclideanMass (butterflyPhysicalState 1)))
        butterflyPhysicalDomain 0 := by
    apply traceDerivative.congr
    · intro actual actualMem
      dsimp
      ring
    · dsimp
      ring
  have traceDerivativeZero :
      HasDerivWithinAt
        (fun actual =>
          butterflyKineticMassPath actual -
            2 * butterflyKineticCross actual +
              puncturedWholeVorticityKineticMass
                (butterflyPhysicalState 1))
        0 butterflyPhysicalDomain 0 := by
    exact reorderedTraceDerivative.congr_deriv (by ring)
  apply traceDerivativeZero.congr
  · intro actual actualMem
    exact butterflyKineticIncrementSq_eq_trace actual
  · exact butterflyKineticIncrementSq_eq_trace 0

theorem butterflyPhysicalPath_zero :
    (actualWholeProjectedTransversePath
      (butterflyReceipt butterflyViscosity) 0).1 =
      butterflyPhysicalState 1 := by
  change
    (butterflyReceipt butterflyViscosity).wholePath
        (Set.projIcc (0 : ℝ)
          (wholeRestartDuration
            (butterflyPhysicalSeed butterflyViscosity))
          (butterflyReceipt butterflyViscosity).requestedTimePos.le 0) =
      butterflyPhysicalState 1
  rw [Set.projIcc_of_mem
    (butterflyReceipt butterflyViscosity).requestedTimePos.le
    ⟨le_rfl,
      (butterflyReceipt butterflyViscosity).requestedTimePos.le⟩]
  exact (butterflyReceipt butterflyViscosity).wholePath_initial

theorem butterflyKineticPath_zero :
    butterflyKineticPath 0 = butterflyKineticInitial := by
  unfold butterflyKineticPath butterflyKineticInitial
  rw [butterflyPhysicalPath_zero]

@[simp] theorem butterflyKineticIncrementSq_zero :
    butterflyKineticIncrementSq 0 = 0 := by
  unfold butterflyKineticIncrementSq
  rw [butterflyKineticPath_zero]
  simp

theorem butterflyKineticIncrementSq_div_tendsto_zero :
    Tendsto
      (fun actual => butterflyKineticIncrementSq actual / actual)
      (nhdsWithin 0 (butterflyPhysicalDomain \ {0}))
      (nhds 0) := by
  have slopeTendsto :=
    hasDerivWithinAt_iff_tendsto_slope.mp
      butterflyKineticIncrementSq_hasDerivWithinAt_zero
  convert slopeTendsto using 1
  funext actual
  rw [slope_def_field, butterflyKineticIncrementSq_zero]
  simp [div_eq_mul_inv, mul_comm]

theorem wholeState_norm_sq_le_euclideanMass_local
    (state : ComplexVorticityHilbertState) :
    ‖state‖ ^ 2 ≤ wholeVorticityEuclideanMass state := by
  have normSqSummable :
      Summable fun wave : IntegerWavevector => ‖state wave‖ ^ 2 := by
    simpa using
      (lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) state).summable
  have amplitudeSummable :
      Summable fun wave : IntegerWavevector =>
        complexCoordinateAmplitudeSq (state wave) :=
    (summable_vorticityRowAmplitude_sq state).congr fun wave => by
      rw [vorticityRowAmplitude_sq,
        complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
  have normIdentity :
      ‖state‖ ^ 2 =
        ∑' wave : IntegerWavevector, ‖state wave‖ ^ 2 := by
    simpa using
      (lp.norm_rpow_eq_tsum
        (p := (2 : ℝ≥0∞)) (by norm_num) state)
  rw [normIdentity]
  unfold wholeVorticityEuclideanMass
  have amplitudeIdentity :
      (∑' wave : IntegerWavevector,
          vorticityRowAmplitude state wave ^ 2) =
        ∑' wave : IntegerWavevector,
          complexCoordinateAmplitudeSq (state wave) := by
    apply tsum_congr
    intro wave
    rw [vorticityRowAmplitude_sq,
      complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
  rw [amplitudeIdentity]
  exact Summable.tsum_le_tsum
    (fun wave =>
      complexCoordinateVector_norm_sq_le_amplitudeSq (state wave))
    normSqSummable amplitudeSummable

def butterflyVelocityPath (actual : ℝ) : ComplexVorticityHilbertState :=
  wholeBiotSavartVelocityState
    (actualWholeProjectedTransversePath
      (butterflyReceipt butterflyViscosity) actual).1

def butterflyVelocityInitial : ComplexVorticityHilbertState :=
  wholeBiotSavartVelocityState (butterflyPhysicalState 1)

theorem butterflyVelocityIncrement_eq_biotSavart_sub (actual : ℝ) :
    butterflyVelocityInitial - butterflyVelocityPath actual =
      wholeBiotSavartVelocityState
        (butterflyPhysicalState 1 -
          (actualWholeProjectedTransversePath
            (butterflyReceipt butterflyViscosity) actual).1) := by
  apply lp.ext
  funext wave
  change
    finiteStateVelocityCoefficient (butterflyPhysicalState 1) wave -
        finiteStateVelocityCoefficient
          (actualWholeProjectedTransversePath
            (butterflyReceipt butterflyViscosity) actual).1 wave =
      finiteStateVelocityCoefficient
        (butterflyPhysicalState 1 -
          (actualWholeProjectedTransversePath
            (butterflyReceipt butterflyViscosity) actual).1) wave
  exact (biotSavartVelocityCoefficient_sub wave
    (butterflyPhysicalState 1 wave)
    ((actualWholeProjectedTransversePath
      (butterflyReceipt butterflyViscosity) actual).1 wave)).symm

theorem butterflyVelocityIncrement_norm_sq_le_kinetic
    (actual : ℝ) :
    ‖butterflyVelocityInitial - butterflyVelocityPath actual‖ ^ 2 ≤
      butterflyKineticIncrementSq actual := by
  let current :=
    (actualWholeProjectedTransversePath
      (butterflyReceipt butterflyViscosity) actual).1
  have differenceTransverse :
      WholeStateTransverse (butterflyPhysicalState 1 - current) :=
    wholeStateTransverse_sub
      (butterflyPhysicalState 1) current
      (butterflyPhysicalState_transverse 1)
      (actualWholeProjectedTransversePath
        (butterflyReceipt butterflyViscosity) actual).2
  calc
    ‖butterflyVelocityInitial - butterflyVelocityPath actual‖ ^ 2 ≤
        wholeVorticityEuclideanMass
          (butterflyVelocityInitial - butterflyVelocityPath actual) :=
      wholeState_norm_sq_le_euclideanMass_local _
    _ = wholeVorticityEuclideanMass
          (wholeBiotSavartVelocityState
            (butterflyPhysicalState 1 - current)) := by
      rw [butterflyVelocityIncrement_eq_biotSavart_sub]
    _ = puncturedWholeVorticityKineticMass
          (butterflyPhysicalState 1 - current) :=
      wholeVorticityEuclideanMass_wholeBiotSavartVelocityState
        _ differenceTransverse
    _ = ‖puncturedWholeVorticityKineticEuclideanState
          (butterflyPhysicalState 1 - current)‖ ^ 2 :=
      (puncturedWholeVorticityKineticEuclideanState_norm_sq _).symm
    _ = ‖butterflyKineticInitial - butterflyKineticPath actual‖ ^ 2 := by
      rw [puncturedWholeVorticityKineticEuclideanState_sub]
      rfl
    _ = butterflyKineticIncrementSq actual := rfl

def butterflyVelocityQuadraticRemainder (actual : ℝ) :
    ComplexCoordinateVector :=
  wholeStateVelocityBilinearCoefficientAt
    (butterflyVelocityPath actual - butterflyVelocityInitial)
    (butterflyVelocityPath actual - butterflyVelocityInitial)
    butterflyNextSidebandTarget

def butterflyVelocityQuadraticConstant : ℝ :=
  (6 * Real.pi) *
    Real.sqrt (integerWaveNormSq butterflyNextSidebandTarget)

theorem butterflyVelocityQuadraticConstant_nonneg :
    0 ≤ butterflyVelocityQuadraticConstant := by
  unfold butterflyVelocityQuadraticConstant
  positivity

theorem butterflyVelocityQuadraticRemainder_norm_le
    (actual : ℝ) :
    ‖butterflyVelocityQuadraticRemainder actual‖ ≤
      butterflyVelocityQuadraticConstant *
        butterflyKineticIncrementSq actual := by
  have differenceTransverse :
      WholeStateTransverse
        (butterflyVelocityPath actual - butterflyVelocityInitial) :=
    wholeStateTransverse_sub _ _
      (wholeBiotSavartVelocityState_transverse
        (actualWholeProjectedTransversePath
          (butterflyReceipt butterflyViscosity) actual).1)
      (wholeBiotSavartVelocityState_transverse
        (butterflyPhysicalState 1))
  have rowBound :=
    wholeStateVelocityBilinearCoefficientAt_norm_le
      (butterflyVelocityPath actual - butterflyVelocityInitial)
      (butterflyVelocityPath actual - butterflyVelocityInitial)
      differenceTransverse butterflyNextSidebandTarget
  calc
    ‖butterflyVelocityQuadraticRemainder actual‖ ≤
        butterflyVelocityQuadraticConstant *
          ‖butterflyVelocityPath actual - butterflyVelocityInitial‖ *
          ‖butterflyVelocityPath actual - butterflyVelocityInitial‖ := by
      simpa only [butterflyVelocityQuadraticRemainder,
        butterflyVelocityQuadraticConstant, mul_assoc] using rowBound
    _ = butterflyVelocityQuadraticConstant *
          ‖butterflyVelocityPath actual - butterflyVelocityInitial‖ ^ 2 := by
      ring
    _ ≤ butterflyVelocityQuadraticConstant *
          butterflyKineticIncrementSq actual :=
      mul_le_mul_of_nonneg_left
        (by
          rw [show
            butterflyVelocityPath actual - butterflyVelocityInitial =
              -(butterflyVelocityInitial - butterflyVelocityPath actual) by
                abel,
            norm_neg]
          exact butterflyVelocityIncrement_norm_sq_le_kinetic actual)
        butterflyVelocityQuadraticConstant_nonneg

theorem butterflyVelocityQuadraticRemainder_scaled_tendsto_zero :
    Tendsto
      (fun actual => actual⁻¹ • butterflyVelocityQuadraticRemainder actual)
      (nhdsWithin 0 (butterflyPhysicalDomain \ {0}))
      (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun actual => norm_nonneg _
  · filter_upwards [self_mem_nhdsWithin] with actual actualMem
    have actualNe : actual ≠ 0 := by
      simpa using actualMem.2
    have actualPos : 0 < actual :=
      lt_of_le_of_ne actualMem.1.1 (Ne.symm actualNe)
    calc
      ‖actual⁻¹ • butterflyVelocityQuadraticRemainder actual‖ =
          actual⁻¹ * ‖butterflyVelocityQuadraticRemainder actual‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr actualPos)]
      _ ≤ actual⁻¹ *
          (butterflyVelocityQuadraticConstant *
            butterflyKineticIncrementSq actual) :=
        mul_le_mul_of_nonneg_left
          (butterflyVelocityQuadraticRemainder_norm_le actual)
          (inv_nonneg.mpr actualPos.le)
      _ = butterflyVelocityQuadraticConstant *
          (butterflyKineticIncrementSq actual / actual) := by
        rw [div_eq_mul_inv]
        ring
  · exact
      (by simpa using
        (butterflyKineticIncrementSq_div_tendsto_zero.const_mul
          butterflyVelocityQuadraticConstant))

theorem wholeSymmetrizedVelocityBilinear_curl_eq_vorticity
    (left right : ComplexVorticityHilbertState)
    (leftZero : left 0 = 0)
    (rightZero : right 0 = 0)
    (leftTransverse : WholeStateTransverse left)
    (rightTransverse : WholeStateTransverse right)
    (output : IntegerWavevector) :
    fourierCurlCoefficient output
        (wholeStateVelocityBilinearCoefficientAt
            (wholeBiotSavartVelocityState left)
            (wholeBiotSavartVelocityState right) output +
          wholeStateVelocityBilinearCoefficientAt
            (wholeBiotSavartVelocityState right)
            (wholeBiotSavartVelocityState left) output) =
      wholeStateVorticityBilinearCoefficientAt left right output +
        wholeStateVorticityBilinearCoefficientAt right left output := by
  let velocityLeft := wholeBiotSavartVelocityState left
  let velocityRight := wholeBiotSavartVelocityState right
  let velocityDirect : IntegerWavevector → ComplexCoordinateVector :=
    fun first => wholeStateVelocityBilinearPairContribution
      velocityLeft velocityRight (first, output - first)
  let velocityReverse : IntegerWavevector → ComplexCoordinateVector :=
    fun first => wholeStateVelocityBilinearPairContribution
      velocityRight velocityLeft (first, output - first)
  let velocitySwapped : IntegerWavevector → ComplexCoordinateVector :=
    fun first => wholeStateVelocityBilinearPairContribution
      velocityRight velocityLeft (output - first, first)
  let vorticityDirect : IntegerWavevector → ComplexCoordinateVector :=
    fun first => finiteStateVorticityBilinearPairContribution
      left right (first, output - first)
  let vorticityReverse : IntegerWavevector → ComplexCoordinateVector :=
    fun first => finiteStateVorticityBilinearPairContribution
      right left (first, output - first)
  let vorticitySwapped : IntegerWavevector → ComplexCoordinateVector :=
    fun first => finiteStateVorticityBilinearPairContribution
      right left (output - first, first)
  have velocityDirectSummable : Summable velocityDirect := by
    exact summable_wholeStateVelocityBilinearPair
      velocityLeft velocityRight
      (wholeBiotSavartVelocityState_transverse left) output
  have velocityReverseSummable : Summable velocityReverse := by
    exact summable_wholeStateVelocityBilinearPair
      velocityRight velocityLeft
      (wholeBiotSavartVelocityState_transverse right) output
  have velocitySwappedSummable : Summable velocitySwapped := by
    have shifted :=
      ((outputSubEquiv output).summable_iff).2 velocityReverseSummable
    exact shifted.congr fun first => by
      simp only [Function.comp_apply, outputSubEquiv_apply]
      simp [velocityReverse, velocitySwapped]
  have vorticityDirectSummable : Summable vorticityDirect := by
    exact summable_wholeStateVorticityBilinearPair
      left right leftTransverse output
  have vorticityReverseSummable : Summable vorticityReverse := by
    exact summable_wholeStateVorticityBilinearPair
      right left rightTransverse output
  have vorticitySwappedSummable : Summable vorticitySwapped := by
    have shifted :=
      ((outputSubEquiv output).summable_iff).2 vorticityReverseSummable
    exact shifted.congr fun first => by
      simp only [Function.comp_apply, outputSubEquiv_apply]
      simp [vorticityReverse, vorticitySwapped]
  have velocityReindex :
      (∑' first, velocitySwapped first) =
        ∑' first, velocityReverse first := by
    simpa [velocitySwapped, velocityReverse,
      outputSubEquiv_apply] using
      (outputSubEquiv output).tsum_eq velocityReverse
  have vorticityReindex :
      (∑' first, vorticitySwapped first) =
        ∑' first, vorticityReverse first := by
    simpa [vorticitySwapped, vorticityReverse,
      outputSubEquiv_apply] using
      (outputSubEquiv output).tsum_eq vorticityReverse
  have pairEq : ∀ first : IntegerWavevector,
      fourierCurlCoefficient output
          (velocityDirect first + velocitySwapped first) =
        vorticityDirect first + vorticitySwapped first := by
    intro first
    have incidence : first + (output - first) = output := by abel
    rw [← incidence]
    exact fourierCurlCoefficient_velocityBilinearPair_add_swap_of_zero
      left right leftZero rightZero leftTransverse rightTransverse
      first (output - first)
  let curl := fourierCurlCoefficientContinuousLinearMap output
  change curl
      ((∑' first, velocityDirect first) +
        ∑' first, velocityReverse first) =
    (∑' first, vorticityDirect first) +
      ∑' first, vorticityReverse first
  rw [← velocityReindex, ← vorticityReindex]
  rw [← Summable.tsum_add velocityDirectSummable velocitySwappedSummable,
    ← Summable.tsum_add vorticityDirectSummable vorticitySwappedSummable]
  rw [curl.map_tsum
    (velocityDirectSummable.add velocitySwappedSummable)]
  apply tsum_congr
  intro first
  exact pairEq first

theorem wholeVelocityNonlinear_curl_eq_vorticityNonlinear
    (state : ComplexVorticityHilbertState)
    (stateZero : state 0 = 0)
    (stateTransverse : WholeStateTransverse state)
    (output : IntegerWavevector) :
    fourierCurlCoefficient output
        (wholeStateVelocityNonlinearCoefficientAt
          (wholeBiotSavartVelocityState state) output) =
      wholeStateVorticityNonlinearCoefficientAt state output := by
  have doubled :=
    wholeSymmetrizedVelocityBilinear_curl_eq_vorticity
      state state stateZero stateZero stateTransverse stateTransverse output
  let quadratic :=
    wholeStateVelocityNonlinearCoefficientAt
      (wholeBiotSavartVelocityState state) output
  have doubledRaw :
      fourierCurlCoefficient output quadratic +
          fourierCurlCoefficient output quadratic =
        wholeStateVorticityNonlinearCoefficientAt state output +
          wholeStateVorticityNonlinearCoefficientAt state output := by
    calc
      fourierCurlCoefficient output quadratic +
          fourierCurlCoefficient output quadratic =
          fourierCurlCoefficient output (quadratic + quadratic) := by
        change
          fourierCurlCoefficientContinuousLinearMap output quadratic +
              fourierCurlCoefficientContinuousLinearMap output quadratic =
            fourierCurlCoefficientContinuousLinearMap output
              (quadratic + quadratic)
        rw [map_add]
      _ = _ := by
        simpa [quadratic, wholeStateVelocityNonlinearCoefficientAt,
          wholeStateVorticityBilinearCoefficientAt_self] using doubled
  have doubled' :
      (2 : ℂ) •
          fourierCurlCoefficient output
            (wholeStateVelocityNonlinearCoefficientAt
              (wholeBiotSavartVelocityState state) output) =
        (2 : ℂ) •
          wholeStateVorticityNonlinearCoefficientAt state output := by
    simpa [quadratic, two_smul] using doubledRaw
  have halved := congrArg
    (fun row : ComplexCoordinateVector => (1 / 2 : ℂ) • row) doubled'
  simpa [smul_smul] using halved

def butterflyVelocityActionState : ComplexVorticityHilbertState :=
  wholeBiotSavartVelocityState butterflyPhysicalActionState

theorem butterflyVelocityPathRow_hasDerivWithinAt
    (wave : IntegerWavevector) :
    HasDerivWithinAt
      (fun actual => butterflyVelocityPath actual wave)
      (butterflyVelocityActionState wave)
      butterflyPhysicalDomain 0 := by
  by_cases waveZero : wave = 0
  · subst wave
    have zeroDerivative :
        HasDerivWithinAt (fun _ : ℝ => (0 : ComplexCoordinateVector)) 0
          butterflyPhysicalDomain 0 :=
      (hasDerivAt_const 0 (0 : ComplexCoordinateVector)).hasDerivWithinAt
    simpa [butterflyVelocityPath, butterflyVelocityActionState,
      wholeBiotSavartVelocityState, finiteStateVelocityCoefficient,
      biotSavartVelocityCoefficient_zero] using zeroDerivative
  · have rowDerivative :=
      butterflyPhysicalRow_hasDerivWithinAt wave waveZero
    exact (biotSavartVelocityCLM wave).hasFDerivAt.comp_hasDerivWithinAt
      0 rowDerivative

def butterflyVelocityIncrementRow
    (actual : ℝ) (wave : IntegerWavevector) : ComplexCoordinateVector :=
  butterflyVelocityPath actual wave - butterflyVelocityInitial wave

theorem butterflyVelocityIncrementRow_hasDerivWithinAt
    (wave : IntegerWavevector) :
    HasDerivWithinAt
      (fun actual => butterflyVelocityIncrementRow actual wave)
      (butterflyVelocityActionState wave)
      butterflyPhysicalDomain 0 := by
  exact (butterflyVelocityPathRow_hasDerivWithinAt wave).sub_const
    (butterflyVelocityInitial wave)

@[simp] theorem butterflyVelocityIncrementRow_zero
    (wave : IntegerWavevector) :
    butterflyVelocityIncrementRow 0 wave = 0 := by
  have pathZero : butterflyVelocityPath 0 = butterflyVelocityInitial := by
    unfold butterflyVelocityPath butterflyVelocityInitial
    rw [butterflyPhysicalPath_zero]
  unfold butterflyVelocityIncrementRow
  rw [pathZero]
  simp

def complexVelocityRowPairContribution
    (_first second : IntegerWavevector)
    (advecting transported : ComplexCoordinateVector) :
    ComplexCoordinateVector :=
  -((Complex.I * (((2 * Real.pi : ℝ) : ℂ))) *
      (complexWavevector second ⬝ᵥ advecting)) • transported

def complexVelocityRowPairContributionLinear
    (first second : IntegerWavevector) :
    ComplexCoordinateVector →ₗ[ℝ]
      ComplexCoordinateVector →ₗ[ℝ] ComplexCoordinateVector :=
  LinearMap.mk₂ ℝ (complexVelocityRowPairContribution first second)
    (by
      intros
      simp [complexVelocityRowPairContribution, dotProduct_add]
      module)
    (by
      intros
      simp [complexVelocityRowPairContribution, dotProduct_smul]
      module)
    (by
      intros
      simp [complexVelocityRowPairContribution, smul_add]
      )
    (by
      intros
      simp [complexVelocityRowPairContribution]
      module)

noncomputable def complexVelocityRowPairContributionRightCLM
    (first second : IntegerWavevector)
    (left : ComplexCoordinateVector) :
    ComplexCoordinateVector →L[ℝ] ComplexCoordinateVector := by
  let linear := complexVelocityRowPairContributionLinear first second left
  exact ⟨linear, linear.continuous_of_finiteDimensional⟩

noncomputable def complexVelocityRowPairContributionCLM
    (first second : IntegerWavevector) :
    ComplexCoordinateVector →L[ℝ]
      ComplexCoordinateVector →L[ℝ] ComplexCoordinateVector := by
  let linear : ComplexCoordinateVector →ₗ[ℝ]
      ComplexCoordinateVector →L[ℝ] ComplexCoordinateVector :=
    { toFun := complexVelocityRowPairContributionRightCLM first second
      map_add' := by
        intro left right
        ext value coordinate
        simp [complexVelocityRowPairContributionRightCLM,
          complexVelocityRowPairContributionLinear]
      map_smul' := by
        intro scalar left
        ext value coordinate
        simp [complexVelocityRowPairContributionRightCLM,
          complexVelocityRowPairContributionLinear] }
  exact ⟨linear, linear.continuous_of_finiteDimensional⟩

theorem complexVelocityRowPairContribution_hasDerivWithinAt
    (first second : IntegerWavevector)
    (left right : ℝ → ComplexCoordinateVector)
    (time : ℝ) (domain : Set ℝ)
    (left' right' : ComplexCoordinateVector)
    (leftDeriv : HasDerivWithinAt left left' domain time)
    (rightDeriv : HasDerivWithinAt right right' domain time) :
    HasDerivWithinAt
      (fun actual => complexVelocityRowPairContribution first second
        (left actual) (right actual))
      (complexVelocityRowPairContribution first second left' (right time) +
        complexVelocityRowPairContribution first second (left time) right')
      domain time := by
  have generated :=
    (complexVelocityRowPairContributionCLM first second)
      |>.hasDerivWithinAt_of_bilinear leftDeriv rightDeriv
  simpa [complexVelocityRowPairContributionCLM,
    complexVelocityRowPairContributionRightCLM,
    complexVelocityRowPairContributionLinear, add_comm] using generated

theorem butterflyVelocityInitial_supported
    (wave : IntegerWavevector) (waveNotMem : wave ∉ butterflySeedModes) :
    butterflyVelocityInitial wave = 0 := by
  change finiteStateVelocityCoefficient (butterflyPhysicalState 1) wave = 0
  unfold finiteStateVelocityCoefficient
  rw [butterflyPhysicalState_supported 1 wave waveNotMem]
  exact biotSavartVelocityCoefficient_zero_vorticity wave

theorem butterflyVelocityBilinear_initial_right_eq_sum
    (right : ComplexVorticityHilbertState) :
    wholeStateVelocityBilinearCoefficientAt
        butterflyVelocityInitial right butterflyNextSidebandTarget =
      ∑ first ∈ butterflySeedModes,
        complexVelocityRowPairContribution first
          (butterflyNextSidebandTarget - first)
          (butterflyVelocityInitial first)
          (right (butterflyNextSidebandTarget - first)) := by
  rw [wholeStateVelocityBilinearCoefficientAt,
    tsum_eq_sum (s := butterflySeedModes)]
  · rfl
  · intro first firstNotMem
    unfold wholeStateVelocityBilinearPairContribution
    rw [show butterflyVelocityInitial first = 0 from
      butterflyVelocityInitial_supported first firstNotMem]
    simp

theorem butterflyVelocityBilinear_left_initial_eq_sum
    (left : ComplexVorticityHilbertState) :
    wholeStateVelocityBilinearCoefficientAt
        left butterflyVelocityInitial butterflyNextSidebandTarget =
      ∑ second ∈ butterflySeedModes,
        complexVelocityRowPairContribution
          (butterflyNextSidebandTarget - second) second
          (left (butterflyNextSidebandTarget - second))
          (butterflyVelocityInitial second) := by
  let pairRow : IntegerWavevector → ComplexCoordinateVector :=
    fun first => wholeStateVelocityBilinearPairContribution
      left butterflyVelocityInitial
      (first, butterflyNextSidebandTarget - first)
  have reindexed :
      (∑' second : IntegerWavevector,
          pairRow (butterflyNextSidebandTarget - second)) =
        ∑' first : IntegerWavevector, pairRow first := by
    exact (outputSubEquiv butterflyNextSidebandTarget).tsum_eq pairRow
  rw [wholeStateVelocityBilinearCoefficientAt]
  rw [← reindexed]
  rw [tsum_eq_sum (s := butterflySeedModes)]
  · apply Finset.sum_congr rfl
    intro second secondMem
    simp [pairRow, wholeStateVelocityBilinearPairContribution,
      complexVelocityRowPairContribution]
  · intro second secondNotMem
    have pairEq : pairRow (butterflyNextSidebandTarget - second) =
        wholeStateVelocityBilinearPairContribution
          left butterflyVelocityInitial
          (butterflyNextSidebandTarget - second, second) := by
      simp [pairRow]
    rw [pairEq]
    unfold wholeStateVelocityBilinearPairContribution
    rw [show butterflyVelocityInitial second = 0 from
      butterflyVelocityInitial_supported second secondNotMem]
    simp

def butterflyVelocityLinearizedPath (actual : ℝ) :
    ComplexCoordinateVector :=
  wholeStateVelocityBilinearCoefficientAt
      (butterflyVelocityPath actual - butterflyVelocityInitial)
      butterflyVelocityInitial butterflyNextSidebandTarget +
    wholeStateVelocityBilinearCoefficientAt
      butterflyVelocityInitial
      (butterflyVelocityPath actual - butterflyVelocityInitial)
      butterflyNextSidebandTarget

def butterflyVelocityLinearizedDerivative : ComplexCoordinateVector :=
  wholeStateVelocityBilinearCoefficientAt
      butterflyVelocityActionState butterflyVelocityInitial
      butterflyNextSidebandTarget +
    wholeStateVelocityBilinearCoefficientAt
      butterflyVelocityInitial butterflyVelocityActionState
      butterflyNextSidebandTarget

theorem butterflyVelocityLeftLinearizedPath_hasDerivWithinAt :
    HasDerivWithinAt
      (fun actual =>
        wholeStateVelocityBilinearCoefficientAt
          (butterflyVelocityPath actual - butterflyVelocityInitial)
          butterflyVelocityInitial butterflyNextSidebandTarget)
      (wholeStateVelocityBilinearCoefficientAt
        butterflyVelocityActionState butterflyVelocityInitial
        butterflyNextSidebandTarget)
      butterflyPhysicalDomain 0 := by
  have finiteDerivative :
      HasDerivWithinAt
        (fun actual =>
          ∑ second ∈ butterflySeedModes,
            complexVelocityRowPairContribution
              (butterflyNextSidebandTarget - second) second
              (butterflyVelocityIncrementRow actual
                (butterflyNextSidebandTarget - second))
              (butterflyVelocityInitial second))
        (∑ second ∈ butterflySeedModes,
          complexVelocityRowPairContribution
            (butterflyNextSidebandTarget - second) second
            (butterflyVelocityActionState
              (butterflyNextSidebandTarget - second))
            (butterflyVelocityInitial second))
        butterflyPhysicalDomain 0 := by
    apply HasDerivWithinAt.fun_sum
    intro second secondMem
    have generated :=
      complexVelocityRowPairContribution_hasDerivWithinAt
        (butterflyNextSidebandTarget - second) second
        (fun actual => butterflyVelocityIncrementRow actual
          (butterflyNextSidebandTarget - second))
        (fun _ => butterflyVelocityInitial second)
        0 butterflyPhysicalDomain
        (butterflyVelocityActionState
          (butterflyNextSidebandTarget - second)) 0
        (butterflyVelocityIncrementRow_hasDerivWithinAt
          (butterflyNextSidebandTarget - second))
        (hasDerivAt_const 0 (butterflyVelocityInitial second)
          |>.hasDerivWithinAt)
    simpa [complexVelocityRowPairContribution] using generated
  have sourceEq : ∀ actual,
      wholeStateVelocityBilinearCoefficientAt
          (butterflyVelocityPath actual - butterflyVelocityInitial)
          butterflyVelocityInitial butterflyNextSidebandTarget =
        ∑ second ∈ butterflySeedModes,
          complexVelocityRowPairContribution
            (butterflyNextSidebandTarget - second) second
            (butterflyVelocityIncrementRow actual
              (butterflyNextSidebandTarget - second))
            (butterflyVelocityInitial second) := by
    intro actual
    simpa [butterflyVelocityIncrementRow] using
      butterflyVelocityBilinear_left_initial_eq_sum
        (butterflyVelocityPath actual - butterflyVelocityInitial)
  have tangentEq :
      wholeStateVelocityBilinearCoefficientAt
          butterflyVelocityActionState butterflyVelocityInitial
          butterflyNextSidebandTarget =
        ∑ second ∈ butterflySeedModes,
          complexVelocityRowPairContribution
            (butterflyNextSidebandTarget - second) second
            (butterflyVelocityActionState
              (butterflyNextSidebandTarget - second))
            (butterflyVelocityInitial second) :=
    butterflyVelocityBilinear_left_initial_eq_sum
      butterflyVelocityActionState
  exact (finiteDerivative.congr
    (fun actual actualMem => sourceEq actual)
    (sourceEq 0)).congr_deriv tangentEq.symm

theorem butterflyVelocityRightLinearizedPath_hasDerivWithinAt :
    HasDerivWithinAt
      (fun actual =>
        wholeStateVelocityBilinearCoefficientAt
          butterflyVelocityInitial
          (butterflyVelocityPath actual - butterflyVelocityInitial)
          butterflyNextSidebandTarget)
      (wholeStateVelocityBilinearCoefficientAt
        butterflyVelocityInitial butterflyVelocityActionState
        butterflyNextSidebandTarget)
      butterflyPhysicalDomain 0 := by
  have finiteDerivative :
      HasDerivWithinAt
        (fun actual =>
          ∑ first ∈ butterflySeedModes,
            complexVelocityRowPairContribution first
              (butterflyNextSidebandTarget - first)
              (butterflyVelocityInitial first)
              (butterflyVelocityIncrementRow actual
                (butterflyNextSidebandTarget - first)))
        (∑ first ∈ butterflySeedModes,
          complexVelocityRowPairContribution first
            (butterflyNextSidebandTarget - first)
            (butterflyVelocityInitial first)
            (butterflyVelocityActionState
              (butterflyNextSidebandTarget - first)))
        butterflyPhysicalDomain 0 := by
    apply HasDerivWithinAt.fun_sum
    intro first firstMem
    have generated :=
      complexVelocityRowPairContribution_hasDerivWithinAt
        first (butterflyNextSidebandTarget - first)
        (fun _ => butterflyVelocityInitial first)
        (fun actual => butterflyVelocityIncrementRow actual
          (butterflyNextSidebandTarget - first))
        0 butterflyPhysicalDomain 0
        (butterflyVelocityActionState
          (butterflyNextSidebandTarget - first))
        (hasDerivAt_const 0 (butterflyVelocityInitial first)
          |>.hasDerivWithinAt)
        (butterflyVelocityIncrementRow_hasDerivWithinAt
          (butterflyNextSidebandTarget - first))
    simpa [complexVelocityRowPairContribution] using generated
  have sourceEq : ∀ actual,
      wholeStateVelocityBilinearCoefficientAt
          butterflyVelocityInitial
          (butterflyVelocityPath actual - butterflyVelocityInitial)
          butterflyNextSidebandTarget =
        ∑ first ∈ butterflySeedModes,
          complexVelocityRowPairContribution first
            (butterflyNextSidebandTarget - first)
            (butterflyVelocityInitial first)
            (butterflyVelocityIncrementRow actual
              (butterflyNextSidebandTarget - first)) := by
    intro actual
    simpa [butterflyVelocityIncrementRow] using
      butterflyVelocityBilinear_initial_right_eq_sum
        (butterflyVelocityPath actual - butterflyVelocityInitial)
  have tangentEq :
      wholeStateVelocityBilinearCoefficientAt
          butterflyVelocityInitial butterflyVelocityActionState
          butterflyNextSidebandTarget =
        ∑ first ∈ butterflySeedModes,
          complexVelocityRowPairContribution first
            (butterflyNextSidebandTarget - first)
            (butterflyVelocityInitial first)
            (butterflyVelocityActionState
              (butterflyNextSidebandTarget - first)) :=
    butterflyVelocityBilinear_initial_right_eq_sum
      butterflyVelocityActionState
  exact (finiteDerivative.congr
    (fun actual actualMem => sourceEq actual)
    (sourceEq 0)).congr_deriv tangentEq.symm

theorem butterflyVelocityLinearizedPath_hasDerivWithinAt :
    HasDerivWithinAt butterflyVelocityLinearizedPath
      butterflyVelocityLinearizedDerivative
      butterflyPhysicalDomain 0 := by
  exact butterflyVelocityLeftLinearizedPath_hasDerivWithinAt.add
    butterflyVelocityRightLinearizedPath_hasDerivWithinAt

theorem wholeStateVelocityBilinearCoefficientAt_add_right_local
    (left right₁ right₂ : ComplexVorticityHilbertState)
    (leftTransverse : WholeStateTransverse left)
    (output : IntegerWavevector) :
    wholeStateVelocityBilinearCoefficientAt left (right₁ + right₂) output =
      wholeStateVelocityBilinearCoefficientAt left right₁ output +
        wholeStateVelocityBilinearCoefficientAt left right₂ output := by
  have firstSummable :=
    summable_wholeStateVelocityBilinearPair
      left right₁ leftTransverse output
  have secondSummable :=
    summable_wholeStateVelocityBilinearPair
      left right₂ leftTransverse output
  unfold wholeStateVelocityBilinearCoefficientAt
  rw [← firstSummable.tsum_add secondSummable]
  apply tsum_congr
  intro first
  simp [wholeStateVelocityBilinearPairContribution, smul_add]

theorem butterflyVelocityNonlinearDifference_eq_linearized_add_remainder
    (actual : ℝ) :
    wholeStateVelocityNonlinearCoefficientAt
          (butterflyVelocityPath actual) butterflyNextSidebandTarget -
        wholeStateVelocityNonlinearCoefficientAt
          butterflyVelocityInitial butterflyNextSidebandTarget =
      butterflyVelocityLinearizedPath actual +
        butterflyVelocityQuadraticRemainder actual := by
  have pathTransverse : WholeStateTransverse (butterflyVelocityPath actual) :=
    wholeBiotSavartVelocityState_transverse _
  have initialTransverse : WholeStateTransverse butterflyVelocityInitial :=
    wholeBiotSavartVelocityState_transverse _
  rw [wholeStateVelocityNonlinearCoefficientAt_sub
    (butterflyVelocityPath actual) butterflyVelocityInitial
    pathTransverse initialTransverse butterflyNextSidebandTarget]
  let increment := butterflyVelocityPath actual - butterflyVelocityInitial
  have pathEq : butterflyVelocityPath actual =
      butterflyVelocityInitial + increment := by
    dsimp only [increment]
    abel
  rw [pathEq]
  have differenceEq :
      butterflyVelocityInitial + increment - butterflyVelocityInitial =
        increment := by abel
  rw [differenceEq,
    wholeStateVelocityBilinearCoefficientAt_add_right_local
      increment butterflyVelocityInitial increment
      (wholeStateTransverse_sub _ _ pathTransverse initialTransverse)
      butterflyNextSidebandTarget]
  unfold butterflyVelocityLinearizedPath
    butterflyVelocityQuadraticRemainder
  dsimp only [increment]
  abel

@[simp] theorem butterflyVelocityQuadraticRemainder_zero :
    butterflyVelocityQuadraticRemainder 0 = 0 := by
  unfold butterflyVelocityQuadraticRemainder
  have pathZero : butterflyVelocityPath 0 = butterflyVelocityInitial := by
    unfold butterflyVelocityPath butterflyVelocityInitial
    rw [butterflyPhysicalPath_zero]
  rw [pathZero]
  simp [wholeStateVelocityBilinearCoefficientAt,
    wholeStateVelocityBilinearPairContribution]

theorem butterflyVelocityQuadraticRemainder_hasDerivWithinAt_zero :
    HasDerivWithinAt butterflyVelocityQuadraticRemainder 0
      butterflyPhysicalDomain 0 := by
  rw [hasDerivWithinAt_iff_tendsto_slope]
  convert butterflyVelocityQuadraticRemainder_scaled_tendsto_zero using 1
  funext actual
  rw [slope_def_module, butterflyVelocityQuadraticRemainder_zero]
  simp

theorem butterflyVelocityNonlinearDifferencePath_hasDerivWithinAt :
    HasDerivWithinAt
      (fun actual =>
        wholeStateVelocityNonlinearCoefficientAt
              (butterflyVelocityPath actual) butterflyNextSidebandTarget -
            wholeStateVelocityNonlinearCoefficientAt
              butterflyVelocityInitial butterflyNextSidebandTarget)
      butterflyVelocityLinearizedDerivative
      butterflyPhysicalDomain 0 := by
  have combined := butterflyVelocityLinearizedPath_hasDerivWithinAt.add
    butterflyVelocityQuadraticRemainder_hasDerivWithinAt_zero
  have combined' := combined.congr_deriv
    (add_zero butterflyVelocityLinearizedDerivative)
  apply combined'.congr
  · intro actual actualMem
    exact butterflyVelocityNonlinearDifference_eq_linearized_add_remainder
      actual
  · exact butterflyVelocityNonlinearDifference_eq_linearized_add_remainder 0

theorem butterflyVelocityNonlinearPath_hasDerivWithinAt :
    HasDerivWithinAt
      (fun actual =>
        wholeStateVelocityNonlinearCoefficientAt
          (butterflyVelocityPath actual) butterflyNextSidebandTarget)
      butterflyVelocityLinearizedDerivative
      butterflyPhysicalDomain 0 := by
  have shifted :=
    butterflyVelocityNonlinearDifferencePath_hasDerivWithinAt.const_add
      (wholeStateVelocityNonlinearCoefficientAt
        butterflyVelocityInitial butterflyNextSidebandTarget)
  apply shifted.congr
  · intro actual actualMem
    abel
  ·
    abel

theorem butterflyVelocityLinearizedDerivative_curl :
    fourierCurlCoefficient butterflyNextSidebandTarget
        butterflyVelocityLinearizedDerivative =
      butterflyPhysicalFullNextSidebandDerivative := by
  have actionZero : butterflyPhysicalActionState 0 = 0 :=
    butterflyPhysicalActionState_supported 0
      butterflyRationalActionModes_zero_not_mem
  have actionTransverse : WholeStateTransverse butterflyPhysicalActionState :=
    wholeFiniteSupportActionState_transverse
      butterflyViscosity.coeff butterflySeedModes
      (butterflyPhysicalState 1)
      (butterflyPhysicalState_supported 1)
      (butterflyPhysicalState_transverse 1)
  have commuting :=
    wholeSymmetrizedVelocityBilinear_curl_eq_vorticity
      butterflyPhysicalActionState (butterflyPhysicalState 1)
      actionZero (butterflyPhysicalState_zero 1)
      actionTransverse (butterflyPhysicalState_transverse 1)
      butterflyNextSidebandTarget
  change
    fourierCurlCoefficient butterflyNextSidebandTarget
        butterflyVelocityLinearizedDerivative = _ at commuting
  unfold butterflyPhysicalFullNextSidebandDerivative
  rw [butterflyRationalFullNextSidebandDerivative_toComplex]
  exact commuting

theorem butterflyNextSidebandFullRowPath_eq_velocityCurl
    (actual : ℝ) :
    butterflyNextSidebandFullRowPath butterflyViscosity actual =
      fourierCurlCoefficient butterflyNextSidebandTarget
        (wholeStateVelocityNonlinearCoefficientAt
          (butterflyVelocityPath actual) butterflyNextSidebandTarget) := by
  let state :=
    (actualWholeProjectedTransversePath
      (butterflyReceipt butterflyViscosity) actual).1
  have stateZero : state 0 = 0 := by
    exact (butterflyReceipt butterflyViscosity).wholePath_zero_row _
  have commuting :=
    wholeVelocityNonlinear_curl_eq_vorticityNonlinear
      state stateZero
      (actualWholeProjectedTransversePath
        (butterflyReceipt butterflyViscosity) actual).2
      butterflyNextSidebandTarget
  unfold butterflyNextSidebandFullRowPath
    actualWholeContinuousNonlinearRow butterflyVelocityPath
  exact commuting.symm

theorem butterflyNextSidebandFullRowPath_hasDerivWithinAt_zero :
    HasDerivWithinAt
      (butterflyNextSidebandFullRowPath butterflyViscosity)
      butterflyPhysicalFullNextSidebandDerivative
      butterflyPhysicalDomain 0 := by
  have curled :=
    (fourierCurlCoefficientContinuousLinearMap
      butterflyNextSidebandTarget).restrictScalars ℝ
        |>.hasFDerivAt.comp_hasDerivWithinAt
        0 butterflyVelocityNonlinearPath_hasDerivWithinAt
  have aligned := curled.congr
    (fun actual actualMem =>
      butterflyNextSidebandFullRowPath_eq_velocityCurl actual)
    (butterflyNextSidebandFullRowPath_eq_velocityCurl 0)
  exact aligned.congr_deriv butterflyVelocityLinearizedDerivative_curl

theorem exists_butterflyNextSidebandFullRowPhysicalPersistenceTime :
    ∃ epsilon : ℝ,
      0 < epsilon ∧ epsilon ≤ butterflyPhysicalTime ∧
        ∀ actual : ℝ, 0 < actual → actual < epsilon →
          butterflyNextSidebandFullRowPath
            butterflyViscosity actual ≠ 0 := by
  have punctured :=
    butterflyNextSidebandFullRowPath_hasDerivWithinAt_zero.eventually_ne
      butterflyPhysicalFullNextSidebandDerivative_ne_zero
      (c := (0 : ComplexCoordinateVector))
  have nearZero :
      ∀ᶠ actual in nhds (0 : ℝ),
        actual ∈ butterflyPhysicalDomain \ {0} →
          butterflyNextSidebandFullRowPath
            butterflyViscosity actual ≠ 0 :=
    eventually_nhdsWithin_iff.mp punctured
  obtain ⟨radius, radiusPos, withinBall⟩ :=
    Metric.eventually_nhds_iff.mp nearZero
  let epsilon := min radius (butterflyPhysicalTime / 2)
  have physicalTimePos : 0 < butterflyPhysicalTime :=
    wholeRestartDuration_pos (butterflyPhysicalSeed butterflyViscosity)
  have epsilonPos : 0 < epsilon := by
    exact lt_min radiusPos (half_pos physicalTimePos)
  have epsilonLePhysical : epsilon ≤ butterflyPhysicalTime :=
    (min_le_right radius (butterflyPhysicalTime / 2)).trans
      (half_le_self physicalTimePos.le)
  refine ⟨epsilon, epsilonPos, epsilonLePhysical, ?_⟩
  intro actual actualPos actualLt
  apply withinBall
  · rw [Real.dist_eq, sub_zero, abs_of_pos actualPos]
    exact actualLt.trans_le (min_le_left _ _)
  · exact ⟨⟨actualPos.le,
      actualLt.le.trans epsilonLePhysical⟩, by
        simpa using actualPos.ne'⟩

end
end SaturationMonoid.NavierStokes.RationalVorticityEvaluator
