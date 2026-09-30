import H0mework.NavierStokes.Accumulation.ActualFourierConeAdvance

/-!
# Full-receipt Fourier-cone advance

The selected-prefix Euler tube is reproduced on the unchanged canonical
`current.nextReceipt` horizon.  Every row and margin is computed from the
same current, its generated full receipt, viscosity and output frequency.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

open scoped ENNReal Topology Interval

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientFullReceiptFourierConeAdvance

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinAmbientNorm
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientFiniteGalerkinMildDuhamel
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteMildDuhamel
open ThreeDimensionalVorticityCoefficientCanonicalExhaustiveGalerkinTarget
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientWholeTangentEnergyTransport
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSourcePairOccurrence
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairOccurrenceWork
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartActualFourierConeAdvance
open ThreeDimensionalVorticityCoefficientWholeStateSourceOwnedLocalBarrier

noncomputable section

/-- Complete first-order Euler row at an arbitrary time on the canonical
full replay. -/
def fullReplayEulerRow
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (time : Real)
    (wave : IntegerWavevector) : ComplexCoordinateVector :=
  current.contact.physicalState wave +
    time • wholeLatticeVorticityFourierTangentAt nu.coeff
      current.contact.physicalState wave

/-- Current-generated radius for the unchanged full next receipt. -/
def fullReplayEulerRadius
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu) : Real :=
  ‖current.nextReceipt.wholePath‖ + ‖current.contact.physicalState‖

/-- Full-replay rowwise remainder slope. -/
def fullReplayEulerRemainderSlope
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (wave : IntegerWavevector) : Real :=
  6 * Real.sqrt (integerWaveNormSq wave) *
      fullReplayEulerRadius current ^ 2 +
    (nu.coeff * integerWaveViscousMultiplier wave) *
      fullReplayEulerRadius current

theorem fullReplayEulerRemainderSlope_nonneg
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (wave : IntegerWavevector) :
    0 ≤ fullReplayEulerRemainderSlope current wave := by
  unfold fullReplayEulerRemainderSlope fullReplayEulerRadius
  have dampingNonneg :
      0 ≤ nu.coeff * integerWaveViscousMultiplier wave :=
    mul_nonneg nu.coeff_pos.le (by
      unfold integerWaveViscousMultiplier
      exact mul_nonneg (sq_nonneg _) (integerWaveNormSq_nonneg wave))
  positivity

/-- The canonical coefficient ceiling bounds the norm of the entire
unchanged next receipt, not merely almost every representative. -/
theorem fullReplay_wholePath_norm_le_sqrt_coefficientCeiling
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu) :
    ‖current.nextReceipt.wholePath‖ ≤
      Real.sqrt (wholeRestartCoefficientCeiling current.contact) := by
  have ceilingNonneg :
      0 ≤ wholeRestartCoefficientCeiling current.contact :=
    (wholeRestartCoefficientCeiling_pos current.contact).le
  apply (BoundedContinuousFunction.norm_le
    (Real.sqrt_nonneg _)).2
  intro time
  have normSqLe :
      ‖current.nextReceipt.wholePath time‖ ^ 2 ≤
        wholeRestartCoefficientCeiling current.contact :=
    (wholeState_norm_sq_le_wholeVorticityEuclideanMass
      (current.nextReceipt.wholePath time)).trans
        (fullReplayWholeMass_le_coefficientCeiling current time)
  exact (Real.le_sqrt (norm_nonneg _) ceilingNonneg).2 normSqLe

/-- The same ceiling also bounds the exact current endpoint. -/
theorem current_physicalState_norm_le_sqrt_coefficientCeiling
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu) :
    ‖current.contact.physicalState‖ ≤
      Real.sqrt (wholeRestartCoefficientCeiling current.contact) := by
  have ceilingNonneg :
      0 ≤ wholeRestartCoefficientCeiling current.contact :=
    (wholeRestartCoefficientCeiling_pos current.contact).le
  have rawLe := wholeRestartRawCoefficientCeiling_le current.contact
  rw [wholeRestartRawCoefficientCeiling_eq] at rawLe
  simp only [wholeRestartPhysicalState_generatedPositiveWholeRestartContact]
    at rawLe
  have massLe :
      wholeVorticityEuclideanMass current.contact.physicalState ≤
        wholeRestartCoefficientCeiling current.contact := by
    linarith
  have normSqLe :=
    (wholeState_norm_sq_le_wholeVorticityEuclideanMass
      current.contact.physicalState).trans massLe
  exact (Real.le_sqrt (norm_nonneg _) ceilingNonneg).2 normSqLe

/-- Source-only removal of the opaque receipt norm from the Euler radius. -/
theorem fullReplayEulerRadius_le_two_sqrt_coefficientCeiling
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu) :
    fullReplayEulerRadius current ≤
      2 * Real.sqrt (wholeRestartCoefficientCeiling current.contact) := by
  unfold fullReplayEulerRadius
  linarith [fullReplay_wholePath_norm_le_sqrt_coefficientCeiling current,
    current_physicalState_norm_le_sqrt_coefficientCeiling current]

/-- Explicit fixed-output slope bound depending only on viscosity, output
frequency and the current coefficient ceiling. -/
theorem fullReplayEulerRemainderSlope_le_sourceCeiling
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (wave : IntegerWavevector) :
    fullReplayEulerRemainderSlope current wave ≤
      24 * Real.sqrt (integerWaveNormSq wave) *
          wholeRestartCoefficientCeiling current.contact +
        2 * (nu.coeff * integerWaveViscousMultiplier wave) *
          Real.sqrt (wholeRestartCoefficientCeiling current.contact) := by
  let radius := fullReplayEulerRadius current
  let ceiling := wholeRestartCoefficientCeiling current.contact
  have radiusNonneg : 0 ≤ radius := by
    dsimp only [radius, fullReplayEulerRadius]
    positivity
  have ceilingNonneg : 0 ≤ ceiling :=
    (wholeRestartCoefficientCeiling_pos current.contact).le
  have radiusLe : radius ≤ 2 * Real.sqrt ceiling := by
    simpa only [radius, ceiling] using
      fullReplayEulerRadius_le_two_sqrt_coefficientCeiling current
  have radiusSqLe : radius ^ 2 ≤ 4 * ceiling := by
    have squared := (sq_le_sq₀ radiusNonneg
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))).2 radiusLe
    rw [mul_pow, Real.sq_sqrt ceilingNonneg] at squared
    norm_num at squared ⊢
    exact squared
  have angularNonneg :
      0 ≤ 6 * Real.sqrt (integerWaveNormSq wave) := by positivity
  have dampingNonneg :
      0 ≤ nu.coeff * integerWaveViscousMultiplier wave :=
    mul_nonneg nu.coeff_pos.le (by
      unfold integerWaveViscousMultiplier
      exact mul_nonneg (sq_nonneg _) (integerWaveNormSq_nonneg wave))
  unfold fullReplayEulerRemainderSlope
  dsimp only [radius, ceiling] at radiusLe radiusSqLe ⊢
  calc
    6 * Real.sqrt (integerWaveNormSq wave) *
          fullReplayEulerRadius current ^ 2 +
        (nu.coeff * integerWaveViscousMultiplier wave) *
          fullReplayEulerRadius current ≤
      6 * Real.sqrt (integerWaveNormSq wave) * (4 * ceiling) +
        (nu.coeff * integerWaveViscousMultiplier wave) *
          (2 * Real.sqrt ceiling) :=
      add_le_add
        (mul_le_mul_of_nonneg_left radiusSqLe angularNonneg)
        (mul_le_mul_of_nonneg_left radiusLe dampingNonneg)
    _ = 24 * Real.sqrt (integerWaveNormSq wave) * ceiling +
        2 * (nu.coeff * integerWaveViscousMultiplier wave) *
          Real.sqrt ceiling := by ring

/-- Seventh-order source barrier gives an explicit upper, rather than lower,
bound on the unchanged canonical horizon. -/
theorem wholeRestartDuration_le_inverse_seventhBarrier
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu) :
    wholeRestartDuration current.contact ≤
      1 /
        (2 *
          (sourceOwnedWholeStateBarrierSeventhCoefficient nu *
              wholeRestartCoefficientCeiling current.contact ^ 7 + 1)) := by
  let ceiling := wholeRestartCoefficientCeiling current.contact
  let model := sourceOwnedWholeStateBarrierSeventhCoefficient nu *
      ceiling ^ 7 + 1
  have ceilingPos : 0 < ceiling :=
    wholeRestartCoefficientCeiling_pos current.contact
  have modelPos : 0 < model := by
    dsimp only [model]
    have coefficientPos :=
      sourceOwnedWholeStateBarrierSeventhCoefficient_pos nu
    positivity
  have barrierLower := sourceOwnedWholeStateBarrierSeventh_le
    nu ceiling ceilingPos.le
  have denominatorLe :
      2 * model ≤ 2 * sourceOwnedWholeStateBarrierSlope nu ceiling := by
    exact mul_le_mul_of_nonneg_left barrierLower (by norm_num)
  have reciprocal := one_div_le_one_div_of_le
    (mul_pos (by norm_num) modelPos) denominatorLe
  simpa only [wholeRestartDuration, sourceOwnedWholeStateDuration,
    ceiling, model] using reciprocal

/-- Complete source-only upper payment for one fixed-output Euler tube. -/
def fullReplayEulerTubePaymentUpper
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (wave : IntegerWavevector) : Real :=
  let ceiling := wholeRestartCoefficientCeiling current.contact
  (1 /
      (2 *
        (sourceOwnedWholeStateBarrierSeventhCoefficient nu *
            ceiling ^ 7 + 1))) *
    (24 * Real.sqrt (integerWaveNormSq wave) * ceiling +
      2 * (nu.coeff * integerWaveViscousMultiplier wave) *
        Real.sqrt ceiling)

theorem fullReplay_duration_mul_remainderSlope_le_sourceUpper
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (wave : IntegerWavevector) :
    wholeRestartDuration current.contact *
        fullReplayEulerRemainderSlope current wave ≤
      fullReplayEulerTubePaymentUpper current wave := by
  have durationLe := wholeRestartDuration_le_inverse_seventhBarrier current
  have slopeLe := fullReplayEulerRemainderSlope_le_sourceCeiling current wave
  have slopeNonneg := fullReplayEulerRemainderSlope_nonneg current wave
  have durationUpperNonneg :
      0 ≤ 1 /
        (2 *
          (sourceOwnedWholeStateBarrierSeventhCoefficient nu *
              wholeRestartCoefficientCeiling current.contact ^ 7 + 1)) := by
    have coefficientPos :=
      sourceOwnedWholeStateBarrierSeventhCoefficient_pos nu
    have ceilingPos := wholeRestartCoefficientCeiling_pos current.contact
    exact (one_div_pos.mpr (mul_pos (by norm_num) (by positivity))).le
  exact mul_le_mul durationLe slopeLe slopeNonneg durationUpperNonneg

theorem fullReplayEulerTubePaymentUpper_nonneg
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (wave : IntegerWavevector) :
    0 ≤ fullReplayEulerTubePaymentUpper current wave := by
  unfold fullReplayEulerTubePaymentUpper
  have coefficientPos :=
    sourceOwnedWholeStateBarrierSeventhCoefficient_pos nu
  have ceilingPos := wholeRestartCoefficientCeiling_pos current.contact
  have durationModelNonneg :
      0 ≤ 1 /
        (2 *
          (sourceOwnedWholeStateBarrierSeventhCoefficient nu *
              wholeRestartCoefficientCeiling current.contact ^ 7 + 1)) := by
    exact (one_div_pos.mpr (mul_pos (by norm_num) (by positivity))).le
  have dampingNonneg :
      0 ≤ nu.coeff * integerWaveViscousMultiplier wave :=
    mul_nonneg nu.coeff_pos.le (by
      unfold integerWaveViscousMultiplier
      exact mul_nonneg (sq_nonneg _) (integerWaveNormSq_nonneg wave))
  exact mul_nonneg durationModelNonneg
    (add_nonneg (by positivity)
      (mul_nonneg
        (mul_nonneg (by norm_num) dampingNonneg)
        (Real.sqrt_nonneg _)))

/-- Simplified inverse-sixth source envelope for fixed output frequency. -/
def fullReplayEulerTubeInverseSixthUpper
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (wave : IntegerWavevector) : Real :=
  let ceiling := wholeRestartCoefficientCeiling current.contact
  (12 * Real.sqrt (integerWaveNormSq wave) +
      nu.coeff * integerWaveViscousMultiplier wave) /
    (sourceOwnedWholeStateBarrierSeventhCoefficient nu * ceiling ^ 6)

theorem fullReplayEulerTubePaymentUpper_le_inverseSixth
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (wave : IntegerWavevector) :
    fullReplayEulerTubePaymentUpper current wave ≤
      fullReplayEulerTubeInverseSixthUpper current wave := by
  let ceiling := wholeRestartCoefficientCeiling current.contact
  let coefficient := sourceOwnedWholeStateBarrierSeventhCoefficient nu
  let angular := Real.sqrt (integerWaveNormSq wave)
  let damping := nu.coeff * integerWaveViscousMultiplier wave
  let numerator := 24 * angular * ceiling + 2 * damping * Real.sqrt ceiling
  let denominator := 2 * (coefficient * ceiling ^ 7 + 1)
  let target := (12 * angular + damping) / (coefficient * ceiling ^ 6)
  have ceilingPos : 0 < ceiling := by
    simpa only [ceiling] using
      wholeRestartCoefficientCeiling_pos current.contact
  have ceilingOne : 1 ≤ ceiling := by
    have levelPos : 0 < wholeRestartCoefficientLevel current.contact := by
      have castPos :
          0 < (wholeRestartCoefficientLevel current.contact : Real) := by
        simpa only [wholeRestartCoefficientCeiling] using
          wholeRestartCoefficientCeiling_pos current.contact
      exact_mod_cast castPos
    dsimp only [ceiling, wholeRestartCoefficientCeiling]
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr levelPos.ne')
  have sqrtLe : Real.sqrt ceiling ≤ ceiling :=
    Real.sqrt_le_self_iff.mpr (Or.inr ceilingOne)
  have coefficientPos : 0 < coefficient := by
    simpa only [coefficient] using
      sourceOwnedWholeStateBarrierSeventhCoefficient_pos nu
  have angularNonneg : 0 ≤ angular := Real.sqrt_nonneg _
  have dampingNonneg : 0 ≤ damping := by
    dsimp only [damping]
    exact mul_nonneg nu.coeff_pos.le (by
      unfold integerWaveViscousMultiplier
      exact mul_nonneg (sq_nonneg _) (integerWaveNormSq_nonneg wave))
  have numeratorLe : numerator ≤ 2 * (12 * angular + damping) * ceiling := by
    dsimp only [numerator]
    nlinarith
  have denominatorPos : 0 < denominator := by
    dsimp only [denominator]
    positivity
  have modelDenominatorPos :
      0 < coefficient * ceiling ^ 6 := by positivity
  have targetNonneg : 0 ≤ target := by
    dsimp only [target]
    exact div_nonneg (add_nonneg (by positivity) dampingNonneg)
      modelDenominatorPos.le
  have denominatorLower :
      2 * coefficient * ceiling ^ 7 ≤ denominator := by
    dsimp only [denominator]
    linarith
  unfold fullReplayEulerTubePaymentUpper
    fullReplayEulerTubeInverseSixthUpper
  dsimp only [ceiling, coefficient, angular, damping,
    numerator, denominator, target] at *
  rw [one_div_mul_eq_div]
  apply (div_le_iff₀ denominatorPos).2
  calc
    24 * angular * ceiling + 2 * damping * Real.sqrt ceiling ≤
        2 * (12 * angular + damping) * ceiling := numeratorLe
    _ = target * (2 * coefficient * ceiling ^ 7) := by
      dsimp only [target]
      have denominatorNe : coefficient * ceiling ^ 6 ≠ 0 :=
        modelDenominatorPos.ne'
      rw [show 2 * coefficient * ceiling ^ 7 =
          (coefficient * ceiling ^ 6) * (2 * ceiling) by ring]
      rw [← mul_assoc, div_mul_cancel₀ _ denominatorNe]
      ring
    _ ≤ target * denominator :=
      mul_le_mul_of_nonneg_left denominatorLower targetNonneg

private theorem fullReceipt_initialRow_eq_heatPath_zero
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (wave : IntegerWavevector) :
    actualWholeContinuousHeatDuhamelPath current.nextReceipt wave 0 =
      current.contact.physicalState wave := by
  unfold actualWholeContinuousHeatDuhamelPath
    heatDuhamelComplexCoordinatePath intervalIntegralComplexCoordinatePath
  simp

private theorem fullReceipt_heatPath_hasDerivAt
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (wave : IntegerWavevector)
    (actual : Real) :
    HasDerivAt
      (actualWholeContinuousHeatDuhamelPath current.nextReceipt wave)
      (actualWholeContinuousNonlinearRow current.nextReceipt wave actual -
        (nu.coeff * integerWaveViscousMultiplier wave) •
          actualWholeContinuousHeatDuhamelPath
            current.nextReceipt wave actual)
      actual := by
  exact heatDuhamelComplexCoordinatePath_hasDerivAt_of_continuous
    (current.contact.physicalState wave)
    (actualWholeContinuousNonlinearRow current.nextReceipt wave)
    (nu.coeff * integerWaveViscousMultiplier wave) 0 actual
    (actualWholeContinuousNonlinearRow_continuous current.nextReceipt wave)

def fullReplayEulerErrorDerivative
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (wave : IntegerWavevector)
    (actual : Real) : ComplexCoordinateVector :=
  (actualWholeContinuousNonlinearRow current.nextReceipt wave actual -
      (nu.coeff * integerWaveViscousMultiplier wave) •
        actualWholeContinuousHeatDuhamelPath
          current.nextReceipt wave actual) -
    wholeLatticeVorticityFourierTangentAt nu.coeff
      current.contact.physicalState wave

private theorem fullReplayEulerErrorDerivative_continuous
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (wave : IntegerWavevector) :
    Continuous (fullReplayEulerErrorDerivative current wave) := by
  unfold fullReplayEulerErrorDerivative
  have heatContinuous : Continuous
      (actualWholeContinuousHeatDuhamelPath current.nextReceipt wave) := by
    rw [continuous_iff_continuousAt]
    intro actual
    exact (fullReceipt_heatPath_hasDerivAt current wave actual).continuousAt
  exact
    ((actualWholeContinuousNonlinearRow_continuous
        current.nextReceipt wave).sub
      (heatContinuous.const_smul
        (nu.coeff * integerWaveViscousMultiplier wave))).sub
      continuous_const

theorem fullReplayEulerError_integral_eq
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (wave : IntegerWavevector)
    (waveNe : wave ≠ 0)
    (time : Icc (0 : Real) (wholeRestartDuration current.contact)) :
    (∫ actual in (0 : Real)..time.1,
        fullReplayEulerErrorDerivative current wave actual) =
      current.nextReceipt.wholePath time wave -
        fullReplayEulerRow current time.1 wave := by
  let heatPath := actualWholeContinuousHeatDuhamelPath
    current.nextReceipt wave
  let tangent := wholeLatticeVorticityFourierTangentAt nu.coeff
    current.contact.physicalState wave
  let line : Real →L[Real] ComplexCoordinateVector :=
    (ContinuousLinearMap.id Real Real).smulRight tangent
  let eulerPath : Real → ComplexCoordinateVector := fun actual =>
    current.contact.physicalState wave + line actual
  let errorPath := fun actual => heatPath actual - eulerPath actual
  have lineOne : line 1 = tangent := by
    ext coordinate
    simp [line, tangent]
  have errorDerivative : ∀ actual : Real,
      HasDerivAt errorPath
        (fullReplayEulerErrorDerivative current wave actual) actual := by
    intro actual
    have eulerDerivative : HasDerivAt eulerPath tangent actual := by
      have generated := (line.hasDerivAt (x := actual)).const_add
        (current.contact.physicalState wave)
      simpa only [eulerPath, lineOne] using generated
    exact (fullReceipt_heatPath_hasDerivAt current wave actual).sub
      eulerDerivative
  have integralEq := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : Real)) (b := time.1)
    (f := errorPath) (f' := fullReplayEulerErrorDerivative current wave)
    (fun actual _ => errorDerivative actual)
    ((fullReplayEulerErrorDerivative_continuous current wave
      ).intervalIntegrable _ _)
  have heatAtTime : heatPath time.1 =
      current.nextReceipt.wholePath time wave := by
    exact (wholePath_wave_eq_actualWholeContinuousHeatDuhamelPath
      current.nextReceipt wave waveNe time).symm
  have heatZero : heatPath 0 = current.contact.physicalState wave :=
    fullReceipt_initialRow_eq_heatPath_zero current wave
  rw [integralEq]
  dsimp only [errorPath, eulerPath]
  rw [heatAtTime, heatZero]
  unfold fullReplayEulerRow
  have lineApply : line time.1 = time.1 • tangent := by
    ext coordinate
    simp [line]
  rw [lineApply]
  dsimp only [tangent]
  simp

private theorem fullReplayEulerErrorDerivative_norm_le
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (wave : IntegerWavevector)
    (waveNe : wave ≠ 0)
    (actual : Real)
    (actualMem : actual ∈ Icc (0 : Real)
      (wholeRestartDuration current.contact)) :
    ‖fullReplayEulerErrorDerivative current wave actual‖ ≤
      fullReplayEulerRemainderSlope current wave := by
  let receipt := current.nextReceipt
  let physicalTime : Icc (0 : Real) (wholeRestartDuration current.contact) :=
    ⟨actual, actualMem⟩
  let pathState : ComplexVorticityHilbertState :=
    (actualWholeProjectedTransversePath receipt actual).1
  let initialState : ComplexVorticityHilbertState :=
    current.contact.physicalState
  let radius := fullReplayEulerRadius current
  have pathStateEq : pathState = receipt.wholePath physicalTime := by
    change receipt.wholePath
        (projIcc 0 (wholeRestartDuration current.contact)
          (wholeRestartDuration_pos current.contact).le actual) =
      receipt.wholePath physicalTime
    rw [projIcc_of_mem (wholeRestartDuration_pos current.contact).le actualMem]
  have pathNormLe : ‖pathState‖ ≤ ‖receipt.wholePath‖ := by
    rw [pathStateEq]
    exact receipt.wholePath.norm_coe_le_norm physicalTime
  have radiusNonneg : 0 ≤ radius := by
    dsimp only [radius, fullReplayEulerRadius]
    positivity
  have differenceNormLe : ‖pathState - initialState‖ ≤ radius := by
    calc
      ‖pathState - initialState‖ ≤ ‖pathState‖ + ‖initialState‖ :=
        norm_sub_le _ _
      _ ≤ ‖receipt.wholePath‖ + ‖initialState‖ :=
        add_le_add pathNormLe le_rfl
      _ = radius := rfl
  have normSumLe : ‖pathState‖ + ‖initialState‖ ≤ radius :=
    (add_le_add pathNormLe le_rfl).trans_eq rfl
  have nonlinearLe :
      ‖actualWholeContinuousNonlinearRow receipt wave actual -
          wholeStateVorticityNonlinearCoefficientAt initialState wave‖ ≤
        6 * Real.sqrt (integerWaveNormSq wave) * radius ^ 2 := by
    have generated := wholeStateVorticityNonlinearCoefficientAt_sub_norm_le
      pathState initialState
      (actualWholeProjectedTransversePath receipt actual).2
      current.contact.transverse wave
    calc
      ‖actualWholeContinuousNonlinearRow receipt wave actual -
          wholeStateVorticityNonlinearCoefficientAt initialState wave‖ =
          ‖wholeStateVorticityNonlinearCoefficientAt pathState wave -
            wholeStateVorticityNonlinearCoefficientAt initialState wave‖ := rfl
      _ ≤ 6 * Real.sqrt (integerWaveNormSq wave) *
          ‖pathState - initialState‖ *
            (‖pathState‖ + ‖initialState‖) := generated
      _ ≤ 6 * Real.sqrt (integerWaveNormSq wave) * radius * radius := by
        have angularNonneg :
            0 ≤ 6 * Real.sqrt (integerWaveNormSq wave) := by positivity
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left differenceNormLe angularNonneg)
          normSumLe (add_nonneg (norm_nonneg _) (norm_nonneg _))
          (mul_nonneg angularNonneg radiusNonneg)
      _ = 6 * Real.sqrt (integerWaveNormSq wave) * radius ^ 2 := by ring
  have heatPathEq :
      actualWholeContinuousHeatDuhamelPath receipt wave actual =
        receipt.wholePath physicalTime wave :=
    (wholePath_wave_eq_actualWholeContinuousHeatDuhamelPath
      receipt wave waveNe physicalTime).symm
  have pathRowNormLe : ‖receipt.wholePath physicalTime wave‖ ≤
      ‖receipt.wholePath‖ :=
    (lp.norm_apply_le_norm (by norm_num)
      (receipt.wholePath physicalTime) wave).trans
        (receipt.wholePath.norm_coe_le_norm physicalTime)
  have initialRowNormLe : ‖initialState wave‖ ≤ ‖initialState‖ :=
    lp.norm_apply_le_norm (by norm_num) initialState wave
  have rowDifferenceLe :
      ‖actualWholeContinuousHeatDuhamelPath receipt wave actual -
          initialState wave‖ ≤ radius := by
    rw [heatPathEq]
    exact (norm_sub_le _ _).trans
      ((add_le_add pathRowNormLe initialRowNormLe).trans_eq rfl)
  have dampingNonneg :
      0 ≤ nu.coeff * integerWaveViscousMultiplier wave :=
    mul_nonneg nu.coeff_pos.le (by
      unfold integerWaveViscousMultiplier
      exact mul_nonneg (sq_nonneg _) (integerWaveNormSq_nonneg wave))
  unfold fullReplayEulerErrorDerivative
    wholeLatticeVorticityFourierTangentAt
  rw [show actualWholeContinuousNonlinearRow receipt wave actual -
          (nu.coeff * integerWaveViscousMultiplier wave) •
            actualWholeContinuousHeatDuhamelPath receipt wave actual -
        (wholeStateVorticityNonlinearCoefficientAt initialState wave -
          (nu.coeff * integerWaveViscousMultiplier wave) •
            initialState wave) =
      (actualWholeContinuousNonlinearRow receipt wave actual -
          wholeStateVorticityNonlinearCoefficientAt initialState wave) -
        (nu.coeff * integerWaveViscousMultiplier wave) •
          (actualWholeContinuousHeatDuhamelPath receipt wave actual -
            initialState wave) by module]
  calc
    ‖(actualWholeContinuousNonlinearRow receipt wave actual -
          wholeStateVorticityNonlinearCoefficientAt initialState wave) -
        (nu.coeff * integerWaveViscousMultiplier wave) •
          (actualWholeContinuousHeatDuhamelPath receipt wave actual -
            initialState wave)‖ ≤
        ‖actualWholeContinuousNonlinearRow receipt wave actual -
          wholeStateVorticityNonlinearCoefficientAt initialState wave‖ +
        ‖(nu.coeff * integerWaveViscousMultiplier wave) •
          (actualWholeContinuousHeatDuhamelPath receipt wave actual -
            initialState wave)‖ := norm_sub_le _ _
    _ ≤ 6 * Real.sqrt (integerWaveNormSq wave) * radius ^ 2 +
        (nu.coeff * integerWaveViscousMultiplier wave) * radius := by
      rw [norm_smul, Real.norm_of_nonneg dampingNonneg]
      exact add_le_add nonlinearLe
        (mul_le_mul_of_nonneg_left rowDifferenceLe dampingNonneg)
    _ = fullReplayEulerRemainderSlope current wave := rfl

/-- Every point of the unchanged canonical next receipt lies in the
source-generated full-replay Euler tube. -/
theorem fullReplay_row_sub_euler_norm_le
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (wave : IntegerWavevector)
    (waveNe : wave ≠ 0)
    (time : Icc (0 : Real) (wholeRestartDuration current.contact)) :
    ‖current.nextReceipt.wholePath time wave -
        fullReplayEulerRow current time.1 wave‖ ≤
      time.1 * fullReplayEulerRemainderSlope current wave := by
  rw [← fullReplayEulerError_integral_eq current wave waveNe time]
  calc
    ‖∫ actual in (0 : Real)..time.1,
        fullReplayEulerErrorDerivative current wave actual‖ ≤
        fullReplayEulerRemainderSlope current wave * |time.1 - 0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro actual actualMem
      apply fullReplayEulerErrorDerivative_norm_le
        current wave waveNe actual
      rw [uIoc_of_le time.2.1] at actualMem
      exact ⟨actualMem.1.le, actualMem.2.trans time.2.2⟩
    _ = time.1 * fullReplayEulerRemainderSlope current wave := by
      rw [sub_zero, abs_of_nonneg time.2.1]
      ring

/-! ## Finite-carrier assembly of the full Euler tube -/

/-- Canonical finite state assembled from the full-replay Euler rows. -/
def fullReplayFiniteEulerState
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector)
    (time : Real) : ComplexVorticityHilbertState :=
  finiteComplexVorticityState modes
    (fullReplayEulerRow current time)

/-- Exact finite coefficient-energy escrow assembled from the rowwise tube. -/
def fullReplayFiniteEulerErrorEnergy
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector)
    (time : Real) : Real :=
  ∑ wave ∈ modes,
    3 * (time * fullReplayEulerRemainderSlope current wave) ^ 2

theorem fullReplayFiniteEulerErrorEnergy_nonneg
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector)
    (time : Real) :
    0 ≤ fullReplayFiniteEulerErrorEnergy current modes time := by
  unfold fullReplayFiniteEulerErrorEnergy
  exact Finset.sum_nonneg fun wave _ =>
    mul_nonneg (by norm_num) (sq_nonneg _)

/-- The actual finite projection of every full-receipt state lies in the
assembled Euler ball, with no target displacement supplied by a caller. -/
theorem fullReplay_projection_sub_finiteEuler_norm_le
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector)
    (zeroNotMem : (0 : IntegerWavevector) ∉ modes)
    (time : Icc (0 : Real) (wholeRestartDuration current.contact)) :
    ‖complexSharpSupportProjection modes
          (current.nextReceipt.wholePath time) -
        fullReplayFiniteEulerState current modes time.1‖ ≤
      Real.sqrt
        (fullReplayFiniteEulerErrorEnergy current modes time.1) := by
  let errorState :=
    complexSharpSupportProjection modes
        (current.nextReceipt.wholePath time) -
      fullReplayFiniteEulerState current modes time.1
  have errorSupported : ∀ wave : IntegerWavevector,
      wave ∉ modes → errorState wave = 0 := by
    intro wave waveNotMem
    dsimp only [errorState, fullReplayFiniteEulerState]
    change
      complexSharpSupportProjection modes
            (current.nextReceipt.wholePath time) wave -
          finiteComplexVorticityState modes
            (fullReplayEulerRow current time.1) wave = 0
    rw [complexSharpSupportProjection_apply,
      if_neg waveNotMem, finiteComplexVorticityState_apply,
      if_neg waveNotMem, sub_zero]
  have normSqLeFinite :
      ‖errorState‖ ^ 2 ≤
        finiteStateVorticityCoefficientEnstrophy modes errorState :=
    complexVorticityHilbertState_norm_sq_le_coefficientEnstrophy
      modes errorState errorSupported
  have finiteLe :
      finiteStateVorticityCoefficientEnstrophy modes errorState ≤
        fullReplayFiniteEulerErrorEnergy current modes time.1 := by
    unfold finiteStateVorticityCoefficientEnstrophy
      fullReplayFiniteEulerErrorEnergy
    apply Finset.sum_le_sum
    intro wave waveMem
    have waveNe : wave ≠ 0 := fun waveZero =>
      zeroNotMem (waveZero ▸ waveMem)
    have rowBound := fullReplay_row_sub_euler_norm_le
      current wave waveNe time
    have amplitudeLe :=
      complexCoordinateAmplitudeSq_le_three_mul_norm_sq (errorState wave)
    have errorRow :
        errorState wave =
          current.nextReceipt.wholePath time wave -
            fullReplayEulerRow current time.1 wave := by
      dsimp only [errorState, fullReplayFiniteEulerState]
      change
        complexSharpSupportProjection modes
              (current.nextReceipt.wholePath time) wave -
            finiteComplexVorticityState modes
              (fullReplayEulerRow current time.1) wave = _
      rw [complexSharpSupportProjection_apply,
        if_pos waveMem, finiteComplexVorticityState_apply,
        if_pos waveMem]
    rw [errorRow] at amplitudeLe
    calc
      complexCoordinateAmplitudeSq (errorState wave) ≤
          3 * ‖current.nextReceipt.wholePath time wave -
            fullReplayEulerRow current time.1 wave‖ ^ 2 := by
        simpa only [errorRow] using amplitudeLe
      _ ≤ 3 *
          (time.1 * fullReplayEulerRemainderSlope current wave) ^ 2 := by
        exact mul_le_mul_of_nonneg_left
          ((sq_le_sq₀ (norm_nonneg _)
            (mul_nonneg time.2.1
              (fullReplayEulerRemainderSlope_nonneg current wave))).2
            rowBound)
          (by norm_num)
  have normSqLe := normSqLeFinite.trans finiteLe
  have energyNonneg :=
    fullReplayFiniteEulerErrorEnergy_nonneg current modes time.1
  change ‖errorState‖ ≤ _
  exact (Real.le_sqrt (norm_nonneg _) energyNonneg).2 normSqLe

/-- The current row pays the entire full-horizon tube loss, while the exact
current tangent is nonnegative in the same source-fixed phase direction. -/
def fullReplayPhaseConeHasEulerMargin
    {nu : Viscosity}
    (cone : FiniteFourierPhaseCone)
    (current : GeneratedWholeRestartCurrent nu) : Prop :=
  ∀ wave ∈ cone.modes,
    0 ≤ complexCoordinateRealInner (cone.axis wave)
        (current.contact.physicalState wave) ∧
    0 ≤ complexCoordinateRealInner (cone.axis wave)
        (wholeLatticeVorticityFourierTangentAt nu.coeff
          current.contact.physicalState wave) ∧
    3 * ‖cone.axis wave‖ * wholeRestartDuration current.contact *
        fullReplayEulerRemainderSlope current wave ≤
      complexCoordinateRealInner (cone.axis wave)
        (current.contact.physicalState wave)

/-- Stronger finite source mouth with the entire receipt norm and duration
already eliminated into the canonical seventh-order scale law. -/
def fullReplayPhaseConeHasSourceMargin
    {nu : Viscosity}
    (cone : FiniteFourierPhaseCone)
    (current : GeneratedWholeRestartCurrent nu) : Prop :=
  ∀ wave ∈ cone.modes,
    0 ≤ complexCoordinateRealInner (cone.axis wave)
        (wholeLatticeVorticityFourierTangentAt nu.coeff
          current.contact.physicalState wave) ∧
    3 * ‖cone.axis wave‖ *
        fullReplayEulerTubePaymentUpper current wave ≤
      complexCoordinateRealInner (cone.axis wave)
        (current.contact.physicalState wave)

/-- Strongest easy-to-calculate mouth: the seventh-order clock and
first-order row dynamics have already collapsed to an inverse-sixth scale
factor. -/
def fullReplayPhaseConeHasInverseSixthMargin
    {nu : Viscosity}
    (cone : FiniteFourierPhaseCone)
    (current : GeneratedWholeRestartCurrent nu) : Prop :=
  ∀ wave ∈ cone.modes,
    0 ≤ complexCoordinateRealInner (cone.axis wave)
        (wholeLatticeVorticityFourierTangentAt nu.coeff
          current.contact.physicalState wave) ∧
    3 * ‖cone.axis wave‖ *
        fullReplayEulerTubeInverseSixthUpper current wave ≤
      complexCoordinateRealInner (cone.axis wave)
        (current.contact.physicalState wave)

theorem fullReplayPhaseConeHasSourceMargin_of_inverseSixth
    {nu : Viscosity}
    (cone : FiniteFourierPhaseCone)
    (current : GeneratedWholeRestartCurrent nu)
    (margin : fullReplayPhaseConeHasInverseSixthMargin cone current) :
    fullReplayPhaseConeHasSourceMargin cone current := by
  intro wave waveMem
  have generated := margin wave waveMem
  refine ⟨generated.1, ?_⟩
  exact (mul_le_mul_of_nonneg_left
    (fullReplayEulerTubePaymentUpper_le_inverseSixth current wave)
    (by positivity)).trans generated.2

theorem fullReplayPhaseConeHasEulerMargin_of_sourceMargin
    {nu : Viscosity}
    (cone : FiniteFourierPhaseCone)
    (current : GeneratedWholeRestartCurrent nu)
    (margin : fullReplayPhaseConeHasSourceMargin cone current) :
    fullReplayPhaseConeHasEulerMargin cone current := by
  intro wave waveMem
  have sourceMargin := margin wave waveMem
  have paymentNonneg :=
    fullReplayEulerTubePaymentUpper_nonneg current wave
  have axisCoefficientNonneg : 0 ≤ 3 * ‖cone.axis wave‖ := by positivity
  have sourceNonneg :
      0 ≤ complexCoordinateRealInner (cone.axis wave)
        (current.contact.physicalState wave) :=
    (mul_nonneg axisCoefficientNonneg paymentNonneg).trans
      sourceMargin.2
  have tubeLe := fullReplay_duration_mul_remainderSlope_le_sourceUpper
    current wave
  have scaledTubeLe :
      3 * ‖cone.axis wave‖ * wholeRestartDuration current.contact *
          fullReplayEulerRemainderSlope current wave ≤
        3 * ‖cone.axis wave‖ *
          fullReplayEulerTubePaymentUpper current wave := by
    calc
      3 * ‖cone.axis wave‖ * wholeRestartDuration current.contact *
            fullReplayEulerRemainderSlope current wave =
          (3 * ‖cone.axis wave‖) *
            (wholeRestartDuration current.contact *
              fullReplayEulerRemainderSlope current wave) := by ring
      _ ≤ (3 * ‖cone.axis wave‖) *
          fullReplayEulerTubePaymentUpper current wave :=
        mul_le_mul_of_nonneg_left tubeLe axisCoefficientNonneg
  exact ⟨sourceNonneg, sourceMargin.1,
    scaledTubeLe.trans sourceMargin.2⟩

/-- A source-side full-edge Euler margin keeps every actual point of the
canonical next receipt inside the same candidate cone. -/
theorem finiteFourierPhaseCone_fullReceipt_holds_of_eulerMargin
    {nu : Viscosity}
    (cone : FiniteFourierPhaseCone)
    (current : GeneratedWholeRestartCurrent nu)
    (margin : fullReplayPhaseConeHasEulerMargin cone current)
    (time : Icc (0 : Real) (wholeRestartDuration current.contact)) :
    cone.Holds (current.nextReceipt.wholePath time) := by
  intro wave waveMem
  have waveNe : wave ≠ 0 := fun waveZero =>
    cone.zeroNotMem (waveZero ▸ waveMem)
  have remainder := fullReplay_row_sub_euler_norm_le
    current wave waveNe time
  have pairingBound := abs_complexCoordinateRealInner_le_three_mul_norm
    (cone.axis wave)
    (current.nextReceipt.wholePath time wave -
      fullReplayEulerRow current time.1 wave)
  have absoluteBound :
      |complexCoordinateRealInner (cone.axis wave)
          (current.nextReceipt.wholePath time wave -
            fullReplayEulerRow current time.1 wave)| ≤
        3 * ‖cone.axis wave‖ * time.1 *
          fullReplayEulerRemainderSlope current wave := by
    calc
      |complexCoordinateRealInner (cone.axis wave)
          (current.nextReceipt.wholePath time wave -
            fullReplayEulerRow current time.1 wave)| ≤
          3 * ‖cone.axis wave‖ *
            ‖current.nextReceipt.wholePath time wave -
              fullReplayEulerRow current time.1 wave‖ := pairingBound
      _ ≤ 3 * ‖cone.axis wave‖ *
          (time.1 * fullReplayEulerRemainderSlope current wave) :=
        mul_le_mul_of_nonneg_left remainder (by positivity)
      _ = 3 * ‖cone.axis wave‖ * time.1 *
          fullReplayEulerRemainderSlope current wave := by ring
  have errorLower :
      -(3 * ‖cone.axis wave‖ * time.1 *
          fullReplayEulerRemainderSlope current wave) ≤
        complexCoordinateRealInner (cone.axis wave)
          (current.nextReceipt.wholePath time wave -
            fullReplayEulerRow current time.1 wave) := by
    exact (neg_le_neg absoluteBound).trans (neg_abs_le _)
  have source := (margin wave waveMem).1
  have tangent := (margin wave waveMem).2.1
  have fullMargin := (margin wave waveMem).2.2
  have localMargin :
      3 * ‖cone.axis wave‖ * time.1 *
          fullReplayEulerRemainderSlope current wave ≤
        complexCoordinateRealInner (cone.axis wave)
          (current.contact.physicalState wave) := by
    have coefficientNonneg :
        0 ≤ 3 * ‖cone.axis wave‖ *
          fullReplayEulerRemainderSlope current wave :=
      mul_nonneg
        (mul_nonneg (by norm_num) (norm_nonneg _))
        (fullReplayEulerRemainderSlope_nonneg current wave)
    calc
      3 * ‖cone.axis wave‖ * time.1 *
          fullReplayEulerRemainderSlope current wave =
          (3 * ‖cone.axis wave‖ *
            fullReplayEulerRemainderSlope current wave) * time.1 := by ring
      _ ≤ (3 * ‖cone.axis wave‖ *
            fullReplayEulerRemainderSlope current wave) *
          wholeRestartDuration current.contact :=
        mul_le_mul_of_nonneg_left time.2.2 coefficientNonneg
      _ = 3 * ‖cone.axis wave‖ *
          wholeRestartDuration current.contact *
            fullReplayEulerRemainderSlope current wave := by ring
      _ ≤ _ := fullMargin
  have eulerPairNonneg :
      0 ≤ complexCoordinateRealInner (cone.axis wave)
        (fullReplayEulerRow current time.1 wave) := by
    unfold fullReplayEulerRow
    rw [complexCoordinateRealInner_add_right,
      complexCoordinateRealInner_real_smul_right]
    exact add_nonneg source (mul_nonneg time.2.1 tangent)
  have split :
      complexCoordinateRealInner (cone.axis wave)
          (current.nextReceipt.wholePath time wave) =
        complexCoordinateRealInner (cone.axis wave)
            (fullReplayEulerRow current time.1 wave) +
          complexCoordinateRealInner (cone.axis wave)
            (current.nextReceipt.wholePath time wave -
              fullReplayEulerRow current time.1 wave) := by
    rw [complexCoordinateRealInner_sub_right]
    ring
  rw [split]
  have paidEuler :
      3 * ‖cone.axis wave‖ * time.1 *
          fullReplayEulerRemainderSlope current wave ≤
        complexCoordinateRealInner (cone.axis wave)
          (fullReplayEulerRow current time.1 wave) :=
    localMargin.trans (by
      unfold fullReplayEulerRow
      rw [complexCoordinateRealInner_add_right,
        complexCoordinateRealInner_real_smul_right]
      exact le_add_of_nonneg_right (mul_nonneg time.2.1 tangent))
  linarith

end
end ThreeDimensionalVorticityCoefficientFullReceiptFourierConeAdvance
end NavierStokes
end SaturationMonoid
