import H0mework.NavierStokes.Accumulation.MovingInventoryScaleRelativeClockFold
import H0mework.NavierStokes.Accumulation.InstantaneousWholeNetPowerCapture
import H0mework.NavierStokes.PairRestart.PairOccurrenceWork
import H0mework.NavierStokes.PairRestart.SourcePairOccurrence
import H0mework.NavierStokes.GeneratedPaths.InfiniteNonlinearRowLimit

/-!
# Actual Fourier-cone advance on one whole-restart edge

For every nonzero Fourier row, the exact selected successor is placed in a
source-generated Euler tube whose center uses the complete summed whole NS
tangent.  The remainder is bounded from the current receipt and current
state; no target coefficient, Taylor table, future recurrence, branch or
payment is accepted.

The rowwise tube is also folded into a finite lower enclosure.  A
coverage-complete no-go proves that this coarse global-radius enclosure is
always nonpositive, so it cannot be promoted into a physical payment.

The nondegenerate route instead integrates the complete projected net-power
on the same selected prefix.  A current-indexed actual phase cone then pays
the moving-inventory ledger exactly.  A concrete source must generate this
cone recursively across the existing `nextContact`; no target coefficient,
Taylor table, future branch, or payment is accepted.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped ENNReal Topology Interval

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartActualFourierConeAdvance

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinAmbientNorm
open ThreeDimensionalVorticityCoefficientFiniteGalerkinMildDuhamel
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteMildDuhamel
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientCanonicalExhaustiveGalerkinTarget
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageHilbertCompletion
open ThreeDimensionalVorticityCoefficientWholeKineticDifferenceCancellation
open ThreeDimensionalVorticityCoefficientWholeTangentEnergyTransport
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeCriticalSerrin
open ThreeDimensionalVorticityCoefficientWholeSerrinEnstrophyGronwall
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinOverlap
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSourcePairOccurrence
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairOccurrenceWork
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEnstrophyWork
open ThreeDimensionalVorticityCoefficientGeneratedPathInfiniteNonlinearRowLimit
open ThreeDimensionalVorticityCoefficientGeneratedPathInfiniteNonlinearNegativeOneTimeBudget
open ThreeDimensionalVorticityCoefficientGeneratedPathFiniteObservedCompactness
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartWholeContinuousMildSerrin
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartFiniteObservedCompactness
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationNativeTurbulenceLaw
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationNonlinearDuhamelConcentration
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeTemporalEnstrophyLedger
open ThreeDimensionalVorticityCoefficientInstantaneousWholeNetPowerCapture
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartMovingInventoryScaleRelativeClockFold
open ThreeDimensionalVorticityCoefficientWholeStateSourceOwnedLocalBarrier

noncomputable section

def nextContactEulerRow
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (wave : IntegerWavevector) : ComplexCoordinateVector :=
  current.contact.physicalState wave +
    current.nextContact.time.1 •
      wholeLatticeVorticityFourierTangentAt nu.coeff
        current.contact.physicalState wave

def nextContactEulerRadius
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu) : Real :=
  ‖current.nextContact.prefixReceipt.wholePath‖ +
    ‖current.contact.physicalState‖

def nextContactEulerRemainderSlope
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (wave : IntegerWavevector) : Real :=
  6 * Real.sqrt (integerWaveNormSq wave) *
      nextContactEulerRadius current ^ 2 +
    (nu.coeff * integerWaveViscousMultiplier wave) *
      nextContactEulerRadius current

private theorem initialRow_eq_heatPath_zero
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (wave : IntegerWavevector) :
    actualWholeContinuousHeatDuhamelPath
        current.nextContact.prefixReceipt wave 0 =
      current.contact.physicalState wave := by
  unfold actualWholeContinuousHeatDuhamelPath
    heatDuhamelComplexCoordinatePath
    intervalIntegralComplexCoordinatePath
  simp

private theorem heatPath_hasDerivAt
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (wave : IntegerWavevector)
    (actual : Real) :
    HasDerivAt
      (actualWholeContinuousHeatDuhamelPath
        current.nextContact.prefixReceipt wave)
      (actualWholeContinuousNonlinearRow
          current.nextContact.prefixReceipt wave actual -
        (nu.coeff * integerWaveViscousMultiplier wave) •
          actualWholeContinuousHeatDuhamelPath
            current.nextContact.prefixReceipt wave actual)
      actual := by
  exact heatDuhamelComplexCoordinatePath_hasDerivAt_of_continuous
    (current.contact.physicalState wave)
    (actualWholeContinuousNonlinearRow
      current.nextContact.prefixReceipt wave)
    (nu.coeff * integerWaveViscousMultiplier wave) 0 actual
    (actualWholeContinuousNonlinearRow_continuous
      current.nextContact.prefixReceipt wave)

private def eulerErrorDerivative
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (wave : IntegerWavevector)
    (actual : Real) : ComplexCoordinateVector :=
  (actualWholeContinuousNonlinearRow
        current.nextContact.prefixReceipt wave actual -
      (nu.coeff * integerWaveViscousMultiplier wave) •
        actualWholeContinuousHeatDuhamelPath
          current.nextContact.prefixReceipt wave actual) -
    wholeLatticeVorticityFourierTangentAt nu.coeff
      current.contact.physicalState wave

private theorem eulerErrorDerivative_continuous
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (wave : IntegerWavevector) :
    Continuous (eulerErrorDerivative current wave) := by
  unfold eulerErrorDerivative
  have heatContinuous : Continuous
      (actualWholeContinuousHeatDuhamelPath
        current.nextContact.prefixReceipt wave) := by
    rw [continuous_iff_continuousAt]
    intro actual
    exact (heatPath_hasDerivAt current wave actual).continuousAt
  exact
    ((actualWholeContinuousNonlinearRow_continuous
        current.nextContact.prefixReceipt wave).sub
      (heatContinuous.const_smul
        (nu.coeff * integerWaveViscousMultiplier wave))).sub
      continuous_const

private theorem eulerError_integral_eq
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (wave : IntegerWavevector)
    (waveNe : wave ≠ 0) :
    (∫ actual in (0 : Real)..current.nextContact.time.1,
        eulerErrorDerivative current wave actual) =
      current.nextContact.physicalState wave -
        nextContactEulerRow current wave := by
  let heatPath := actualWholeContinuousHeatDuhamelPath
    current.nextContact.prefixReceipt wave
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
      HasDerivAt errorPath (eulerErrorDerivative current wave actual) actual := by
    intro actual
    have eulerDerivative : HasDerivAt eulerPath tangent actual := by
      have generated :=
        (line.hasDerivAt (x := actual)).const_add
          (current.contact.physicalState wave)
      simpa only [eulerPath, lineOne] using generated
    exact (heatPath_hasDerivAt current wave actual).sub eulerDerivative
  have integralEq := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : Real)) (b := current.nextContact.time.1)
    (f := errorPath) (f' := eulerErrorDerivative current wave)
    (fun actual _ => errorDerivative actual)
    ((eulerErrorDerivative_continuous current wave).intervalIntegrable _ _)
  have heatTerminal : heatPath current.nextContact.time.1 =
      current.nextContact.physicalState wave := by
    let terminal : Icc (0 : Real) current.nextContact.time.1 :=
      ⟨current.nextContact.time.1,
        current.nextContact.time_pos.le, le_rfl⟩
    rw [show heatPath current.nextContact.time.1 =
        current.nextContact.prefixReceipt.wholePath terminal wave by
      symm
      exact wholePath_wave_eq_actualWholeContinuousHeatDuhamelPath
        current.nextContact.prefixReceipt wave waveNe terminal]
    exact congrArg (fun state => state wave)
      current.nextContact.prefixReceipt_terminal
  have heatZero : heatPath 0 = current.contact.physicalState wave :=
    initialRow_eq_heatPath_zero current wave
  change (∫ actual in (0 : Real)..current.nextContact.time.1,
      eulerErrorDerivative current wave actual) = _
  rw [integralEq]
  dsimp only [errorPath, eulerPath]
  rw [heatTerminal, heatZero]
  unfold nextContactEulerRow
  have lineApply : line current.nextContact.time.1 =
      current.nextContact.time.1 • tangent := by
    ext coordinate
    simp [line]
  rw [lineApply]
  dsimp only [tangent]
  simp

private theorem eulerErrorDerivative_norm_le
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (wave : IntegerWavevector)
    (waveNe : wave ≠ 0)
    (actual : Real)
    (actualMem : actual ∈ Icc (0 : Real) current.nextContact.time.1) :
    ‖eulerErrorDerivative current wave actual‖ ≤
      nextContactEulerRemainderSlope current wave := by
  let receipt := current.nextContact.prefixReceipt
  let physicalTime : Icc (0 : Real) current.nextContact.time.1 :=
    ⟨actual, actualMem⟩
  let pathState : ComplexVorticityHilbertState :=
    (actualWholeProjectedTransversePath receipt actual).1
  let initialState : ComplexVorticityHilbertState :=
    current.contact.physicalState
  let radius := nextContactEulerRadius current
  have pathStateEq : pathState = receipt.wholePath physicalTime := by
    change receipt.wholePath
        (projIcc 0 current.nextContact.time.1
          current.nextContact.time_pos.le actual) =
      receipt.wholePath physicalTime
    rw [projIcc_of_mem current.nextContact.time_pos.le actualMem]
  have pathNormLe : ‖pathState‖ ≤ ‖receipt.wholePath‖ := by
    rw [pathStateEq]
    exact receipt.wholePath.norm_coe_le_norm physicalTime
  have radiusNonneg : 0 ≤ radius := by
    dsimp only [radius, nextContactEulerRadius]
    positivity
  have differenceNormLe : ‖pathState - initialState‖ ≤ radius := by
    calc
      ‖pathState - initialState‖ ≤ ‖pathState‖ + ‖initialState‖ :=
        norm_sub_le _ _
      _ ≤ ‖receipt.wholePath‖ + ‖initialState‖ :=
        add_le_add pathNormLe le_rfl
      _ = radius := rfl
  have normSumLe : ‖pathState‖ + ‖initialState‖ ≤ radius := by
    exact (add_le_add pathNormLe le_rfl).trans_eq rfl
  have nonlinearLe :
      ‖actualWholeContinuousNonlinearRow receipt wave actual -
          wholeStateVorticityNonlinearCoefficientAt initialState wave‖ ≤
        6 * Real.sqrt (integerWaveNormSq wave) * radius ^ 2 := by
    have generated :=
      wholeStateVorticityNonlinearCoefficientAt_sub_norm_le
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
        calc
          6 * Real.sqrt (integerWaveNormSq wave) *
                ‖pathState - initialState‖ *
              (‖pathState‖ + ‖initialState‖) ≤
              6 * Real.sqrt (integerWaveNormSq wave) * radius *
                (‖pathState‖ + ‖initialState‖) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left differenceNormLe angularNonneg)
              (add_nonneg (norm_nonneg _) (norm_nonneg _))
          _ ≤ 6 * Real.sqrt (integerWaveNormSq wave) * radius * radius :=
            mul_le_mul_of_nonneg_left normSumLe
              (mul_nonneg angularNonneg radiusNonneg)
      _ = 6 * Real.sqrt (integerWaveNormSq wave) * radius ^ 2 := by ring
  have heatPathEq :
      actualWholeContinuousHeatDuhamelPath receipt wave actual =
        receipt.wholePath physicalTime wave := by
    exact (wholePath_wave_eq_actualWholeContinuousHeatDuhamelPath
      receipt wave waveNe physicalTime).symm
  have pathRowNormLe : ‖receipt.wholePath physicalTime wave‖ ≤
      ‖receipt.wholePath‖ := by
    exact (lp.norm_apply_le_norm (by norm_num)
      (receipt.wholePath physicalTime) wave).trans
        (receipt.wholePath.norm_coe_le_norm physicalTime)
  have initialRowNormLe : ‖initialState wave‖ ≤ ‖initialState‖ :=
    lp.norm_apply_le_norm (by norm_num) initialState wave
  have rowDifferenceLe :
      ‖actualWholeContinuousHeatDuhamelPath receipt wave actual -
          initialState wave‖ ≤ radius := by
    rw [heatPathEq]
    calc
      ‖receipt.wholePath physicalTime wave - initialState wave‖ ≤
          ‖receipt.wholePath physicalTime wave‖ + ‖initialState wave‖ :=
        norm_sub_le _ _
      _ ≤ ‖receipt.wholePath‖ + ‖initialState‖ :=
        add_le_add pathRowNormLe initialRowNormLe
      _ = radius := rfl
  have dampingNonneg :
      0 ≤ nu.coeff * integerWaveViscousMultiplier wave :=
    mul_nonneg nu.coeff_pos.le
      (by
        unfold integerWaveViscousMultiplier
        exact mul_nonneg (sq_nonneg _)
          (integerWaveNormSq_nonneg wave))
  unfold eulerErrorDerivative wholeLatticeVorticityFourierTangentAt
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
    _ = nextContactEulerRemainderSlope current wave := rfl

/-- The actual selected successor lies in the source-generated one-step
Euler tube.  Its radius reads only the current whole receipt norm, current
state norm, exact contact time, viscosity and output frequency. -/
theorem nextContact_row_sub_euler_norm_le
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (wave : IntegerWavevector)
    (waveNe : wave ≠ 0) :
    ‖current.nextContact.physicalState wave -
        nextContactEulerRow current wave‖ ≤
      current.nextContact.time.1 *
        nextContactEulerRemainderSlope current wave := by
  rw [← eulerError_integral_eq current wave waveNe]
  calc
    ‖∫ actual in (0 : Real)..current.nextContact.time.1,
        eulerErrorDerivative current wave actual‖ ≤
        nextContactEulerRemainderSlope current wave *
          |current.nextContact.time.1 - 0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro actual actualMem
      apply eulerErrorDerivative_norm_le current wave waveNe actual
      rw [uIoc_of_le current.nextContact.time_pos.le] at actualMem
      exact ⟨actualMem.1.le, actualMem.2⟩
    _ = current.nextContact.time.1 *
        nextContactEulerRemainderSlope current wave := by
      rw [sub_zero, abs_of_pos current.nextContact.time_pos]
      ring

structure FiniteFourierPhaseCone where
  modes : Finset IntegerWavevector
  zeroNotMem : (0 : IntegerWavevector) ∉ modes
  axis : IntegerWavevector → ComplexCoordinateVector

def FiniteFourierPhaseCone.Holds
    (cone : FiniteFourierPhaseCone)
    (state : ComplexVorticityHilbertState) : Prop :=
  ∀ wave ∈ cone.modes,
    0 ≤ complexCoordinateRealInner (cone.axis wave) (state wave)

/-- Entirely source-side margin test for one generated next edge.  The
right side is the complete summed NS Euler row, not a pairwise incidence or
target coefficient. -/
def FiniteFourierPhaseCone.HasNextEulerMargin
    {nu : Viscosity}
    (cone : FiniteFourierPhaseCone)
    (current : GeneratedWholeRestartCurrent nu) : Prop :=
  ∀ wave ∈ cone.modes,
    3 * ‖cone.axis wave‖ * current.nextContact.time.1 *
          nextContactEulerRemainderSlope current wave ≤
      complexCoordinateRealInner (cone.axis wave)
        (nextContactEulerRow current wave)

theorem FiniteFourierPhaseCone.nextContact_holds_of_eulerMargin
    {nu : Viscosity}
    (cone : FiniteFourierPhaseCone)
    (current : GeneratedWholeRestartCurrent nu)
    (margin : cone.HasNextEulerMargin current) :
    cone.Holds current.nextContact.physicalState := by
  intro wave waveMem
  have waveNe : wave ≠ 0 := fun waveZero =>
    cone.zeroNotMem (waveZero ▸ waveMem)
  have remainder := nextContact_row_sub_euler_norm_le current wave waveNe
  have pairingBound :=
    abs_complexCoordinateRealInner_le_three_mul_norm
      (cone.axis wave)
      (current.nextContact.physicalState wave -
        nextContactEulerRow current wave)
  have absoluteBound :
      |complexCoordinateRealInner (cone.axis wave)
          (current.nextContact.physicalState wave -
            nextContactEulerRow current wave)| ≤
        3 * ‖cone.axis wave‖ * current.nextContact.time.1 *
          nextContactEulerRemainderSlope current wave := by
    calc
      |complexCoordinateRealInner (cone.axis wave)
          (current.nextContact.physicalState wave -
            nextContactEulerRow current wave)| ≤
          3 * ‖cone.axis wave‖ *
            ‖current.nextContact.physicalState wave -
              nextContactEulerRow current wave‖ := pairingBound
      _ ≤ 3 * ‖cone.axis wave‖ *
          (current.nextContact.time.1 *
            nextContactEulerRemainderSlope current wave) := by
        exact mul_le_mul_of_nonneg_left remainder (by positivity)
      _ = 3 * ‖cone.axis wave‖ * current.nextContact.time.1 *
          nextContactEulerRemainderSlope current wave := by ring
  have errorLower :
      -(3 * ‖cone.axis wave‖ * current.nextContact.time.1 *
          nextContactEulerRemainderSlope current wave) ≤
        complexCoordinateRealInner (cone.axis wave)
          (current.nextContact.physicalState wave -
            nextContactEulerRow current wave) := by
    have negAbsLe := neg_abs_le
      (complexCoordinateRealInner (cone.axis wave)
        (current.nextContact.physicalState wave -
          nextContactEulerRow current wave))
    linarith
  have sourceMargin := margin wave waveMem
  have split :
      complexCoordinateRealInner (cone.axis wave)
          (current.nextContact.physicalState wave) =
        complexCoordinateRealInner (cone.axis wave)
            (nextContactEulerRow current wave) +
          complexCoordinateRealInner (cone.axis wave)
            (current.nextContact.physicalState wave -
              nextContactEulerRow current wave) := by
    rw [complexCoordinateRealInner_sub_right]
    ring
  rw [split]
  linarith

def nextContactEulerPaymentDensity
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (wave : IntegerWavevector) : Real :=
  2 * complexCoordinateRealInner
      (current.contact.physicalState wave)
      (wholeLatticeVorticityFourierTangentAt nu.coeff
        current.contact.physicalState wave) -
    6 * ‖current.contact.physicalState wave‖ *
      nextContactEulerRemainderSlope current wave

/-- The first-order Euler tube is a faithful update enclosure but its global
radius is too coarse to be a positive payment producer: row by row, the
subtracted allowance already dominates the absolute gross Euler pairing. -/
theorem nextContactEulerPaymentDensity_nonpos
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (wave : IntegerWavevector) :
    nextContactEulerPaymentDensity current wave ≤ 0 := by
  let state := current.contact.physicalState
  let radius := nextContactEulerRadius current
  let angular := 6 * Real.sqrt (integerWaveNormSq wave)
  let viscous := nu.coeff * integerWaveViscousMultiplier wave
  have angularNonneg : 0 ≤ angular := by
    dsimp only [angular]
    positivity
  have viscousNonneg : 0 ≤ viscous := by
    dsimp only [viscous]
    exact mul_nonneg nu.coeff_pos.le (by
      unfold integerWaveViscousMultiplier
      exact mul_nonneg (sq_nonneg _)
        (integerWaveNormSq_nonneg wave))
  have stateNormLeRadius : ‖state‖ ≤ radius := by
    dsimp only [state, radius, nextContactEulerRadius]
    linarith [norm_nonneg current.nextContact.prefixReceipt.wholePath]
  have radiusNonneg : 0 ≤ radius :=
    (norm_nonneg state).trans stateNormLeRadius
  have rowNormLeState : ‖state wave‖ ≤ ‖state‖ :=
    lp.norm_apply_le_norm (by norm_num) state wave
  have rowNormLeRadius : ‖state wave‖ ≤ radius :=
    rowNormLeState.trans stateNormLeRadius
  have nonlinearNormLe :
      ‖wholeStateVorticityNonlinearCoefficientAt state wave‖ ≤
        angular * ‖state‖ ^ 2 := by
    have generated := wholeStateVorticityBilinearCoefficientAt_norm_le
      state state current.contact.transverse wave
    rw [wholeStateVorticityBilinearCoefficientAt_self] at generated
    simpa only [angular, pow_two, mul_assoc] using generated
  have stateSquareLe : ‖state‖ ^ 2 ≤ radius ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) radiusNonneg).2 stateNormLeRadius
  have nonlinearRadiusLe :
      ‖wholeStateVorticityNonlinearCoefficientAt state wave‖ ≤
        angular * radius ^ 2 :=
    nonlinearNormLe.trans
      (mul_le_mul_of_nonneg_left stateSquareLe angularNonneg)
  have viscousRowLe : ‖viscous • state wave‖ ≤ viscous * radius := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg viscousNonneg]
    exact mul_le_mul_of_nonneg_left rowNormLeRadius viscousNonneg
  have tangentNormLe :
      ‖wholeLatticeVorticityFourierTangentAt
          nu.coeff state wave‖ ≤
        nextContactEulerRemainderSlope current wave := by
    unfold wholeLatticeVorticityFourierTangentAt
    change
      ‖wholeStateVorticityNonlinearCoefficientAt state wave -
          viscous • state wave‖ ≤ _
    calc
      ‖wholeStateVorticityNonlinearCoefficientAt state wave -
          viscous • state wave‖ ≤
          ‖wholeStateVorticityNonlinearCoefficientAt state wave‖ +
            ‖viscous • state wave‖ := norm_sub_le _ _
      _ ≤ angular * radius ^ 2 + viscous * radius :=
        add_le_add nonlinearRadiusLe viscousRowLe
      _ = nextContactEulerRemainderSlope current wave := by
        rfl
  have pairingAbs := abs_complexCoordinateRealInner_le_three_mul_norm
    (state wave)
    (wholeLatticeVorticityFourierTangentAt nu.coeff state wave)
  have grossLe :
      2 * complexCoordinateRealInner (state wave)
          (wholeLatticeVorticityFourierTangentAt nu.coeff state wave) ≤
        6 * ‖state wave‖ *
          nextContactEulerRemainderSlope current wave := by
    have innerLeAbs := le_abs_self
      (complexCoordinateRealInner (state wave)
        (wholeLatticeVorticityFourierTangentAt nu.coeff state wave))
    have scaleNonneg : 0 ≤ 6 * ‖state wave‖ :=
      mul_nonneg (by norm_num) (norm_nonneg _)
    have scaledTangent := mul_le_mul_of_nonneg_left tangentNormLe
      scaleNonneg
    nlinarith
  unfold nextContactEulerPaymentDensity
  dsimp only [state] at grossLe ⊢
  linarith

/-- At time zero, the projected physical net-power is exactly the gross
whole-lattice Euler work of the receipt's own initial state.  No support
closure is required: the projection is evaluated only on rows belonging to
the displayed finite inventory. -/
theorem actualProjectedWholeNetEnstrophyPower_zero_eq_wholeTangentWork
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (modes : Finset IntegerWavevector) :
    actualProjectedWholeNetEnstrophyPower receipt modes 0 =
      2 * ∑ wave ∈ modes,
        complexCoordinateRealInner (initialState wave)
          (wholeLatticeVorticityFourierTangentAt
            nu.coeff initialState wave) := by
  have stateAtZero :
      (actualWholeProjectedTransversePath receipt 0).1 = initialState := by
    change receipt.wholePath
        (Set.projIcc (0 : Real) requestedTime
          receipt.requestedTimePos.le 0) = initialState
    rw [Set.projIcc_of_mem receipt.requestedTimePos.le
      ⟨le_rfl, receipt.requestedTimePos.le⟩]
    exact receipt.wholePath_initial
  unfold actualProjectedWholeNetEnstrophyPower
    actualProjectedWholeEnstrophyPower
    actualProjectedWholeViscousEnstrophyPower
  rw [stateAtZero]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro wave waveMem
  rw [complexSharpSupportProjection_apply, if_pos waveMem]
  unfold wholeLatticeVorticityFourierTangentAt
  rw [complexCoordinateRealInner_sub_right]
  ring

/-- Exact time-zero decomposition into retained and newly installed Fourier
rows on one receipt. -/
theorem actualProjectedWholeNetEnstrophyPower_zero_eq_sdiff_add
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (smaller larger : Finset IntegerWavevector)
    (nested : smaller ⊆ larger) :
    actualProjectedWholeNetEnstrophyPower receipt larger 0 =
      actualProjectedWholeNetEnstrophyPower
          receipt (larger \ smaller) 0 +
        actualProjectedWholeNetEnstrophyPower receipt smaller 0 := by
  rw [actualProjectedWholeNetEnstrophyPower_zero_eq_wholeTangentWork,
    actualProjectedWholeNetEnstrophyPower_zero_eq_wholeTangentWork,
    actualProjectedWholeNetEnstrophyPower_zero_eq_wholeTangentWork]
  let row : IntegerWavevector → Real := fun wave =>
    complexCoordinateRealInner (initialState wave)
      (wholeLatticeVorticityFourierTangentAt
        nu.coeff initialState wave)
  have split := Finset.sum_sdiff (f := row) nested
  dsimp only [row] at split
  calc
    2 * ∑ wave ∈ larger,
          complexCoordinateRealInner (initialState wave)
            (wholeLatticeVorticityFourierTangentAt
              nu.coeff initialState wave) =
        2 * ((∑ wave ∈ larger \ smaller,
          complexCoordinateRealInner (initialState wave)
            (wholeLatticeVorticityFourierTangentAt
              nu.coeff initialState wave)) +
          ∑ wave ∈ smaller,
            complexCoordinateRealInner (initialState wave)
              (wholeLatticeVorticityFourierTangentAt
                nu.coeff initialState wave)) :=
      congrArg (fun value : Real => 2 * value) split.symm
    _ =
        2 * ∑ wave ∈ larger \ smaller,
          complexCoordinateRealInner (initialState wave)
            (wholeLatticeVorticityFourierTangentAt
              nu.coeff initialState wave) +
        2 * ∑ wave ∈ smaller,
          complexCoordinateRealInner (initialState wave)
            (wholeLatticeVorticityFourierTangentAt
              nu.coeff initialState wave) := by ring

/-- Shifted finite coefficient mass read only from the current physical
state and one candidate material inventory. -/
def currentFiniteEulerMassBase
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector) : Real :=
  finiteStateVorticityCoefficientEnstrophy modes
      current.contact.physicalState + 1

theorem currentFiniteEulerMassBase_pos
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector) :
    0 < currentFiniteEulerMassBase current modes := by
  unfold currentFiniteEulerMassBase
  have massNonneg : 0 ≤
      finiteStateVorticityCoefficientEnstrophy modes
        current.contact.physicalState := by
    unfold finiteStateVorticityCoefficientEnstrophy
    exact Finset.sum_nonneg fun wave _ =>
      complexCoordinateAmplitudeSq_nonneg _
  linarith

/-- Every actual current generates a finite canonical Fourier inventory
capturing its whole coefficient mass up to one absolute unit.  The radius is
chosen from convergence of the current's own canonical projections; it is
not a cutoff submitted by a caller and contains no future state. -/
theorem exists_currentMassCaptureRadius
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu) :
    ∃ radius : Nat,
      wholeVorticityEuclideanMass current.contact.physicalState <
        finiteStateVorticityCoefficientEnstrophy
            (wholeRestartModes radius) current.contact.physicalState + 1 := by
  have convergence := finiteRestartInventoryMass_tendsto_wholeMass
    current.contact.physicalState current.contact.physicalState_zero
  have eventuallyCaptured : ∀ᶠ radius : Nat in atTop,
      wholeVorticityEuclideanMass current.contact.physicalState - 1 <
        finiteStateVorticityCoefficientEnstrophy
          (wholeRestartModes radius) current.contact.physicalState := by
    apply convergence.eventually
    exact Ioi_mem_nhds (sub_lt_self _ (by norm_num))
  rcases (eventually_atTop.1 eventuallyCaptured) with
    ⟨radius, radiusSpec⟩
  refine ⟨radius, ?_⟩
  linarith [radiusSpec radius le_rfl]

noncomputable def currentMassCaptureRadius
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu) : Nat := by
  classical
  exact Nat.find (exists_currentMassCaptureRadius current)

def currentMassCaptureModes
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu) :
    Finset IntegerWavevector :=
  wholeRestartModes (currentMassCaptureRadius current)

theorem currentMassCaptureModes_spec
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu) :
    wholeVorticityEuclideanMass current.contact.physicalState <
      finiteStateVorticityCoefficientEnstrophy
          (currentMassCaptureModes current)
          current.contact.physicalState + 1 := by
  exact Nat.find_spec (exists_currentMassCaptureRadius current)

/-- Any explicit source cube capturing all but one unit of coefficient mass
bounds the canonical least mass-capture radius. -/
theorem currentMassCaptureRadius_le_of_spec
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (radius : Nat)
    (radiusSpec :
      wholeVorticityEuclideanMass current.contact.physicalState <
        finiteStateVorticityCoefficientEnstrophy
            (wholeRestartModes radius) current.contact.physicalState + 1) :
    currentMassCaptureRadius current ≤ radius := by
  classical
  exact Nat.find_min' (exists_currentMassCaptureRadius current) radiusSpec

/-- Every positive source tolerance generates one finite current-owned
inventory that simultaneously captures omitted coefficient mass and the
signed global time-zero work row.  The choice predicate therefore records
the evolution-sensitive power coordinate before the inventory is selected. -/
theorem exists_currentMassPowerCaptureAtTolerance
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (tolerance : Real)
    (tolerancePos : 0 < tolerance) :
    ∃ modes : Finset IntegerWavevector,
      (0 : IntegerWavevector) ∉ modes ∧
      wholeTailVorticityMass modes current.contact.physicalState < tolerance ∧
      |(∑' wave : IntegerWavevector,
          instantaneousWholeNetPowerRow
            nu current.contact.physicalState wave) -
        actualProjectedWholeNetEnstrophyPower
          current.nextReceipt modes 0| < tolerance := by
  rcases exists_current_jointMassPowerCapture_zeroFree
      current ∅ (by simp) tolerancePos tolerancePos with
    ⟨modes, _emptySubset, zeroNotMem, tailSmall, workClose⟩
  exact ⟨modes, zeroNotMem, tailSmall, workClose⟩

noncomputable def currentMassCaptureModesAtTolerance
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (tolerance : { value : Real // 0 < value }) :
    Finset IntegerWavevector :=
  Classical.choose
    (exists_currentMassPowerCaptureAtTolerance
      current tolerance.1 tolerance.2)

theorem currentMassCaptureModesAtTolerance_spec
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (tolerance : { value : Real // 0 < value }) :
    wholeTailVorticityMass
        (currentMassCaptureModesAtTolerance current tolerance)
        current.contact.physicalState < tolerance.1 :=
  (Classical.choose_spec
    (exists_currentMassPowerCaptureAtTolerance
      current tolerance.1 tolerance.2)).2.1

/-- The same chosen inventory approximates the complete signed
instantaneous work.  This is the commuting row absent from the old
mass-only selector. -/
theorem currentMassCaptureModesAtTolerance_power_spec
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (tolerance : { value : Real // 0 < value }) :
    |(∑' wave : IntegerWavevector,
        instantaneousWholeNetPowerRow
          nu current.contact.physicalState wave) -
      actualProjectedWholeNetEnstrophyPower current.nextReceipt
        (currentMassCaptureModesAtTolerance current tolerance) 0| <
      tolerance.1 :=
  (Classical.choose_spec
    (exists_currentMassPowerCaptureAtTolerance
      current tolerance.1 tolerance.2)).2.2

theorem currentMassCaptureModesAtTolerance_zeroNotMem
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (tolerance : { value : Real // 0 < value }) :
    (0 : IntegerWavevector) ∉
      currentMassCaptureModesAtTolerance current tolerance :=
  (Classical.choose_spec
    (exists_currentMassPowerCaptureAtTolerance
      current tolerance.1 tolerance.2)).1

/-! ## Quantitative full-replay finite retention -/

/-- The almost-everywhere coefficient ceiling of the generated whole replay
is a pointwise ceiling because the same receipt path is continuous. -/
theorem fullReplayWholeMass_le_coefficientCeiling
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (time : Set.Icc (0 : Real) (wholeRestartDuration current.contact)) :
    wholeVorticityEuclideanMass (current.nextReceipt.wholePath time) ≤
      wholeRestartCoefficientCeiling current.contact := by
  apply continuous_le_of_ae_le_commonTime
    (wholeRestartDuration_pos current.contact)
    (fun actual =>
      wholeVorticityEuclideanMass (current.nextReceipt.wholePath actual))
  · exact wholeReceiptVorticityMass_continuous current.nextReceipt
  · simpa only [GeneratedWholeRestartCurrent.nextReceipt] using
      generatedWholeRestartWholeContinuousMildSerrinReceipt_coefficientMass_ae_le
        (generatedWholeRestartCanonicalReplay current.contact)

/-- Quantization leaves strictly less than two units between the actual
whole coefficient mass and its restart ceiling. -/
theorem wholeRestartCoefficientCeiling_sub_physicalMass_lt_two
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu) :
    wholeRestartCoefficientCeiling current.contact -
        wholeVorticityEuclideanMass current.contact.physicalState < 2 := by
  have massNonneg :
      0 ≤ wholeVorticityEuclideanMass current.contact.physicalState :=
    by
      unfold wholeVorticityEuclideanMass
      exact tsum_nonneg fun wave => sq_nonneg _
  have rawNonneg :
      0 ≤ wholeRestartRawCoefficientCeiling current.contact := by
    rw [wholeRestartRawCoefficientCeiling_eq]
    simp only [wholeRestartPhysicalState_generatedPositiveWholeRestartContact]
    linarith
  have ceilingLt := Nat.ceil_lt_add_one rawNonneg
  rw [wholeRestartRawCoefficientCeiling_eq] at ceilingLt
  simp only [wholeRestartPhysicalState_generatedPositiveWholeRestartContact]
    at ceilingLt
  unfold wholeRestartCoefficientCeiling wholeRestartCoefficientLevel
  rw [wholeRestartRawCoefficientCeiling_eq]
  simp only [wholeRestartPhysicalState_generatedPositiveWholeRestartContact]
  linarith

/-- The exact finite-observation modulus accumulated on one current-owned
inventory.  It is computed from the fixed replay and the displayed finite
carrier; no time modulus is accepted from a caller. -/
def fullReplayFiniteObservedHolderBudget
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector) : Real :=
  ∑ wave ∈ modes,
    wholeRestartFiniteObservedHalfHolderEnergy
      (generatedWholeRestartCanonicalReplay current.contact) {wave}

theorem fullReplayFiniteObservedHolderBudget_nonneg
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector) :
    0 ≤ fullReplayFiniteObservedHolderBudget current modes := by
  unfold fullReplayFiniteObservedHolderBudget
  exact Finset.sum_nonneg fun wave _waveMem =>
    wholeRestartFiniteObservedHalfHolderEnergy_nonneg
      (generatedWholeRestartCanonicalReplay current.contact) {wave}

/-- Every current-owned finite inventory inherits the same explicit
half-Hölder displacement ledger as the historical crossing core.  This is
the full fixed replay, not the selected contact prefix. -/
theorem fullReplayFiniteDifferenceMass_le
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector)
    (zeroNotMem : (0 : IntegerWavevector) ∉ modes)
    (time : Set.Icc (0 : Real) (wholeRestartDuration current.contact)) :
    finiteStateVorticityCoefficientEnstrophy modes
        (current.nextReceipt.wholePath time -
          current.contact.physicalState) ≤
      3 * time.1 * fullReplayFiniteObservedHolderBudget current modes := by
  let replay := generatedWholeRestartCanonicalReplay current.contact
  let zeroTime : Set.Icc (0 : Real)
      (wholeRestartDuration current.contact) :=
    ⟨0, ⟨le_rfl, (wholeRestartDuration_pos current.contact).le⟩⟩
  have zeroPath :
      current.nextReceipt.wholePath zeroTime =
        current.contact.physicalState :=
    current.nextReceipt_initial
  have distanceEq : dist time zeroTime = time.1 := by
    rw [Subtype.dist_eq, Real.dist_eq]
    simp only [zeroTime, sub_zero, abs_of_nonneg time.2.1]
  unfold finiteStateVorticityCoefficientEnstrophy
    fullReplayFiniteObservedHolderBudget
  calc
    (∑ wave ∈ modes,
        complexCoordinateAmplitudeSq
          ((current.nextReceipt.wholePath time -
            current.contact.physicalState) wave)) ≤
        ∑ wave ∈ modes,
          3 * time.1 *
            wholeRestartFiniteObservedHalfHolderEnergy replay {wave} := by
      apply Finset.sum_le_sum
      intro wave waveMem
      have waveNe : wave ≠ 0 := fun waveZero =>
        zeroNotMem (waveZero ▸ waveMem)
      have zeroCoordinate :
          current.nextReceipt.wholePath zeroTime wave =
            current.contact.physicalState wave :=
        congrArg (fun state => state wave) zeroPath
      have holder :=
        generatedWholeRestartWholeContinuousMildSerrinReceipt_fixedWave_increment_sq_le
          replay wave waveNe time zeroTime
      change
        complexCoordinateAmplitudeSq
            (current.nextReceipt.wholePath time wave -
              current.contact.physicalState wave) ≤
          3 * time.1 *
            wholeRestartFiniteObservedHalfHolderEnergy replay {wave}
      rw [← zeroCoordinate]
      calc
        complexCoordinateAmplitudeSq
            (current.nextReceipt.wholePath time wave -
              current.nextReceipt.wholePath zeroTime wave) ≤
            3 *
              ‖current.nextReceipt.wholePath time wave -
                current.nextReceipt.wholePath zeroTime wave‖ ^ 2 :=
          complexCoordinateAmplitudeSq_le_three_mul_norm_sq _
        _ = 3 *
              dist
                (current.nextReceipt.wholePath time wave)
                (current.nextReceipt.wholePath zeroTime wave) ^ 2 := by
          rw [dist_eq_norm]
        _ ≤ 3 *
              (dist time zeroTime *
                wholeRestartFiniteObservedHalfHolderEnergy replay {wave}) :=
          mul_le_mul_of_nonneg_left holder (by norm_num)
        _ = 3 * time.1 *
              wholeRestartFiniteObservedHalfHolderEnergy replay {wave} := by
          rw [distanceEq]
          ring
    _ = 3 * time.1 *
        ∑ wave ∈ modes,
          wholeRestartFiniteObservedHalfHolderEnergy replay {wave} := by
      rw [Finset.mul_sum]

private theorem complexCoordinateAmplitudeSq_le_weighted_add_difference
    (left right : ComplexCoordinateVector)
    (weight : Real)
    (weightPos : 0 < weight) :
    complexCoordinateAmplitudeSq left ≤
      (1 + weight) * complexCoordinateAmplitudeSq right +
        (1 + 1 / weight) *
          complexCoordinateAmplitudeSq (right - left) := by
  unfold complexCoordinateAmplitudeSq
  calc
    (∑ coordinate : Coordinate, Complex.normSq (left coordinate)) ≤
        ∑ coordinate : Coordinate,
          ((1 + weight) * Complex.normSq (right coordinate) +
            (1 + 1 / weight) *
              Complex.normSq ((right - left) coordinate)) := by
      apply Finset.sum_le_sum
      intro coordinate _coordinateMem
      let x : Real := ‖right coordinate‖
      let y : Real := ‖(right - left) coordinate‖
      have leftNormLe : ‖left coordinate‖ ≤ x + y := by
        have identity : left coordinate =
            right coordinate - (right - left) coordinate := by
          simp
        rw [identity]
        exact norm_sub_le _ _
      have squareLe : ‖left coordinate‖ ^ 2 ≤ (x + y) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _)
          (add_nonneg (norm_nonneg _) (norm_nonneg _))).2 leftNormLe
      have weightedNonneg :
          0 ≤ weight * x ^ 2 + y ^ 2 / weight - 2 * x * y := by
        rw [show weight * x ^ 2 + y ^ 2 / weight - 2 * x * y =
            (weight * x - y) ^ 2 / weight by
          field_simp [weightPos.ne']
          ring]
        positivity
      simp only [Pi.sub_apply, Complex.normSq_eq_norm_sq]
      have targetGap :
          (1 + weight) * x ^ 2 + (1 + 1 / weight) * y ^ 2 -
              (x + y) ^ 2 =
            weight * x ^ 2 + y ^ 2 / weight - 2 * x * y := by
        ring
      calc
        ‖left coordinate‖ ^ 2 ≤ (x + y) ^ 2 := squareLe
        _ ≤ (1 + weight) * x ^ 2 +
              (1 + 1 / weight) * y ^ 2 := by
          rw [← sub_nonneg, targetGap]
          exact weightedNonneg
    _ =
        (1 + weight) *
            (∑ coordinate : Coordinate,
              Complex.normSq (right coordinate)) +
          (1 + 1 / weight) *
            (∑ coordinate : Coordinate,
              Complex.normSq ((right - left) coordinate)) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

/-- Weighted finite-carrier retention.  The free positive weight lets the
barrier calculation trade a small multiplicative loss of retained mass
against the exact replay displacement ledger. -/
theorem finiteStateVorticityCoefficientEnstrophy_le_weighted_target_add_difference
    (modes : Finset IntegerWavevector)
    (initial target : ComplexVorticityHilbertState)
    (weight : Real)
    (weightPos : 0 < weight) :
    finiteStateVorticityCoefficientEnstrophy modes initial ≤
      (1 + weight) *
          finiteStateVorticityCoefficientEnstrophy modes target +
        (1 + 1 / weight) *
          finiteStateVorticityCoefficientEnstrophy modes
            (target - initial) := by
  unfold finiteStateVorticityCoefficientEnstrophy
  calc
    (∑ wave ∈ modes, complexCoordinateAmplitudeSq (initial wave)) ≤
        ∑ wave ∈ modes,
          ((1 + weight) * complexCoordinateAmplitudeSq (target wave) +
            (1 + 1 / weight) *
              complexCoordinateAmplitudeSq ((target - initial) wave)) := by
      apply Finset.sum_le_sum
      intro wave _waveMem
      exact complexCoordinateAmplitudeSq_le_weighted_add_difference
        (initial wave) (target wave) weight weightPos
    _ =
        (1 + weight) *
            (∑ wave ∈ modes,
              complexCoordinateAmplitudeSq (target wave)) +
          (1 + 1 / weight) *
            (∑ wave ∈ modes,
              complexCoordinateAmplitudeSq ((target - initial) wave)) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

/-- Same-occurrence finite retention ledger on the actual fixed replay. -/
theorem fullReplayFiniteMass_retention_ledger
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector)
    (zeroNotMem : (0 : IntegerWavevector) ∉ modes)
    (time : Set.Icc (0 : Real) (wholeRestartDuration current.contact))
    (weight : Real)
    (weightPos : 0 < weight) :
    finiteStateVorticityCoefficientEnstrophy modes
        current.contact.physicalState ≤
      (1 + weight) *
          finiteStateVorticityCoefficientEnstrophy modes
            (current.nextReceipt.wholePath time) +
        (1 + 1 / weight) *
          (3 * time.1 *
            fullReplayFiniteObservedHolderBudget current modes) := by
  have weighted :=
    finiteStateVorticityCoefficientEnstrophy_le_weighted_target_add_difference
      modes current.contact.physicalState
      (current.nextReceipt.wholePath time) weight weightPos
  have differenceLe :=
    fullReplayFiniteDifferenceMass_le current modes zeroNotMem time
  have multiplierNonneg : 0 ≤ 1 + 1 / weight := by
    positivity
  exact weighted.trans
    (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left differenceLe multiplierNonneg))

/-- Exact finite/tail commuting consequence of the weighted retention row.
It isolates the only path-tail growth still available after the canonical
barrier ceiling and finite-observation displacement are both consumed. -/
theorem fullReplayTailMass_weighted_le
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector)
    (zeroNotMem : (0 : IntegerWavevector) ∉ modes)
    (time : Set.Icc (0 : Real) (wholeRestartDuration current.contact))
    (weight : Real)
    (weightPos : 0 < weight) :
    (1 + weight) * wholeTailVorticityMass modes
        (current.nextReceipt.wholePath time) ≤
      (1 + weight) * wholeRestartCoefficientCeiling current.contact -
        finiteStateVorticityCoefficientEnstrophy modes
          current.contact.physicalState +
        (1 + 1 / weight) *
          (3 * time.1 *
            fullReplayFiniteObservedHolderBudget current modes) := by
  have wholeLe := fullReplayWholeMass_le_coefficientCeiling current time
  have retained := fullReplayFiniteMass_retention_ledger
    current modes zeroNotMem time weight weightPos
  have scaleNonneg : 0 ≤ 1 + weight := by linarith
  have scaledWhole := mul_le_mul_of_nonneg_left wholeLe scaleNonneg
  rw [wholeTailVorticityMass_eq_whole_sub_finite]
  nlinarith

/-- Fully source-readable tail envelope.  The only non-finite loss is the
current occurrence's own captured tail; quantization contributes less than
two, and path drift is the exact finite-observation ledger above. -/
theorem fullReplayTailMass_weighted_lt_sourceEnvelope
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector)
    (zeroNotMem : (0 : IntegerWavevector) ∉ modes)
    (time : Set.Icc (0 : Real) (wholeRestartDuration current.contact))
    (weight : Real)
    (weightPos : 0 < weight) :
    (1 + weight) * wholeTailVorticityMass modes
        (current.nextReceipt.wholePath time) <
      2 + weight * wholeRestartCoefficientCeiling current.contact +
        wholeTailVorticityMass modes current.contact.physicalState +
        (1 + 1 / weight) *
          (3 * time.1 *
            fullReplayFiniteObservedHolderBudget current modes) := by
  have weighted := fullReplayTailMass_weighted_le
    current modes zeroNotMem time weight weightPos
  have quantized :=
    wholeRestartCoefficientCeiling_sub_physicalMass_lt_two current
  have massSplit :=
    wholeVorticityEuclideanMass_eq_finite_add_tail
      modes current.contact.physicalState
  nlinarith

/-- The ambient whole `ℓ²` norm is bounded by the exact Euclidean
coefficient mass.  This is the infinite-carrier counterpart of the existing
finite sharp-support estimate. -/
theorem wholeState_norm_sq_le_wholeVorticityEuclideanMass
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
    (fun wave => complexCoordinateVector_norm_sq_le_amplitudeSq (state wave))
    normSqSummable amplitudeSummable

theorem wholeVorticityEuclideanMass_projection_sub_eq_tail
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) :
    wholeVorticityEuclideanMass
        (complexSharpSupportProjection modes state - state) =
      wholeTailVorticityMass modes state := by
  have partition :=
    wholeVorticityEuclideanMass_eq_projection_add_complement modes state
  have tailPartition :=
    wholeVorticityEuclideanMass_eq_finite_add_tail modes state
  have projectionMass :
      wholeVorticityEuclideanMass
          (complexSharpSupportProjection modes state) =
        finiteStateVorticityCoefficientEnstrophy modes state := by
    rw [wholeVorticityEuclideanMass_eq_finite_of_supported
      modes (complexSharpSupportProjection modes state)
      (complexSharpSupportProjection_supported modes state)]
    exact finiteStateVorticityCoefficientEnstrophy_sharpSupportProjection
      modes state
  rw [projectionMass] at partition
  linarith

private theorem norm_le_sqrt_wholeVorticityEuclideanMass
    (state : ComplexVorticityHilbertState) :
    ‖state‖ ≤ Real.sqrt (wholeVorticityEuclideanMass state) := by
  exact (Real.le_sqrt (norm_nonneg _)
    (by
      unfold wholeVorticityEuclideanMass
      exact tsum_nonneg fun wave => sq_nonneg _)).2
    (wholeState_norm_sq_le_wholeVorticityEuclideanMass state)

/-- Finite projection plus the two exact coefficient tails control the
whole-carrier distance required by fixed-output nonlinear Lipschitz
continuity. -/
theorem wholeState_sub_norm_le_finiteDifference_add_tails
    (modes : Finset IntegerWavevector)
    (left right : ComplexVorticityHilbertState) :
    ‖left - right‖ ≤
      Real.sqrt
          (finiteStateVorticityCoefficientEnstrophy modes (left - right)) +
        Real.sqrt (wholeTailVorticityMass modes left) +
        Real.sqrt (wholeTailVorticityMass modes right) := by
  let projectedDifference :=
    complexSharpSupportProjection modes (left - right)
  let leftComplement := complexSharpSupportProjection modes left - left
  let rightComplement := complexSharpSupportProjection modes right - right
  have projectedSquare :
      ‖projectedDifference‖ ^ 2 ≤
        finiteStateVorticityCoefficientEnstrophy modes (left - right) := by
    dsimp only [projectedDifference]
    have supported := complexSharpSupportProjection_supported
      modes (left - right)
    have finiteBound :=
      complexVorticityHilbertState_norm_sq_le_coefficientEnstrophy
        modes (complexSharpSupportProjection modes (left - right)) supported
    rw [finiteStateVorticityCoefficientEnstrophy_sharpSupportProjection]
      at finiteBound
    exact finiteBound
  have finiteNonneg :
      0 ≤ finiteStateVorticityCoefficientEnstrophy modes (left - right) := by
    unfold finiteStateVorticityCoefficientEnstrophy
    exact Finset.sum_nonneg fun wave _waveMem =>
      complexCoordinateAmplitudeSq_nonneg _
  have projectedNorm :
      ‖projectedDifference‖ ≤
        Real.sqrt
          (finiteStateVorticityCoefficientEnstrophy modes (left - right)) :=
    (Real.le_sqrt (norm_nonneg _) finiteNonneg).2 projectedSquare
  have leftComplementNorm :
      ‖leftComplement‖ ≤
        Real.sqrt (wholeTailVorticityMass modes left) := by
    have wholeBound := norm_le_sqrt_wholeVorticityEuclideanMass
      leftComplement
    simpa only [leftComplement,
      wholeVorticityEuclideanMass_projection_sub_eq_tail] using wholeBound
  have rightComplementNorm :
      ‖rightComplement‖ ≤
        Real.sqrt (wholeTailVorticityMass modes right) := by
    have wholeBound := norm_le_sqrt_wholeVorticityEuclideanMass
      rightComplement
    simpa only [rightComplement,
      wholeVorticityEuclideanMass_projection_sub_eq_tail] using wholeBound
  have decomposition :
      left - right =
        projectedDifference - leftComplement + rightComplement := by
    dsimp only [projectedDifference, leftComplement, rightComplement]
    rw [complexSharpSupportProjection_sub]
    abel
  calc
    ‖left - right‖ =
        ‖projectedDifference - leftComplement + rightComplement‖ :=
      congrArg norm decomposition
    ‖projectedDifference - leftComplement + rightComplement‖ ≤
        ‖projectedDifference - leftComplement‖ + ‖rightComplement‖ :=
      norm_add_le _ _
    _ ≤ (‖projectedDifference‖ + ‖leftComplement‖) +
          ‖rightComplement‖ :=
      add_le_add_left (norm_sub_le _ _) _
    _ ≤
        (Real.sqrt
            (finiteStateVorticityCoefficientEnstrophy modes (left - right)) +
          Real.sqrt (wholeTailVorticityMass modes left)) +
          Real.sqrt (wholeTailVorticityMass modes right) :=
      add_le_add
        (add_le_add projectedNorm leftComplementNorm)
        rightComplementNorm

/-- The actual fixed replay's whole-carrier displacement is now a projection
of three source-generated ledgers: finite Hölder drift, current tail, and
same-time tail. -/
theorem fullReplayPath_sub_current_norm_le
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector)
    (zeroNotMem : (0 : IntegerWavevector) ∉ modes)
    (time : Set.Icc (0 : Real) (wholeRestartDuration current.contact)) :
    ‖current.nextReceipt.wholePath time -
        current.contact.physicalState‖ ≤
      Real.sqrt
          (3 * time.1 *
            fullReplayFiniteObservedHolderBudget current modes) +
        Real.sqrt (wholeTailVorticityMass modes
          (current.nextReceipt.wholePath time)) +
        Real.sqrt (wholeTailVorticityMass modes
          current.contact.physicalState) := by
  have projected := wholeState_sub_norm_le_finiteDifference_add_tails
    modes (current.nextReceipt.wholePath time)
      current.contact.physicalState
  have differenceLe :=
    fullReplayFiniteDifferenceMass_le current modes zeroNotMem time
  have sqrtLe := Real.sqrt_le_sqrt differenceLe
  exact projected.trans
    (add_le_add
      (add_le_add sqrtLe le_rfl) le_rfl)

/-- Fixed-output nonlinear drift on the full replay, with every dependence
factored through current scale, finite-observation drift and the two exact
tails. -/
theorem fullReplayNonlinearRow_sub_norm_le
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector)
    (zeroNotMem : (0 : IntegerWavevector) ∉ modes)
    (time : Set.Icc (0 : Real) (wholeRestartDuration current.contact))
    (output : IntegerWavevector) :
    ‖wholeStateVorticityNonlinearCoefficientAt
          (current.nextReceipt.wholePath time) output -
        wholeStateVorticityNonlinearCoefficientAt
          current.contact.physicalState output‖ ≤
      12 * Real.sqrt (integerWaveNormSq output) *
        Real.sqrt (wholeRestartCoefficientCeiling current.contact) *
        (Real.sqrt
            (3 * time.1 *
              fullReplayFiniteObservedHolderBudget current modes) +
          Real.sqrt (wholeTailVorticityMass modes
            (current.nextReceipt.wholePath time)) +
          Real.sqrt (wholeTailVorticityMass modes
            current.contact.physicalState)) := by
  let path := current.nextReceipt.wholePath time
  let source := current.contact.physicalState
  let ceiling := wholeRestartCoefficientCeiling current.contact
  let drift :=
    Real.sqrt
        (3 * time.1 *
          fullReplayFiniteObservedHolderBudget current modes) +
      Real.sqrt (wholeTailVorticityMass modes path) +
      Real.sqrt (wholeTailVorticityMass modes source)
  have ceilingNonneg : 0 ≤ ceiling :=
    (wholeRestartCoefficientCeiling_pos current.contact).le
  have pathMassLe : wholeVorticityEuclideanMass path ≤ ceiling := by
    simpa only [path, ceiling] using
      fullReplayWholeMass_le_coefficientCeiling current time
  have sourceRawLe := wholeRestartRawCoefficientCeiling_le current.contact
  have sourceMassLe : wholeVorticityEuclideanMass source ≤ ceiling := by
    change wholeRestartRawCoefficientCeiling current.contact ≤ ceiling at sourceRawLe
    rw [wholeRestartRawCoefficientCeiling_eq] at sourceRawLe
    simp only [wholeRestartPhysicalState_generatedPositiveWholeRestartContact]
      at sourceRawLe
    dsimp only [source]
    linarith
  have pathNormSqLe : ‖path‖ ^ 2 ≤ ceiling :=
    (wholeState_norm_sq_le_wholeVorticityEuclideanMass path).trans pathMassLe
  have sourceNormSqLe : ‖source‖ ^ 2 ≤ ceiling :=
    (wholeState_norm_sq_le_wholeVorticityEuclideanMass source).trans
      sourceMassLe
  have pathNormLe : ‖path‖ ≤ Real.sqrt ceiling :=
    (Real.le_sqrt (norm_nonneg _) ceilingNonneg).2 pathNormSqLe
  have sourceNormLe : ‖source‖ ≤ Real.sqrt ceiling :=
    (Real.le_sqrt (norm_nonneg _) ceilingNonneg).2 sourceNormSqLe
  have normSumLe : ‖path‖ + ‖source‖ ≤ 2 * Real.sqrt ceiling := by
    linarith
  have driftLe : ‖path - source‖ ≤ drift := by
    simpa only [path, source, drift] using
      fullReplayPath_sub_current_norm_le current modes zeroNotMem time
  have driftNonneg : 0 ≤ drift := by
    dsimp only [drift]
    positivity
  have angularNonneg :
      0 ≤ 6 * Real.sqrt (integerWaveNormSq output) := by positivity
  have normSumNonneg : 0 ≤ ‖path‖ + ‖source‖ := by positivity
  have generated := wholeStateVorticityNonlinearCoefficientAt_sub_norm_le
    path source (wholePath_transverse current.nextReceipt time)
      current.contact.transverse output
  change ‖wholeStateVorticityNonlinearCoefficientAt path output -
      wholeStateVorticityNonlinearCoefficientAt source output‖ ≤ _
  calc
    ‖wholeStateVorticityNonlinearCoefficientAt path output -
        wholeStateVorticityNonlinearCoefficientAt source output‖ ≤
        6 * Real.sqrt (integerWaveNormSq output) *
          ‖path - source‖ * (‖path‖ + ‖source‖) := generated
    _ ≤ 6 * Real.sqrt (integerWaveNormSq output) *
          drift * (‖path‖ + ‖source‖) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left driftLe angularNonneg)
        normSumNonneg
    _ ≤ 6 * Real.sqrt (integerWaveNormSq output) *
          drift * (2 * Real.sqrt ceiling) :=
      mul_le_mul_of_nonneg_left normSumLe
        (mul_nonneg angularNonneg driftNonneg)
    _ = 12 * Real.sqrt (integerWaveNormSq output) *
          Real.sqrt ceiling * drift := by ring

/-! ## Quantitative projected net-power drift -/

def finiteOutputSqrtFrequencyMass
    (modes : Finset IntegerWavevector) : Real :=
  ∑ wave ∈ modes, Real.sqrt (integerWaveNormSq wave)

theorem finiteOutputSqrtFrequencyMass_nonneg
    (modes : Finset IntegerWavevector) :
    0 ≤ finiteOutputSqrtFrequencyMass modes := by
  unfold finiteOutputSqrtFrequencyMass
  exact Finset.sum_nonneg fun wave _waveMem => Real.sqrt_nonneg _

/-- Static state readout of the projected whole net-power row. -/
def finiteWholeNetEnstrophyPowerAt
    (nu : Viscosity)
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) : Real :=
  2 * ∑ wave ∈ modes,
      complexCoordinateRealInner (state wave)
        (wholeStateVorticityNonlinearCoefficientAt state wave) -
    2 * ∑ wave ∈ modes,
      complexCoordinateRealInner (state wave)
        ((nu.coeff * integerWaveViscousMultiplier wave) • state wave)

theorem actualProjectedWholeNetEnstrophyPower_eq_static
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (modes : Finset IntegerWavevector)
    (actual : Real) :
    actualProjectedWholeNetEnstrophyPower receipt modes actual =
      finiteWholeNetEnstrophyPowerAt nu modes
        (actualWholeProjectedTransversePath receipt actual).1 := by
  unfold actualProjectedWholeNetEnstrophyPower
    actualProjectedWholeEnstrophyPower
    actualProjectedWholeViscousEnstrophyPower
    finiteWholeNetEnstrophyPowerAt
  dsimp only
  congr 1
  · congr 1
    apply Finset.sum_congr rfl
    intro wave waveMem
    rw [complexSharpSupportProjection_apply, if_pos waveMem]
  · congr 1
    apply Finset.sum_congr rfl
    intro wave waveMem
    rw [complexSharpSupportProjection_apply, if_pos waveMem]

private theorem complexCoordinateRealInner_sub_left
    (left₁ left₂ right : ComplexCoordinateVector) :
    complexCoordinateRealInner (left₁ - left₂) right =
      complexCoordinateRealInner left₁ right -
        complexCoordinateRealInner left₂ right := by
  unfold complexCoordinateRealInner
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro coordinate _coordinateMem
  simp only [Pi.sub_apply, Complex.sub_re, Complex.sub_im]
  ring

private theorem complexCoordinateRealInner_pair_sub
    (leftState rightState leftAction rightAction :
      ComplexCoordinateVector) :
    complexCoordinateRealInner leftState leftAction -
        complexCoordinateRealInner rightState rightAction =
      complexCoordinateRealInner (leftState - rightState) leftAction +
        complexCoordinateRealInner rightState
          (leftAction - rightAction) := by
  rw [complexCoordinateRealInner_sub_left,
    complexCoordinateRealInner_sub_right]
  ring

theorem abs_complexCoordinateRealInner_pair_sub_le
    (leftState rightState leftAction rightAction :
      ComplexCoordinateVector) :
    |complexCoordinateRealInner leftState leftAction -
        complexCoordinateRealInner rightState rightAction| ≤
      3 * ‖leftState - rightState‖ * ‖leftAction‖ +
        3 * ‖rightState‖ * ‖leftAction - rightAction‖ := by
  rw [complexCoordinateRealInner_pair_sub]
  exact (abs_add_le _ _).trans
    (add_le_add
      (abs_complexCoordinateRealInner_le_three_mul_norm
        (leftState - rightState) leftAction)
      (abs_complexCoordinateRealInner_le_three_mul_norm
        rightState (leftAction - rightAction)))

private theorem abs_nonlinearPairing_sub_le_of_norms
    (left right : ComplexVorticityHilbertState)
    (leftTransverse : WholeStateTransverse left)
    (rightTransverse : WholeStateTransverse right)
    (output : IntegerWavevector)
    (radius difference : Real)
    (radiusNonneg : 0 ≤ radius)
    (differenceNonneg : 0 ≤ difference)
    (leftNormLe : ‖left‖ ≤ radius)
    (rightNormLe : ‖right‖ ≤ radius)
    (differenceNormLe : ‖left - right‖ ≤ difference) :
    |complexCoordinateRealInner (left output)
          (wholeStateVorticityNonlinearCoefficientAt left output) -
        complexCoordinateRealInner (right output)
          (wholeStateVorticityNonlinearCoefficientAt right output)| ≤
      54 * Real.sqrt (integerWaveNormSq output) *
        radius ^ 2 * difference := by
  let angular := Real.sqrt (integerWaveNormSq output)
  have angularNonneg : 0 ≤ angular := Real.sqrt_nonneg _
  have leftRowNormLe : ‖left output‖ ≤ radius :=
    (lp.norm_apply_le_norm (by norm_num) left output).trans leftNormLe
  have rightRowNormLe : ‖right output‖ ≤ radius :=
    (lp.norm_apply_le_norm (by norm_num) right output).trans rightNormLe
  have differenceRowNormLe : ‖left output - right output‖ ≤ difference := by
    have rowLe := lp.norm_apply_le_norm (by norm_num) (left - right) output
    change ‖(left - right) output‖ ≤ difference
    exact rowLe.trans differenceNormLe
  have leftActionNormLe :
      ‖wholeStateVorticityNonlinearCoefficientAt left output‖ ≤
        6 * angular * radius ^ 2 := by
    have generated := wholeStateVorticityBilinearCoefficientAt_norm_le
      left left leftTransverse output
    rw [wholeStateVorticityBilinearCoefficientAt_self] at generated
    have squareLe : ‖left‖ ^ 2 ≤ radius ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) radiusNonneg).2 leftNormLe
    calc
      ‖wholeStateVorticityNonlinearCoefficientAt left output‖ ≤
          6 * angular * ‖left‖ ^ 2 := by
        simpa only [angular, pow_two, mul_assoc] using generated
      _ ≤ 6 * angular * radius ^ 2 :=
        mul_le_mul_of_nonneg_left squareLe
          (mul_nonneg (by norm_num) angularNonneg)
  have actionDifferenceNormLe :
      ‖wholeStateVorticityNonlinearCoefficientAt left output -
          wholeStateVorticityNonlinearCoefficientAt right output‖ ≤
        12 * angular * radius * difference := by
    have generated := wholeStateVorticityNonlinearCoefficientAt_sub_norm_le
      left right leftTransverse rightTransverse output
    have normSumLe : ‖left‖ + ‖right‖ ≤ 2 * radius := by linarith
    calc
      ‖wholeStateVorticityNonlinearCoefficientAt left output -
          wholeStateVorticityNonlinearCoefficientAt right output‖ ≤
          6 * angular * ‖left - right‖ * (‖left‖ + ‖right‖) := generated
      _ ≤ 6 * angular * difference * (‖left‖ + ‖right‖) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left differenceNormLe
            (mul_nonneg (by norm_num) angularNonneg))
          (by positivity)
      _ ≤ 6 * angular * difference * (2 * radius) :=
        mul_le_mul_of_nonneg_left normSumLe
          (mul_nonneg
            (mul_nonneg (by norm_num) angularNonneg) differenceNonneg)
      _ = 12 * angular * radius * difference := by ring
  have pairing := abs_complexCoordinateRealInner_pair_sub_le
    (left output) (right output)
    (wholeStateVorticityNonlinearCoefficientAt left output)
    (wholeStateVorticityNonlinearCoefficientAt right output)
  calc
    |complexCoordinateRealInner (left output)
          (wholeStateVorticityNonlinearCoefficientAt left output) -
        complexCoordinateRealInner (right output)
          (wholeStateVorticityNonlinearCoefficientAt right output)| ≤
        3 * ‖left output - right output‖ *
            ‖wholeStateVorticityNonlinearCoefficientAt left output‖ +
          3 * ‖right output‖ *
            ‖wholeStateVorticityNonlinearCoefficientAt left output -
              wholeStateVorticityNonlinearCoefficientAt right output‖ :=
      pairing
    _ ≤ 3 * difference * (6 * angular * radius ^ 2) +
          3 * radius * (12 * angular * radius * difference) := by
      gcongr
    _ = 54 * angular * radius ^ 2 * difference := by ring

private theorem abs_viscousPairing_sub_le_of_norms
    (nu : Viscosity)
    (left right : ComplexVorticityHilbertState)
    (output : IntegerWavevector)
    (radius difference : Real)
    (radiusNonneg : 0 ≤ radius)
    (differenceNonneg : 0 ≤ difference)
    (leftNormLe : ‖left‖ ≤ radius)
    (rightNormLe : ‖right‖ ≤ radius)
    (differenceNormLe : ‖left - right‖ ≤ difference) :
    |complexCoordinateRealInner (left output)
          ((nu.coeff * integerWaveViscousMultiplier output) • left output) -
        complexCoordinateRealInner (right output)
          ((nu.coeff * integerWaveViscousMultiplier output) • right output)| ≤
      6 * (nu.coeff * integerWaveViscousMultiplier output) *
        radius * difference := by
  let coefficient := nu.coeff * integerWaveViscousMultiplier output
  have coefficientNonneg : 0 ≤ coefficient := by
    dsimp only [coefficient]
    unfold integerWaveViscousMultiplier
    exact mul_nonneg nu.coeff_pos.le
      (mul_nonneg (sq_nonneg _) (integerWaveNormSq_nonneg output))
  have rightRowNormLe : ‖right output‖ ≤ radius :=
    (lp.norm_apply_le_norm (by norm_num) right output).trans rightNormLe
  have differenceRowNormLe : ‖left output - right output‖ ≤ difference := by
    have rowLe := lp.norm_apply_le_norm (by norm_num) (left - right) output
    change ‖(left - right) output‖ ≤ difference
    exact rowLe.trans differenceNormLe
  have leftActionNormLe : ‖coefficient • left output‖ ≤ coefficient * radius := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg coefficientNonneg]
    exact mul_le_mul_of_nonneg_left
      ((lp.norm_apply_le_norm (by norm_num) left output).trans leftNormLe)
      coefficientNonneg
  have actionDifferenceNormLe :
      ‖coefficient • left output - coefficient • right output‖ ≤
        coefficient * difference := by
    rw [← smul_sub, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg coefficientNonneg]
    exact mul_le_mul_of_nonneg_left differenceRowNormLe coefficientNonneg
  have pairing := abs_complexCoordinateRealInner_pair_sub_le
    (left output) (right output)
    (coefficient • left output) (coefficient • right output)
  change |_ - _| ≤ 6 * coefficient * radius * difference
  calc
    |_ - _| ≤
        3 * ‖left output - right output‖ * ‖coefficient • left output‖ +
          3 * ‖right output‖ *
            ‖coefficient • left output - coefficient • right output‖ :=
      pairing
    _ ≤ 3 * difference * (coefficient * radius) +
          3 * radius * (coefficient * difference) := by
      gcongr
    _ = 6 * coefficient * radius * difference := by ring

/-- Complete finite projected net-power is quantitatively Lipschitz on one
whole-state ball.  The constants are exact readouts of the displayed output
inventory; no path or future state appears in them. -/
theorem finiteWholeNetEnstrophyPowerAt_sub_abs_le
    (nu : Viscosity)
    (modes : Finset IntegerWavevector)
    (left right : ComplexVorticityHilbertState)
    (leftTransverse : WholeStateTransverse left)
    (rightTransverse : WholeStateTransverse right)
    (radius difference : Real)
    (radiusNonneg : 0 ≤ radius)
    (differenceNonneg : 0 ≤ difference)
    (leftNormLe : ‖left‖ ≤ radius)
    (rightNormLe : ‖right‖ ≤ radius)
    (differenceNormLe : ‖left - right‖ ≤ difference) :
    |finiteWholeNetEnstrophyPowerAt nu modes left -
        finiteWholeNetEnstrophyPowerAt nu modes right| ≤
      108 * finiteOutputSqrtFrequencyMass modes * radius ^ 2 * difference +
        12 * nu.coeff * finiteObservedMultiplierMass modes *
          radius * difference := by
  let nonlinearRow := fun state : ComplexVorticityHilbertState =>
    fun wave : IntegerWavevector =>
      complexCoordinateRealInner (state wave)
        (wholeStateVorticityNonlinearCoefficientAt state wave)
  let viscousRow := fun state : ComplexVorticityHilbertState =>
    fun wave : IntegerWavevector =>
      complexCoordinateRealInner (state wave)
        ((nu.coeff * integerWaveViscousMultiplier wave) • state wave)
  have nonlinearAbs :
      |(∑ wave ∈ modes, nonlinearRow left wave) -
          ∑ wave ∈ modes, nonlinearRow right wave| ≤
        54 * finiteOutputSqrtFrequencyMass modes *
          radius ^ 2 * difference := by
    calc
      |(∑ wave ∈ modes, nonlinearRow left wave) -
          ∑ wave ∈ modes, nonlinearRow right wave| =
          |∑ wave ∈ modes,
            (nonlinearRow left wave - nonlinearRow right wave)| := by
        rw [Finset.sum_sub_distrib]
      _ ≤ ∑ wave ∈ modes,
          |nonlinearRow left wave - nonlinearRow right wave| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ wave ∈ modes,
          54 * Real.sqrt (integerWaveNormSq wave) *
            radius ^ 2 * difference := by
        apply Finset.sum_le_sum
        intro wave _waveMem
        exact abs_nonlinearPairing_sub_le_of_norms
          left right leftTransverse rightTransverse wave
          radius difference radiusNonneg differenceNonneg
          leftNormLe rightNormLe differenceNormLe
      _ = 54 * finiteOutputSqrtFrequencyMass modes *
          radius ^ 2 * difference := by
        unfold finiteOutputSqrtFrequencyMass
        calc
          (∑ wave ∈ modes,
              54 * Real.sqrt (integerWaveNormSq wave) *
                radius ^ 2 * difference) =
              (54 * radius ^ 2 * difference) *
                ∑ wave ∈ modes,
                  Real.sqrt (integerWaveNormSq wave) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro wave _waveMem
            ring
          _ = _ := by ring
  have viscousAbs :
      |(∑ wave ∈ modes, viscousRow left wave) -
          ∑ wave ∈ modes, viscousRow right wave| ≤
        6 * nu.coeff * finiteObservedMultiplierMass modes *
          radius * difference := by
    calc
      |(∑ wave ∈ modes, viscousRow left wave) -
          ∑ wave ∈ modes, viscousRow right wave| =
          |∑ wave ∈ modes,
            (viscousRow left wave - viscousRow right wave)| := by
        rw [Finset.sum_sub_distrib]
      _ ≤ ∑ wave ∈ modes,
          |viscousRow left wave - viscousRow right wave| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ wave ∈ modes,
          6 * (nu.coeff * integerWaveViscousMultiplier wave) *
            radius * difference := by
        apply Finset.sum_le_sum
        intro wave _waveMem
        exact abs_viscousPairing_sub_le_of_norms
          nu left right wave radius difference radiusNonneg differenceNonneg
          leftNormLe rightNormLe differenceNormLe
      _ = 6 * nu.coeff * finiteObservedMultiplierMass modes *
          radius * difference := by
        unfold finiteObservedMultiplierMass
        calc
          (∑ wave ∈ modes,
              6 * (nu.coeff * integerWaveViscousMultiplier wave) *
                radius * difference) =
              (6 * nu.coeff * radius * difference) *
                ∑ wave ∈ modes, integerWaveViscousMultiplier wave := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro wave _waveMem
            ring
          _ = _ := by ring
  have netSplit :
      finiteWholeNetEnstrophyPowerAt nu modes left -
          finiteWholeNetEnstrophyPowerAt nu modes right =
        2 * ((∑ wave ∈ modes, nonlinearRow left wave) -
          ∑ wave ∈ modes, nonlinearRow right wave) -
        2 * ((∑ wave ∈ modes, viscousRow left wave) -
          ∑ wave ∈ modes, viscousRow right wave) := by
    unfold finiteWholeNetEnstrophyPowerAt
    dsimp only [nonlinearRow, viscousRow]
    ring
  rw [netSplit]
  calc
    |2 * ((∑ wave ∈ modes, nonlinearRow left wave) -
          ∑ wave ∈ modes, nonlinearRow right wave) -
        2 * ((∑ wave ∈ modes, viscousRow left wave) -
          ∑ wave ∈ modes, viscousRow right wave)| ≤
        |2 * ((∑ wave ∈ modes, nonlinearRow left wave) -
          ∑ wave ∈ modes, nonlinearRow right wave)| +
        |2 * ((∑ wave ∈ modes, viscousRow left wave) -
          ∑ wave ∈ modes, viscousRow right wave)| :=
      by
        rw [sub_eq_add_neg]
        simpa only [abs_neg] using
          (abs_add_le
            (2 * ((∑ wave ∈ modes, nonlinearRow left wave) -
              ∑ wave ∈ modes, nonlinearRow right wave))
            (-(2 * ((∑ wave ∈ modes, viscousRow left wave) -
              ∑ wave ∈ modes, viscousRow right wave))))
    _ = 2 * |(∑ wave ∈ modes, nonlinearRow left wave) -
          ∑ wave ∈ modes, nonlinearRow right wave| +
        2 * |(∑ wave ∈ modes, viscousRow left wave) -
          ∑ wave ∈ modes, viscousRow right wave| := by
      simp [abs_mul]
    _ ≤ 2 * (54 * finiteOutputSqrtFrequencyMass modes *
          radius ^ 2 * difference) +
        2 * (6 * nu.coeff * finiteObservedMultiplierMass modes *
          radius * difference) :=
      add_le_add
        (mul_le_mul_of_nonneg_left nonlinearAbs (by norm_num))
        (mul_le_mul_of_nonneg_left viscousAbs (by norm_num))
    _ = 108 * finiteOutputSqrtFrequencyMass modes *
          radius ^ 2 * difference +
        12 * nu.coeff * finiteObservedMultiplierMass modes *
          radius * difference := by ring

/-- Quantitative full-replay replacement for the former opaque continuity
patch.  The exact projected net-power at any actual time differs from its
time-zero instruction only by a source-computed finite/tail drift row. -/
theorem fullReplayNetPower_sub_zero_abs_le
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector)
    (zeroNotMem : (0 : IntegerWavevector) ∉ modes)
    (time : Set.Icc (0 : Real) (wholeRestartDuration current.contact)) :
    |actualProjectedWholeNetEnstrophyPower current.nextReceipt modes time.1 -
        actualProjectedWholeNetEnstrophyPower current.nextReceipt modes 0| ≤
      108 * finiteOutputSqrtFrequencyMass modes *
          wholeRestartCoefficientCeiling current.contact *
          (Real.sqrt
              (3 * time.1 *
                fullReplayFiniteObservedHolderBudget current modes) +
            Real.sqrt (wholeTailVorticityMass modes
              (current.nextReceipt.wholePath time)) +
            Real.sqrt (wholeTailVorticityMass modes
              current.contact.physicalState)) +
        12 * nu.coeff * finiteObservedMultiplierMass modes *
          Real.sqrt (wholeRestartCoefficientCeiling current.contact) *
          (Real.sqrt
              (3 * time.1 *
                fullReplayFiniteObservedHolderBudget current modes) +
            Real.sqrt (wholeTailVorticityMass modes
              (current.nextReceipt.wholePath time)) +
            Real.sqrt (wholeTailVorticityMass modes
              current.contact.physicalState)) := by
  let path := current.nextReceipt.wholePath time
  let source := current.contact.physicalState
  let ceiling := wholeRestartCoefficientCeiling current.contact
  let drift :=
    Real.sqrt
        (3 * time.1 *
          fullReplayFiniteObservedHolderBudget current modes) +
      Real.sqrt (wholeTailVorticityMass modes path) +
      Real.sqrt (wholeTailVorticityMass modes source)
  have ceilingNonneg : 0 ≤ ceiling :=
    (wholeRestartCoefficientCeiling_pos current.contact).le
  have pathMassLe : wholeVorticityEuclideanMass path ≤ ceiling := by
    simpa only [path, ceiling] using
      fullReplayWholeMass_le_coefficientCeiling current time
  have sourceRawLe := wholeRestartRawCoefficientCeiling_le current.contact
  have sourceMassLe : wholeVorticityEuclideanMass source ≤ ceiling := by
    change wholeRestartRawCoefficientCeiling current.contact ≤ ceiling at sourceRawLe
    rw [wholeRestartRawCoefficientCeiling_eq] at sourceRawLe
    simp only [wholeRestartPhysicalState_generatedPositiveWholeRestartContact]
      at sourceRawLe
    dsimp only [source]
    linarith
  have pathNormLe : ‖path‖ ≤ Real.sqrt ceiling := by
    apply (Real.le_sqrt (norm_nonneg _) ceilingNonneg).2
    exact (wholeState_norm_sq_le_wholeVorticityEuclideanMass path).trans
      pathMassLe
  have sourceNormLe : ‖source‖ ≤ Real.sqrt ceiling := by
    apply (Real.le_sqrt (norm_nonneg _) ceilingNonneg).2
    exact (wholeState_norm_sq_le_wholeVorticityEuclideanMass source).trans
      sourceMassLe
  have differenceNormLe : ‖path - source‖ ≤ drift := by
    simpa only [path, source, drift] using
      fullReplayPath_sub_current_norm_le current modes zeroNotMem time
  have driftNonneg : 0 ≤ drift := by
    dsimp only [drift]
    positivity
  have stateAtTime :
      (actualWholeProjectedTransversePath current.nextReceipt time.1).1 = path := by
    change current.nextReceipt.wholePath
        (Set.projIcc (0 : Real) (wholeRestartDuration current.contact)
          current.nextReceipt.requestedTimePos.le time.1) = path
    rw [Set.projIcc_of_mem current.nextReceipt.requestedTimePos.le time.2]
  have stateAtZero :
      (actualWholeProjectedTransversePath current.nextReceipt 0).1 = source := by
    change current.nextReceipt.wholePath
        (Set.projIcc (0 : Real) (wholeRestartDuration current.contact)
          current.nextReceipt.requestedTimePos.le 0) = source
    rw [Set.projIcc_of_mem current.nextReceipt.requestedTimePos.le
      ⟨le_rfl, current.nextReceipt.requestedTimePos.le⟩]
    exact current.nextReceipt.wholePath_initial
  have generated := finiteWholeNetEnstrophyPowerAt_sub_abs_le
    nu modes path source
    (wholePath_transverse current.nextReceipt time)
    current.contact.transverse
    (Real.sqrt ceiling) drift
    (Real.sqrt_nonneg _) driftNonneg
    pathNormLe sourceNormLe differenceNormLe
  rw [actualProjectedWholeNetEnstrophyPower_eq_static,
    actualProjectedWholeNetEnstrophyPower_eq_static,
    stateAtTime, stateAtZero]
  calc
    |finiteWholeNetEnstrophyPowerAt nu modes path -
        finiteWholeNetEnstrophyPowerAt nu modes source| ≤
      108 * finiteOutputSqrtFrequencyMass modes *
          (Real.sqrt ceiling) ^ 2 * drift +
        12 * nu.coeff * finiteObservedMultiplierMass modes *
          Real.sqrt ceiling * drift := generated
    _ = 108 * finiteOutputSqrtFrequencyMass modes * ceiling * drift +
        12 * nu.coeff * finiteObservedMultiplierMass modes *
          Real.sqrt ceiling * drift := by
      rw [Real.sq_sqrt ceilingNonneg]

/-- Exact finite/tail lower projection of the complete fixed-replay action.
The initial omitted mass remains visible as a subtraction; terminal tail
mass is nonnegative and is the only discarded inequality readout. -/
theorem fullReplayAction_ge_finiteNetPowerIntegral_sub_initialTail
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector)
    (zeroNotMem : (0 : IntegerWavevector) ∉ modes) :
    (∫ actual in (0 : Real)..wholeRestartDuration current.contact,
        actualProjectedWholeNetEnstrophyPower
          current.nextReceipt modes actual) -
        wholeTailVorticityMass modes current.contact.physicalState ≤
      ∑' wave : IntegerWavevector,
        actualWholeRowNetWork current.nextReceipt wave := by
  rw [tsum_actualWholeRowNetWork_eq_netPowerIntegral_add_tail
    current.nextReceipt modes zeroNotMem]
  rw [actualWholeTailNetWork_eq_terminal_sub_initial]
  have terminalTailNonneg := wholeTailVorticityMass_nonneg modes
    (current.nextReceipt.wholePath
      ⟨wholeRestartDuration current.contact,
        ⟨(wholeRestartDuration_pos current.contact).le, le_rfl⟩⟩)
  linarith

/-- Source-tolerance form of the same exact split.  The finite inventory is
computed from the current occurrence and the positive tolerance itself. -/
theorem fullReplayAction_ge_finiteNetPowerIntegral_sub_tolerance
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (tolerance : { value : Real // 0 < value }) :
    (∫ actual in (0 : Real)..wholeRestartDuration current.contact,
        actualProjectedWholeNetEnstrophyPower current.nextReceipt
          (currentMassCaptureModesAtTolerance current tolerance) actual) -
        tolerance.1 ≤
      ∑' wave : IntegerWavevector,
        actualWholeRowNetWork current.nextReceipt wave := by
  have exactLower :=
    fullReplayAction_ge_finiteNetPowerIntegral_sub_initialTail
      current (currentMassCaptureModesAtTolerance current tolerance)
      (currentMassCaptureModesAtTolerance_zeroNotMem current tolerance)
  have tailLt := currentMassCaptureModesAtTolerance_spec current tolerance
  exact (sub_le_sub_left tailLt.le _).trans exactLower

theorem currentMassCaptureModes_zeroNotMem
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu) :
    (0 : IntegerWavevector) ∉ currentMassCaptureModes current := by
  exact zero_not_mem_wholeRestartModes _

/-- Prefix-union of source-generated mass-capture cores along the one actual
run.  It is produced recursively from the current projection and therefore
is not a completed future table. -/
noncomputable def sourceGeneratedRunMassCaptureInventory
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    Nat → Finset IntegerWavevector
  | 0 => currentMassCaptureModes (run initial 0)
  | stage + 1 =>
      sourceGeneratedRunMassCaptureInventory initial stage ∪
        currentMassCaptureModes (run initial (stage + 1))

theorem sourceGeneratedRunMassCaptureInventory_zeroNotMem
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    ∀ stage,
      (0 : IntegerWavevector) ∉
        sourceGeneratedRunMassCaptureInventory initial stage := by
  intro stage
  induction stage with
  | zero =>
      simpa [sourceGeneratedRunMassCaptureInventory] using
        currentMassCaptureModes_zeroNotMem (run initial 0)
  | succ stage inductionHypothesis =>
      rw [sourceGeneratedRunMassCaptureInventory]
      simp only [Finset.mem_union, not_or]
      exact ⟨inductionHypothesis,
        currentMassCaptureModes_zeroNotMem ((run initial stage).next)⟩

theorem sourceGeneratedRunMassCaptureInventory_nested
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (stage : Nat) :
    sourceGeneratedRunMassCaptureInventory initial stage ⊆
      sourceGeneratedRunMassCaptureInventory initial (stage + 1) := by
  rw [sourceGeneratedRunMassCaptureInventory]
  exact Finset.subset_union_left

theorem currentMassCaptureModes_subset_runMassCaptureInventory
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    ∀ stage,
      currentMassCaptureModes (run initial stage) ⊆
        sourceGeneratedRunMassCaptureInventory initial stage := by
  intro stage
  cases stage with
  | zero => exact Finset.Subset.rfl
  | succ stage =>
      rw [sourceGeneratedRunMassCaptureInventory]
      exact Finset.subset_union_right

/-- Once a candidate inventory contains the current's source-generated mass
capture core, one fixed factor `4` covers the quantized whole ceiling. -/
theorem wholeRestartCoefficientCeiling_add_one_le_four_mul_currentFiniteEulerMassBase
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector)
    (captureSubset : currentMassCaptureModes current ⊆ modes) :
    wholeRestartCoefficientCeiling current.contact + 1 ≤
      4 * currentFiniteEulerMassBase current modes := by
  have captureLe :
      finiteStateVorticityCoefficientEnstrophy
          (currentMassCaptureModes current) current.contact.physicalState ≤
        finiteStateVorticityCoefficientEnstrophy
          modes current.contact.physicalState := by
    unfold finiteStateVorticityCoefficientEnstrophy
    exact Finset.sum_le_sum_of_subset_of_nonneg captureSubset
      (fun wave _ _ => complexCoordinateAmplitudeSq_nonneg _)
  have wholeLtBase :
      wholeVorticityEuclideanMass current.contact.physicalState <
        currentFiniteEulerMassBase current modes := by
    unfold currentFiniteEulerMassBase
    linarith [currentMassCaptureModes_spec current]
  have wholeNonneg :
      0 ≤ wholeVorticityEuclideanMass current.contact.physicalState :=
    by
      unfold wholeVorticityEuclideanMass
      exact tsum_nonneg fun wave => sq_nonneg _
  have rawNonneg :
      0 ≤ wholeRestartRawCoefficientCeiling current.contact := by
    change
      0 ≤ wholeVorticityEuclideanMass
        current.contact.physicalState + 1
    linarith
  have ceilingLt := Nat.ceil_lt_add_one
    rawNonneg
  change
    (Nat.ceil
      (wholeVorticityEuclideanMass current.contact.physicalState + 1) : Real) <
      (wholeVorticityEuclideanMass current.contact.physicalState + 1) + 1
    at ceilingLt
  have quantizedLt :
      wholeRestartCoefficientCeiling current.contact <
        wholeVorticityEuclideanMass current.contact.physicalState + 2 := by
    unfold wholeRestartCoefficientCeiling wholeRestartCoefficientLevel
    change
      (Nat.ceil
        (wholeVorticityEuclideanMass current.contact.physicalState + 1) : Real) <
        wholeVorticityEuclideanMass current.contact.physicalState + 2
    linarith
  have baseOne : 1 ≤ currentFiniteEulerMassBase current modes := by
    unfold currentFiniteEulerMassBase
    have finiteNonneg : 0 ≤
        finiteStateVorticityCoefficientEnstrophy
          modes current.contact.physicalState := by
      unfold finiteStateVorticityCoefficientEnstrophy
      exact Finset.sum_nonneg fun wave _ =>
        complexCoordinateAmplitudeSq_nonneg _
    linarith
  linarith

/-- Complete summed Euler work at the current end of the exact replay edge. -/
def currentFiniteEulerGrossWork
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector) : Real :=
  2 * ∑ wave ∈ modes,
    complexCoordinateRealInner
      (current.contact.physicalState wave)
      (wholeLatticeVorticityFourierTangentAt nu.coeff
        current.contact.physicalState wave)

/-- Source-readable loss allowance for transporting the complete summed
Euler work through this current's actual prefix. -/
def nextContactFiniteEulerRemainderLoss
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector) : Real :=
  6 * ∑ wave ∈ modes,
    ‖current.contact.physicalState wave‖ *
      nextContactEulerRemainderSlope current wave

theorem complexCoordinateAmplitudeSq_sub_eq_realInner_add
    (source target : ComplexCoordinateVector) :
    complexCoordinateAmplitudeSq target -
        complexCoordinateAmplitudeSq source =
      2 * complexCoordinateRealInner source (target - source) +
        complexCoordinateAmplitudeSq (target - source) := by
  unfold complexCoordinateAmplitudeSq complexCoordinateRealInner
  rw [← Finset.sum_sub_distrib, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro coordinate _
  simp only [Pi.sub_apply, Complex.sub_re, Complex.sub_im,
    Complex.normSq_apply]
  ring

theorem nextContact_amplitudeSq_sub_current_le_from_below
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (wave : IntegerWavevector)
    (waveNe : wave ≠ 0) :
    current.nextContact.time.1 *
        nextContactEulerPaymentDensity current wave ≤
      complexCoordinateAmplitudeSq
          (current.nextContact.physicalState wave) -
        complexCoordinateAmplitudeSq
          (current.contact.physicalState wave) := by
  let source := current.contact.physicalState wave
  let tangent := wholeLatticeVorticityFourierTangentAt nu.coeff
    current.contact.physicalState wave
  let error := current.nextContact.physicalState wave -
    nextContactEulerRow current wave
  have errorNormLe : ‖error‖ ≤
      current.nextContact.time.1 *
        nextContactEulerRemainderSlope current wave :=
    nextContact_row_sub_euler_norm_le current wave waveNe
  have errorPairingAbs :=
    abs_complexCoordinateRealInner_le_three_mul_norm source error
  have errorPairingLower :
      -(3 * ‖source‖ * current.nextContact.time.1 *
          nextContactEulerRemainderSlope current wave) ≤
        complexCoordinateRealInner source error := by
    have scaled :
        |complexCoordinateRealInner source error| ≤
          3 * ‖source‖ * current.nextContact.time.1 *
            nextContactEulerRemainderSlope current wave := by
      calc
        |complexCoordinateRealInner source error| ≤
            3 * ‖source‖ * ‖error‖ := errorPairingAbs
        _ ≤ 3 * ‖source‖ *
            (current.nextContact.time.1 *
              nextContactEulerRemainderSlope current wave) :=
          mul_le_mul_of_nonneg_left errorNormLe (by positivity)
        _ = 3 * ‖source‖ * current.nextContact.time.1 *
            nextContactEulerRemainderSlope current wave := by ring
    linarith [neg_abs_le (complexCoordinateRealInner source error)]
  have targetSubSource :
      current.nextContact.physicalState wave - source =
        current.nextContact.time.1 • tangent + error := by
    dsimp only [source, tangent, error]
    unfold nextContactEulerRow
    module
  have innerSplit :
      complexCoordinateRealInner source
          (current.nextContact.physicalState wave - source) =
        current.nextContact.time.1 *
            complexCoordinateRealInner source tangent +
          complexCoordinateRealInner source error := by
    rw [targetSubSource, complexCoordinateRealInner_add_right,
      complexCoordinateRealInner_real_smul_right]
  have amplitudeDifference :=
    complexCoordinateAmplitudeSq_sub_eq_realInner_add source
      (current.nextContact.physicalState wave)
  have differenceNonneg :
      0 ≤ complexCoordinateAmplitudeSq
        (current.nextContact.physicalState wave - source) :=
    complexCoordinateAmplitudeSq_nonneg _
  rw [innerSplit] at amplitudeDifference
  unfold nextContactEulerPaymentDensity
  dsimp only [source, tangent] at errorPairingLower amplitudeDifference ⊢
  linarith

def nextContactFiniteEulerPaymentFloor
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector) : Real :=
  current.nextContact.time.1 *
    ∑ wave ∈ modes, nextContactEulerPaymentDensity current wave

theorem nextContactFiniteEulerPaymentFloor_nonpos
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector) :
    nextContactFiniteEulerPaymentFloor current modes ≤ 0 := by
  unfold nextContactFiniteEulerPaymentFloor
  exact mul_nonpos_of_nonneg_of_nonpos current.nextContact.time_pos.le
    (Finset.sum_nonpos fun wave _ =>
      nextContactEulerPaymentDensity_nonpos current wave)

/-- Exact commuting factorization of the current-only payment floor.  Its
two rows are the complete summed whole-lattice work and the generated
actual-prefix remainder loss. -/
theorem nextContactFiniteEulerPaymentFloor_eq_clock_mul_work_sub_loss
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector) :
    nextContactFiniteEulerPaymentFloor current modes =
      current.nextContact.time.1 *
        (currentFiniteEulerGrossWork current modes -
          nextContactFiniteEulerRemainderLoss current modes) := by
  unfold nextContactFiniteEulerPaymentFloor
    nextContactEulerPaymentDensity currentFiniteEulerGrossWork
    nextContactFiniteEulerRemainderLoss
  congr 1
  rw [Finset.sum_sub_distrib]
  have lossSum :
      (∑ wave ∈ modes,
        6 * ‖current.contact.physicalState wave‖ *
          nextContactEulerRemainderSlope current wave) =
        6 * ∑ wave ∈ modes,
          ‖current.contact.physicalState wave‖ *
            nextContactEulerRemainderSlope current wave := by
    simpa only [mul_assoc] using
      (Finset.mul_sum modes
        (fun wave => ‖current.contact.physicalState wave‖ *
          nextContactEulerRemainderSlope current wave) (6 : Real)).symm
  have workSum :
      (∑ wave ∈ modes,
        2 * complexCoordinateRealInner
          (current.contact.physicalState wave)
          (wholeLatticeVorticityFourierTangentAt nu.coeff
            current.contact.physicalState wave)) =
        2 * ∑ wave ∈ modes,
          complexCoordinateRealInner
            (current.contact.physicalState wave)
            (wholeLatticeVorticityFourierTangentAt nu.coeff
              current.contact.physicalState wave) := by
    exact
      (Finset.mul_sum modes
        (fun wave => complexCoordinateRealInner
          (current.contact.physicalState wave)
          (wholeLatticeVorticityFourierTangentAt nu.coeff
            current.contact.physicalState wave)) (2 : Real)).symm
  rw [lossSum, workSum]

/-- Viscosity/source-cone charge generated by the exact seventh-order clock
majorant and the cone's `5/4` complete-work coefficient. -/
def finiteFourierScalePhaseCharge
    (nu : Viscosity)
    (coverage workCoefficient : Real) : Real :=
  workCoefficient /
    (4 * sourceOwnedWholeStateBarrierSeventhCoefficientUpper nu *
      coverage ^ 7)

theorem finiteFourierScalePhaseCharge_pos
    (nu : Viscosity)
    {coverage workCoefficient : Real}
    (coveragePos : 0 < coverage)
    (workCoefficientPos : 0 < workCoefficient) :
    0 < finiteFourierScalePhaseCharge
      nu coverage workCoefficient := by
  unfold finiteFourierScalePhaseCharge
  exact div_pos workCoefficientPos
    (mul_pos
      (mul_pos (by norm_num)
        (sourceOwnedWholeStateBarrierSeventhCoefficientUpper_pos nu))
      (pow_pos coveragePos 7))

/-- No strictly positive scale-relative debit can factor through the coarse
global-radius Euler floor. -/
theorem no_positiveScaleRelativePayment_through_eulerFloor
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector)
    {charge : Real}
    (chargePos : 0 < charge) :
    ¬ charge /
        currentFiniteEulerMassBase current modes ^ (23 / 4 : Real) ≤
      nextContactFiniteEulerPaymentFloor current modes := by
  intro paid
  have denominatorPos :
      0 < currentFiniteEulerMassBase current modes ^ (23 / 4 : Real) :=
    Real.rpow_pos_of_pos (currentFiniteEulerMassBase_pos current modes) _
  have sourcePos : 0 < charge /
      currentFiniteEulerMassBase current modes ^ (23 / 4 : Real) :=
    div_pos chargePos denominatorPos
  linarith [nextContactFiniteEulerPaymentFloor_nonpos current modes]

/-! ## Nondegenerate actual-path phase cone -/

/-- Exact finite physical payment on the current's selected next prefix. -/
def nextContactFiniteActualPayment
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector) : Real :=
  ∫ actual in (0 : Real)..current.nextContact.time.1,
    actualProjectedWholeNetEnstrophyPower
      current.nextContact.prefixReceipt modes actual

/-- Instantaneous shifted finite mass on the same actual next prefix. -/
def nextContactActualFiniteMassBase
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector)
    (actual : Real) : Real :=
  finiteStateVorticityCoefficientEnstrophy modes
      (actualWholeProjectedTransversePath
        current.nextContact.prefixReceipt actual).1 + 1

@[simp] theorem nextContactActualFiniteMassBase_zero
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector) :
    nextContactActualFiniteMassBase current modes 0 =
      currentFiniteEulerMassBase current modes := by
  have stateAtZero :
      (actualWholeProjectedTransversePath
        current.nextContact.prefixReceipt 0).1 =
          current.contact.physicalState := by
    change current.nextContact.prefixReceipt.wholePath
        (Set.projIcc (0 : Real) current.nextContact.time.1
          current.nextContact.time_pos.le 0) =
      current.contact.physicalState
    rw [Set.projIcc_of_mem current.nextContact.time_pos.le
      ⟨le_rfl, current.nextContact.time_pos.le⟩]
    exact current.nextContact.prefixReceipt.wholePath_initial
  unfold nextContactActualFiniteMassBase currentFiniteEulerMassBase
  rw [stateAtZero]

@[simp] theorem nextContactActualFiniteMassBase_terminal
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector) :
    nextContactActualFiniteMassBase current modes
        current.nextContact.time.1 =
      finiteStateVorticityCoefficientEnstrophy modes
          current.nextContact.physicalState + 1 := by
  have stateAtTerminal :
      (actualWholeProjectedTransversePath
        current.nextContact.prefixReceipt
        current.nextContact.time.1).1 =
          current.nextContact.physicalState := by
    change current.nextContact.prefixReceipt.wholePath
        (Set.projIcc (0 : Real) current.nextContact.time.1
          current.nextContact.time_pos.le
          current.nextContact.time.1) =
      current.nextContact.physicalState
    rw [Set.projIcc_of_mem current.nextContact.time_pos.le
      ⟨current.nextContact.time_pos.le, le_rfl⟩]
    exact current.nextContact.prefixReceipt_terminal
  unfold nextContactActualFiniteMassBase
  rw [stateAtTerminal]

theorem nextContactActualFiniteMassBase_continuous
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector) :
    Continuous (nextContactActualFiniteMassBase current modes) := by
  have stateContinuous : Continuous fun actual : Real =>
      (actualWholeProjectedTransversePath
        current.nextContact.prefixReceipt actual).1 :=
    continuous_subtype_val.comp
      (actualWholeProjectedTransversePath_continuous
        current.nextContact.prefixReceipt)
  unfold nextContactActualFiniteMassBase
    finiteStateVorticityCoefficientEnstrophy
  apply Continuous.add
  · apply continuous_finsetSum
    intro wave _waveMem
    apply complexCoordinateAmplitudeSq_continuous.comp
    exact (lp.evalCLM Complex
      (fun _ : IntegerWavevector => ComplexCoordinateVector)
      2 wave).continuous.comp stateContinuous
  · fun_prop

theorem nextContactFiniteActualPayment_eq_mass_sub
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector)
    (zeroNotMem : (0 : IntegerWavevector) ∉ modes) :
    nextContactFiniteActualPayment current modes =
      finiteStateVorticityCoefficientEnstrophy modes
          current.nextContact.physicalState -
        finiteStateVorticityCoefficientEnstrophy modes
          current.contact.physicalState := by
  unfold nextContactFiniteActualPayment
  have ledger :=
    actualProjectedWholeNetEnstrophyPower_integral_eq_terminal_sub_initial
      current.nextContact.prefixReceipt modes zeroNotMem
  rw [current.nextContact.prefixReceipt_terminal] at ledger
  exact ledger

/-- Exact finite ledger stopped at any actual time of the selected prefix. -/
theorem intervalIntegral_nextContactNetPower_eq_actualMass_sub_current
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector)
    (zeroNotMem : (0 : IntegerWavevector) ∉ modes)
    (actual : Real)
    (actualMem : actual ∈ Set.Icc (0 : Real)
      current.nextContact.time.1) :
    (∫ time in (0 : Real)..actual,
        actualProjectedWholeNetEnstrophyPower
          current.nextContact.prefixReceipt modes time) =
      finiteStateVorticityCoefficientEnstrophy modes
          (actualWholeProjectedTransversePath
            current.nextContact.prefixReceipt actual).1 -
        finiteStateVorticityCoefficientEnstrophy modes
          current.contact.physicalState := by
  by_cases actualZero : actual = 0
  · subst actual
    rw [intervalIntegral.integral_same]
    have baseEq := nextContactActualFiniteMassBase_zero current modes
    unfold nextContactActualFiniteMassBase currentFiniteEulerMassBase at baseEq
    linarith
  · have actualPos : 0 < actual :=
      lt_of_le_of_ne actualMem.1 (Ne.symm actualZero)
    let restricted := restrictWholeContinuousMildSerrinReceipt
      actualPos actualMem.2 current.nextContact.prefixReceipt
    have stateEq : ∀ time ∈ Set.Icc (0 : Real) actual,
        (actualWholeProjectedTransversePath restricted time).1 =
          (actualWholeProjectedTransversePath
            current.nextContact.prefixReceipt time).1 := by
      intro time timeMem
      change restricted.wholePath
          (Set.projIcc (0 : Real) actual actualPos.le time) =
        current.nextContact.prefixReceipt.wholePath
          (Set.projIcc (0 : Real) current.nextContact.time.1
            current.nextContact.time_pos.le time)
      rw [Set.projIcc_of_mem actualPos.le timeMem]
      rw [Set.projIcc_of_mem current.nextContact.time_pos.le
        ⟨timeMem.1, timeMem.2.trans actualMem.2⟩]
      rfl
    have powerEq : ∀ time ∈ Set.Icc (0 : Real) actual,
        actualProjectedWholeNetEnstrophyPower restricted modes time =
          actualProjectedWholeNetEnstrophyPower
            current.nextContact.prefixReceipt modes time := by
      intro time timeMem
      unfold actualProjectedWholeNetEnstrophyPower
        actualProjectedWholeEnstrophyPower
        actualProjectedWholeViscousEnstrophyPower
      rw [stateEq time timeMem]
    have integralEq :
        (∫ time in (0 : Real)..actual,
            actualProjectedWholeNetEnstrophyPower restricted modes time) =
          ∫ time in (0 : Real)..actual,
            actualProjectedWholeNetEnstrophyPower
              current.nextContact.prefixReceipt modes time := by
      apply intervalIntegral.integral_congr
      intro time timeMem
      have timeMem' : time ∈ Set.Icc (0 : Real) actual := by
        rw [Set.uIcc_of_le actualPos.le] at timeMem
        exact timeMem
      exact powerEq time timeMem'
    have ledger :=
      actualProjectedWholeNetEnstrophyPower_integral_eq_terminal_sub_initial
        restricted modes zeroNotMem
    rw [integralEq] at ledger
    have terminalEq := stateEq actual ⟨actualPos.le, le_rfl⟩
    have restrictedTerminal :
        restricted.wholePath ⟨actual, ⟨actualPos.le, le_rfl⟩⟩ =
          (actualWholeProjectedTransversePath
            current.nextContact.prefixReceipt actual).1 := by
      calc
        restricted.wholePath ⟨actual, ⟨actualPos.le, le_rfl⟩⟩ =
            (actualWholeProjectedTransversePath restricted actual).1 := by
          change restricted.wholePath ⟨actual, _⟩ =
            restricted.wholePath
              (Set.projIcc (0 : Real) actual actualPos.le actual)
          rw [Set.projIcc_of_mem actualPos.le
            ⟨actualPos.le, le_rfl⟩]
        _ = _ := terminalEq
    rw [restrictedTerminal] at ledger
    exact ledger

/-- General actual-current Fourier cone.  Its phase law is evaluated on the
complete summed physical net-power row of the same selected prefix.  It
contains neither target coefficients nor a payment/summability conclusion. -/
structure FiniteFourierActualPhaseConeAt
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector)
    (coverage workCoefficient : Real) : Prop where
  zeroNotMem : (0 : IntegerWavevector) ∉ modes
  one_le_coverage : 1 ≤ coverage
  workCoefficient_pos : 0 < workCoefficient
  ceiling_covered :
    wholeRestartCoefficientCeiling current.contact + 1 ≤
      coverage * currentFiniteEulerMassBase current modes
  power_margin : ∀ actual ∈ Set.Icc (0 : Real)
      current.nextContact.time.1,
    workCoefficient *
        nextContactActualFiniteMassBase current modes actual ^
          (5 / 4 : Real) ≤
      actualProjectedWholeNetEnstrophyPower
        current.nextContact.prefixReceipt modes actual

/-- Positivity of the normalized complete-power row automatically makes the
same finite mass nondecreasing on every stopped prefix. -/
theorem FiniteFourierActualPhaseConeAt.base_nondecreasing
    {nu : Viscosity}
    {current : GeneratedWholeRestartCurrent nu}
    {modes : Finset IntegerWavevector}
    {coverage workCoefficient : Real}
    (cone : FiniteFourierActualPhaseConeAt
      current modes coverage workCoefficient)
    (actual : Real)
    (actualMem : actual ∈ Set.Icc (0 : Real)
      current.nextContact.time.1) :
    currentFiniteEulerMassBase current modes ≤
      nextContactActualFiniteMassBase current modes actual := by
  have pointwiseNonneg : ∀ time ∈ Set.Icc (0 : Real) actual,
      0 ≤ actualProjectedWholeNetEnstrophyPower
        current.nextContact.prefixReceipt modes time := by
    intro time timeMem
    have timeMemFull : time ∈ Set.Icc (0 : Real)
        current.nextContact.time.1 :=
      ⟨timeMem.1, timeMem.2.trans actualMem.2⟩
    have basePos : 0 < nextContactActualFiniteMassBase
        current modes time := by
      unfold nextContactActualFiniteMassBase
      have finiteNonneg : 0 ≤
          finiteStateVorticityCoefficientEnstrophy modes
            (actualWholeProjectedTransversePath
              current.nextContact.prefixReceipt time).1 := by
        unfold finiteStateVorticityCoefficientEnstrophy
        exact Finset.sum_nonneg fun wave _ =>
          complexCoordinateAmplitudeSq_nonneg _
      linarith
    exact (mul_pos cone.workCoefficient_pos
      (Real.rpow_pos_of_pos basePos _)).le.trans
        (cone.power_margin time timeMemFull)
  have integralLower := intervalIntegral.integral_mono_on
    (μ := volume) actualMem.1
    (continuous_const.intervalIntegrable 0 actual)
    ((actualProjectedWholeNetEnstrophyPower_continuous
      current.nextContact.prefixReceipt modes).intervalIntegrable 0 actual)
    pointwiseNonneg
  have integralNonneg : 0 ≤
      ∫ time in (0 : Real)..actual,
        actualProjectedWholeNetEnstrophyPower
          current.nextContact.prefixReceipt modes time := by
    simpa [intervalIntegral.integral_const] using integralLower
  have ledger :=
    intervalIntegral_nextContactNetPower_eq_actualMass_sub_current
      current modes cone.zeroNotMem actual actualMem
  unfold nextContactActualFiniteMassBase currentFiniteEulerMassBase
  linarith

/-- A strict complete-power margin at the current endpoint generates a
nonzero actual-path neighborhood on the same selected next receipt.  This
is a local source fact, not a replacement contact or scheduler. -/
theorem exists_nextContactActualPowerMarginPatch
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector)
    (threshold : Real)
    (zeroMargin : threshold <
      actualProjectedWholeNetEnstrophyPower
        current.nextContact.prefixReceipt modes 0) :
    ∃ patch : Real, 0 < patch ∧
      ∀ actual ∈ Set.Icc (0 : Real) current.nextContact.time.1,
        actual < patch →
          threshold < actualProjectedWholeNetEnstrophyPower
            current.nextContact.prefixReceipt modes actual := by
  let power : Real → Real := fun actual =>
    actualProjectedWholeNetEnstrophyPower
      current.nextContact.prefixReceipt modes actual
  have powerContinuous : Continuous power :=
    actualProjectedWholeNetEnstrophyPower_continuous
      current.nextContact.prefixReceipt modes
  have zeroMem : 0 ∈ {actual | threshold < power actual} := zeroMargin
  have neighborhoodOpen : IsOpen {actual | threshold < power actual} :=
    isOpen_lt continuous_const powerContinuous
  obtain ⟨patch, patchPos, ballSubset⟩ :=
    Metric.isOpen_iff.mp neighborhoodOpen 0 zeroMem
  refine ⟨patch, patchPos, ?_⟩
  intro actual actualMem actualLt
  apply ballSubset
  rw [Metric.mem_ball, Real.dist_eq, sub_zero,
    abs_of_nonneg actualMem.1]
  exact actualLt

/-- Scale-relative version of the same local source fact.  Both sides read
the actual prefix state, so the patch already has the recursive
instantaneous-mass normalization required at its endpoint. -/
theorem exists_nextContactActualNormalizedPowerMarginPatch
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector)
    (workCoefficient : Real)
    (zeroMargin :
      workCoefficient *
          currentFiniteEulerMassBase current modes ^ (5 / 4 : Real) <
        actualProjectedWholeNetEnstrophyPower
          current.nextContact.prefixReceipt modes 0) :
    ∃ patch : Real, 0 < patch ∧
      ∀ actual ∈ Set.Icc (0 : Real) current.nextContact.time.1,
        actual < patch →
          workCoefficient *
              nextContactActualFiniteMassBase current modes actual ^
                (5 / 4 : Real) <
            actualProjectedWholeNetEnstrophyPower
              current.nextContact.prefixReceipt modes actual := by
  let margin : Real → Real := fun actual =>
    workCoefficient *
      nextContactActualFiniteMassBase current modes actual ^
        (5 / 4 : Real)
  let power : Real → Real := fun actual =>
    actualProjectedWholeNetEnstrophyPower
      current.nextContact.prefixReceipt modes actual
  have exponentNonneg : 0 ≤ (5 / 4 : Real) := by norm_num
  have marginContinuous : Continuous margin := by
    dsimp only [margin]
    exact continuous_const.mul
      (Real.continuous_rpow_const exponentNonneg |>.comp
        (nextContactActualFiniteMassBase_continuous current modes))
  have powerContinuous : Continuous power :=
    actualProjectedWholeNetEnstrophyPower_continuous
      current.nextContact.prefixReceipt modes
  have zeroMem : 0 ∈ {actual | margin actual < power actual} := by
    dsimp only [margin, power]
    change
      workCoefficient *
          nextContactActualFiniteMassBase current modes 0 ^
            (5 / 4 : Real) <
        actualProjectedWholeNetEnstrophyPower
          current.nextContact.prefixReceipt modes 0
    rw [nextContactActualFiniteMassBase_zero]
    exact zeroMargin
  have neighborhoodOpen : IsOpen {actual | margin actual < power actual} :=
    isOpen_lt marginContinuous powerContinuous
  obtain ⟨patch, patchPos, ballSubset⟩ :=
    Metric.isOpen_iff.mp neighborhoodOpen 0 zeroMem
  refine ⟨patch, patchPos, ?_⟩
  intro actual actualMem actualLt
  apply ballSubset
  rw [Metric.mem_ball, Real.dist_eq, sub_zero,
    abs_of_nonneg actualMem.1]
  exact actualLt

/-- The nondegenerate actual-path cone generates the same `23/4`
scale-relative debit, now through the exact physical integral rather than a
global-radius Euler enclosure. -/
theorem FiniteFourierActualPhaseConeAt.local_scaleRelativePayment
    {nu : Viscosity}
    {current : GeneratedWholeRestartCurrent nu}
    {modes : Finset IntegerWavevector}
    {coverage workCoefficient : Real}
    (cone : FiniteFourierActualPhaseConeAt
      current modes coverage workCoefficient) :
    finiteFourierScalePhaseCharge nu coverage workCoefficient /
          currentFiniteEulerMassBase current modes ^ (23 / 4 : Real) ≤
      nextContactFiniteActualPayment current modes := by
  let base := currentFiniteEulerMassBase current modes
  let ceiling := wholeRestartCoefficientCeiling current.contact
  let upper := sourceOwnedWholeStateBarrierSeventhCoefficientUpper nu
  have basePos : 0 < base := currentFiniteEulerMassBase_pos current modes
  have coveragePos : 0 < coverage := lt_of_lt_of_le (by norm_num)
    cone.one_le_coverage
  have ceilingPos : 0 < ceiling := wholeRestartCoefficientCeiling_pos _
  have upperPos : 0 < upper :=
    sourceOwnedWholeStateBarrierSeventhCoefficientUpper_pos nu
  have seventhCovered : (ceiling + 1) ^ 7 ≤
      (coverage * base) ^ 7 := by
    exact pow_le_pow_left₀ (by positivity) cone.ceiling_covered 7
  have barrierUpper :
      sourceOwnedWholeStateBarrierSlope nu ceiling ≤
        upper * (coverage * base) ^ 7 := by
    have generatedUpper := sourceOwnedWholeStateBarrierSlope_le_seventhUpper
      nu ceiling ceilingPos.le
    exact generatedUpper.trans
      (mul_le_mul_of_nonneg_left seventhCovered upperPos.le)
  have durationLower :
      1 / (2 * upper * (coverage * base) ^ 7) ≤
        wholeRestartDuration current.contact := by
    have denominatorLe :
        2 * sourceOwnedWholeStateBarrierSlope nu ceiling ≤
          2 * upper * (coverage * base) ^ 7 := by
      nlinarith
    have denominatorPos :
        0 < 2 * sourceOwnedWholeStateBarrierSlope nu ceiling :=
      mul_pos (by norm_num)
        (sourceOwnedWholeStateBarrierSlope_pos nu ceiling)
    change
      1 / (2 * upper * (coverage * base) ^ 7) ≤
        1 / (2 * sourceOwnedWholeStateBarrierSlope nu ceiling)
    simpa only [one_div] using
      (one_div_le_one_div_of_le denominatorPos denominatorLe)
  have clockLower :
      1 / (4 * upper * (coverage * base) ^ 7) <
        current.nextContact.time.1 := by
    have late := current.nextContact.time_half_lt
    have halvedLower :
        (1 / (2 * upper * (coverage * base) ^ 7)) / 2 ≤
          wholeRestartDuration current.contact / 2 :=
      div_le_div_of_nonneg_right durationLower (by norm_num)
    have normalized :
        (1 / (2 * upper * (coverage * base) ^ 7)) / 2 =
          1 / (4 * upper * (coverage * base) ^ 7) := by ring
    rw [normalized] at halvedLower
    exact halvedLower.trans_lt late
  have workPos : 0 < workCoefficient * base ^ (5 / 4 : Real) :=
    mul_pos cone.workCoefficient_pos (Real.rpow_pos_of_pos basePos _)
  have fixedPowerMargin : ∀ actual ∈ Set.Icc (0 : Real)
      current.nextContact.time.1,
      workCoefficient * base ^ (5 / 4 : Real) ≤
        actualProjectedWholeNetEnstrophyPower
          current.nextContact.prefixReceipt modes actual := by
    intro actual actualMem
    have baseLe := cone.base_nondecreasing actual actualMem
    have exponentNonneg : 0 ≤ (5 / 4 : Real) := by norm_num
    have powerLe := Real.rpow_le_rpow basePos.le baseLe exponentNonneg
    exact (mul_le_mul_of_nonneg_left powerLe
      cone.workCoefficient_pos.le).trans
        (cone.power_margin actual actualMem)
  have integralLower := intervalIntegral.integral_mono_on
    (μ := volume)
    (current.nextContact.time_pos.le)
    (continuous_const.intervalIntegrable 0 current.nextContact.time.1)
    ((actualProjectedWholeNetEnstrophyPower_continuous
      current.nextContact.prefixReceipt modes).intervalIntegrable
        0 current.nextContact.time.1)
    fixedPowerMargin
  have paymentLower :
      workCoefficient * base ^ (5 / 4 : Real) *
          current.nextContact.time.1 ≤
        nextContactFiniteActualPayment current modes := by
    dsimp only [base]
    unfold nextContactFiniteActualPayment
    simpa [intervalIntegral.integral_const, smul_eq_mul,
      mul_comm, mul_assoc] using integralLower
  have strictModelPayment :
      (1 / (4 * upper * (coverage * base) ^ 7)) *
          (workCoefficient * base ^ (5 / 4 : Real)) <
        nextContactFiniteActualPayment current modes := by
    calc
      (1 / (4 * upper * (coverage * base) ^ 7)) *
          (workCoefficient * base ^ (5 / 4 : Real)) <
          current.nextContact.time.1 *
            (workCoefficient * base ^ (5 / 4 : Real)) :=
        mul_lt_mul_of_pos_right clockLower workPos
      _ = workCoefficient * base ^ (5 / 4 : Real) *
          current.nextContact.time.1 := by ring
      _ ≤ nextContactFiniteActualPayment current modes := paymentLower
  have algebra :
      finiteFourierScalePhaseCharge nu coverage workCoefficient /
          base ^ (23 / 4 : Real) =
        (1 / (4 * upper * (coverage * base) ^ 7)) *
          (workCoefficient * base ^ (5 / 4 : Real)) := by
    dsimp only [finiteFourierScalePhaseCharge, upper]
    rw [show (coverage * base) ^ 7 = coverage ^ 7 * base ^ 7 by ring]
    have baseNe : base ≠ 0 := basePos.ne'
    have coverageNe : coverage ≠ 0 := coveragePos.ne'
    have upperNe : upper ≠ 0 := upperPos.ne'
    rw [show base ^ (23 / 4 : Real) =
        base ^ (7 : Real) / base ^ (5 / 4 : Real) by
      rw [← Real.rpow_sub basePos]
      norm_num]
    field_simp [baseNe, coverageNe, upperNe,
      (Real.rpow_pos_of_pos basePos (5 / 4 : Real)).ne']
    all_goals norm_num
  dsimp only [base] at algebra ⊢
  rw [algebra]
  exact strictModelPayment.le

/-- Exact endpoint transport of the scale-relative phase margin.  The
instantaneous mass threshold at the selected endpoint becomes the time-zero
instruction of the physically generated next receipt on the same inventory. -/
theorem FiniteFourierActualPhaseConeAt.endpoint_power_margin
    {nu : Viscosity}
    {current : GeneratedWholeRestartCurrent nu}
    {modes : Finset IntegerWavevector}
    {coverage workCoefficient : Real}
    (cone : FiniteFourierActualPhaseConeAt
      current modes coverage workCoefficient) :
    workCoefficient *
          (finiteStateVorticityCoefficientEnstrophy modes
              current.nextContact.physicalState + 1) ^ (5 / 4 : Real) ≤
      actualProjectedWholeNetEnstrophyPower
        current.next.nextReceipt modes 0 := by
  have endpoint := cone.power_margin current.nextContact.time.1
    ⟨current.nextContact.time_pos.le, le_rfl⟩
  rw [nextContactActualFiniteMassBase_terminal] at endpoint
  rw [next_netPower_zero_eq_current_selectedEndpoint current modes]
  exact endpoint

/-- Exact inventory-expansion seam.  Retained rows transport automatically;
the source need only make the newly installed rows pay the increase of the
`5/4` normalized mass threshold. -/
theorem FiniteFourierActualPhaseConeAt.endpoint_expanded_power_margin
    {nu : Viscosity}
    {current : GeneratedWholeRestartCurrent nu}
    {smaller larger : Finset IntegerWavevector}
    {coverage workCoefficient : Real}
    (cone : FiniteFourierActualPhaseConeAt
      current smaller coverage workCoefficient)
    (nested : smaller ⊆ larger)
    (newRowsPay :
      workCoefficient *
            (finiteStateVorticityCoefficientEnstrophy larger
                current.nextContact.physicalState + 1) ^ (5 / 4 : Real) -
          workCoefficient *
            (finiteStateVorticityCoefficientEnstrophy smaller
                current.nextContact.physicalState + 1) ^ (5 / 4 : Real) ≤
        actualProjectedWholeNetEnstrophyPower
          current.next.nextReceipt (larger \ smaller) 0) :
    workCoefficient *
          (finiteStateVorticityCoefficientEnstrophy larger
              current.nextContact.physicalState + 1) ^ (5 / 4 : Real) ≤
      actualProjectedWholeNetEnstrophyPower
        current.next.nextReceipt larger 0 := by
  have retained := cone.endpoint_power_margin
  have split :=
    actualProjectedWholeNetEnstrophyPower_zero_eq_sdiff_add
      current.next.nextReceipt smaller larger nested
  rw [split]
  linarith

theorem nextContactFiniteActualPayment_le_movingMassDifference
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (sourceModes targetModes : Finset IntegerWavevector)
    (zeroNotMem : (0 : IntegerWavevector) ∉ sourceModes)
    (nested : sourceModes ⊆ targetModes) :
    nextContactFiniteActualPayment current sourceModes ≤
      finiteStateVorticityCoefficientEnstrophy targetModes
          current.nextContact.physicalState -
        finiteStateVorticityCoefficientEnstrophy sourceModes
          current.contact.physicalState := by
  rw [nextContactFiniteActualPayment_eq_mass_sub
    current sourceModes zeroNotMem]
  have finiteLe :
      finiteStateVorticityCoefficientEnstrophy sourceModes
          current.nextContact.physicalState ≤
        finiteStateVorticityCoefficientEnstrophy targetModes
          current.nextContact.physicalState := by
    unfold finiteStateVorticityCoefficientEnstrophy
    exact Finset.sum_le_sum_of_subset_of_nonneg nested
      (fun wave _ _ => complexCoordinateAmplitudeSq_nonneg _)
  linarith

theorem runMovingInventoryEdgePayment_ge_actualPayment
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (modes : Nat → Finset IntegerWavevector)
    (zeroNotMem : ∀ stage, (0 : IntegerWavevector) ∉ modes stage)
    (nested : ∀ stage, modes stage ⊆ modes (stage + 1))
    (index : Nat) :
    nextContactFiniteActualPayment (run initial index)
        (modes (index + 1)) ≤
      runMovingInventoryEdgePayment initial modes (index + 1) := by
  have localBound := nextContactFiniteActualPayment_le_movingMassDifference
    (run initial index) (modes (index + 1)) (modes (index + 2))
    (zeroNotMem (index + 1)) (nested (index + 1))
  rw [runMovingInventoryEdgePayment_eq_nextFiniteMass_sub_current
    initial modes zeroNotMem (index + 1)]
  have sourceEq : (run initial (index + 1)).initialState =
      (run initial index).contact.physicalState :=
    run_succ_initialState initial index
  have targetEq : (run initial (index + 1 + 1)).initialState =
      (run initial index).nextContact.physicalState := by
    rw [run_succ_initialState, run_succ, next_contact]
    rfl
  rw [sourceEq, targetEq]
  simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using localBound

theorem nextContact_finiteMass_sub_current_le_from_below
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector)
    (zeroNotMem : (0 : IntegerWavevector) ∉ modes) :
    nextContactFiniteEulerPaymentFloor current modes ≤
      finiteStateVorticityCoefficientEnstrophy modes
          current.nextContact.physicalState -
        finiteStateVorticityCoefficientEnstrophy modes
          current.contact.physicalState := by
  have rowwise : ∀ wave ∈ modes,
      current.nextContact.time.1 *
          nextContactEulerPaymentDensity current wave ≤
        complexCoordinateAmplitudeSq
            (current.nextContact.physicalState wave) -
          complexCoordinateAmplitudeSq
            (current.contact.physicalState wave) := by
    intro wave waveMem
    exact nextContact_amplitudeSq_sub_current_le_from_below
      current wave (fun waveZero => zeroNotMem (waveZero ▸ waveMem))
  unfold nextContactFiniteEulerPaymentFloor
    finiteStateVorticityCoefficientEnstrophy
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_le_sum rowwise

theorem nextContact_movingFiniteMass_sub_current_le_from_below
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (sourceModes targetModes : Finset IntegerWavevector)
    (zeroNotMem : (0 : IntegerWavevector) ∉ sourceModes)
    (nested : sourceModes ⊆ targetModes) :
    nextContactFiniteEulerPaymentFloor current sourceModes ≤
      finiteStateVorticityCoefficientEnstrophy targetModes
          current.nextContact.physicalState -
        finiteStateVorticityCoefficientEnstrophy sourceModes
          current.contact.physicalState := by
  have sameModes := nextContact_finiteMass_sub_current_le_from_below
    current sourceModes zeroNotMem
  have finiteLe :
      finiteStateVorticityCoefficientEnstrophy sourceModes
          current.nextContact.physicalState ≤
        finiteStateVorticityCoefficientEnstrophy targetModes
          current.nextContact.physicalState := by
    unfold finiteStateVorticityCoefficientEnstrophy
    exact Finset.sum_le_sum_of_subset_of_nonneg nested
      (fun wave _ _ => complexCoordinateAmplitudeSq_nonneg _)
  linarith

end
end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartActualFourierConeAdvance
end NavierStokes
end SaturationMonoid
