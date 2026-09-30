import H0mework.NavierStokes.Accumulation.InstantaneousWholeNetPowerCapture
import H0mework.NavierStokes.Accumulation.ConcretePhaseRichPhysicalSeed
import H0mework.NavierStokes.EndpointTransport.CofinalNonlinearNegativeOneEuclideanBalance

/-!
# Whole instantaneous action commuting

This module closes the same-receipt commuting square from the complete
instantaneous physical enstrophy row, through its space-time H¹--H⁻¹
pairing, to the existing endpoint whole-action ledger.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

open scoped BigOperators ENNReal

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientWholeInstantaneousActionCommuting

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientInfiniteNonlinearNegativeSobolev
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinOverlap
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSourcePairOccurrence
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPositiveOutputWorkDualBudget
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEnstrophyWork
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelKineticTriadRedirect
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartWholeContinuousMildSerrin
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeTemporalEnstrophyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeUnforcedPositiveTimeRestart
open ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeUnforcedPositiveTimeRestart.GeneratedPositiveWholeRestartContact
open ThreeDimensionalVorticityCoefficientInstantaneousWholeNetPowerCapture
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCriticalDissipationLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open GeneratedInfiniteWholeRestartEndpointMacroLineage
open GeneratedInfiniteWholeRestartEndpointMacroLineage.FullFrameBoundaryVorticityCofinalNonlinearNegativeOneEuclideanBalance
open RationalVorticityEvaluator.PhaseRichTriple

noncomputable section

variable {nu : Viscosity}

/-- Full-lattice instantaneous action read directly from one receipt path. -/
def receiptWholeInstantaneousNetPower
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (time : Icc (0 : Real) requestedTime) : Real :=
  ∑' wave : IntegerWavevector,
    instantaneousWholeNetPowerRow nu (receipt.wholePath time) wave

/-- The already generated complete H¹--H⁻¹ cross density, normalized
back from the viscosity-weighted carrier to physical enstrophy power. -/
def receiptWholeCrossDensity
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (time : Icc (0 : Real) requestedTime) : Real :=
  let tangent := puncturedEuclideanSpaceTimeState receipt.wholeTangent
  let viscous := puncturedEuclideanSpaceTimeState
    (receiptViscousNegativeOneState receipt)
  (2 / nu.coeff) * (inner Complex (tangent time) (viscous time)).re

theorem receiptWholeCrossDensity_integrable
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime) :
    Integrable (receiptWholeCrossDensity receipt)
      (commonTimeMeasure requestedTime) := by
  let tangent := puncturedEuclideanSpaceTimeState receipt.wholeTangent
  let viscous := puncturedEuclideanSpaceTimeState
    (receiptViscousNegativeOneState receipt)
  have innerIntegrable :=
    MeasureTheory.L2.integrable_inner (𝕜 := Complex) tangent viscous
  have realIntegrable := Complex.reCLM.integrable_comp innerIntegrable
  change Integrable
    (fun time => (2 / nu.coeff) *
      (inner Complex (tangent time) (viscous time)).re)
    (commonTimeMeasure requestedTime)
  exact realIntegrable.const_mul (2 / nu.coeff)

private theorem complexCoordinateRealInner_comm
    (left right : ComplexCoordinateVector) :
    complexCoordinateRealInner left right =
      complexCoordinateRealInner right left := by
  unfold complexCoordinateRealInner
  apply Finset.sum_congr rfl
  intro coordinate _
  ring

private theorem instantaneousWholeNetPowerRow_zero
    (state : ComplexVorticityHilbertState)
    (zeroRow : state 0 = 0) :
    instantaneousWholeNetPowerRow nu state 0 = 0 := by
  simp [instantaneousWholeNetPowerRow, zeroRow,
    complexCoordinateRealInner]

theorem integral_receiptWholeCrossDensity_eq_boundary
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime) :
    (∫ time, receiptWholeCrossDensity receipt time
        ∂(commonTimeMeasure requestedTime)) =
      wholeVorticityEuclideanMass
          (receipt.wholePath
            ⟨requestedTime, ⟨receipt.requestedTimePos.le, le_rfl⟩⟩) -
        wholeVorticityEuclideanMass initialState := by
  let tangent := puncturedEuclideanSpaceTimeState receipt.wholeTangent
  let viscous := puncturedEuclideanSpaceTimeState
    (receiptViscousNegativeOneState receipt)
  have innerIntegrable :=
    MeasureTheory.L2.integrable_inner (𝕜 := Complex) tangent viscous
  have reIntegral :
      (∫ time, (inner Complex (tangent time) (viscous time)).re
          ∂(commonTimeMeasure requestedTime)) =
        (∫ time, inner Complex (tangent time) (viscous time)
          ∂(commonTimeMeasure requestedTime)).re := by
    exact integral_re (𝕜 := Complex) innerIntegrable
  have spaceTimeIntegral :
      (∫ time, (inner Complex (tangent time) (viscous time)).re
          ∂(commonTimeMeasure requestedTime)) =
        (inner Complex tangent viscous).re := by
    rw [reIntegral]
    rfl
  have boundary := receipt_puncturedEuclidean_cross_eq_boundary receipt
  change
    2 * (inner Complex tangent viscous).re =
      nu.coeff *
        (wholeVorticityEuclideanMass
            (receipt.wholePath
              ⟨requestedTime, ⟨receipt.requestedTimePos.le, le_rfl⟩⟩) -
          wholeVorticityEuclideanMass initialState) at boundary
  rw [show
    receiptWholeCrossDensity receipt =
      fun time =>
        (2 / nu.coeff) *
          (inner Complex (tangent time) (viscous time)).re by rfl]
  rw [integral_const_mul, spaceTimeIntegral]
  field_simp [nu.coeff_pos.ne'] at boundary ⊢
  linarith

private theorem receipt_crossRow_eq_instantaneous_ae
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (wave : NonzeroIntegerWavevector) :
    ∀ᵐ time ∂(commonTimeMeasure requestedTime),
      (2 / nu.coeff) *
          (inner Complex
            (puncturedEuclideanSpaceTimeState
              receipt.wholeTangent time wave)
            (puncturedEuclideanSpaceTimeState
              (receiptViscousNegativeOneState receipt) time wave)).re =
        instantaneousWholeNetPowerRow
          nu (receipt.wholePath time) wave.1 := by
  filter_upwards [
    puncturedEuclideanSpaceTimeState_apply_ae receipt.wholeTangent,
    puncturedEuclideanSpaceTimeState_apply_ae
      (receiptViscousNegativeOneState receipt),
    receipt.rowTangent_eq_wholeTangent_ae wave.1 wave.2,
    receiptViscousNegativeOneState_row_ae receipt wave.1,
    receipt.rowTangent_eq_unforced_ae wave.1 wave.2,
    receipt.wholePath_eq_transverse_ae] with
      time tangentMappedEq viscousMappedEq tangentRowEq viscousRowEq
        unforcedEq pathEq
  rw [tangentMappedEq, viscousMappedEq]
  change
    (2 / nu.coeff) *
        (inner Complex
          (euclideanCoordinateRow ((receipt.wholeTangent time) wave.1))
          (euclideanCoordinateRow
            ((receiptViscousNegativeOneState receipt time) wave.1))).re = _
  rw [euclideanCoordinateRow_re_inner, viscousRowEq]
  have tangentRowEqReal :
      Real.sqrt (integerWaveViscousMultiplier wave.1) •
          (receipt.wholeTangent time) wave.1 =
        receipt.rowTangent wave.1 wave.2 time := by
    ext coordinate
    have coordinateEq := congr_fun tangentRowEq coordinate
    simpa only [Pi.smul_apply, Complex.real_smul, smul_eq_mul]
      using coordinateEq
  have physicalEq :
      instantaneousWholeNetPowerRow
          nu (receipt.wholePath time) wave.1 =
        2 * complexCoordinateRealInner
          (receipt.wholePath time wave.1)
          (receipt.rowTangent wave.1 wave.2 time) := by
    unfold instantaneousWholeNetPowerRow
    rw [unforcedEq, ← pathEq,
      wholeStateVorticityBilinearCoefficientAt_self,
      complexCoordinateRealInner_sub_right]
    ring
  rw [physicalEq, ← tangentRowEqReal]
  rw [complexCoordinateRealInner_real_smul_right]
  rw [complexCoordinateRealInner_real_smul_right]
  rw [complexCoordinateRealInner_comm
    ((receipt.wholeTangent time) wave.1)
    (receipt.wholePath time wave.1)]
  field_simp [nu.coeff_pos.ne']

/-- The physical full-lattice instantaneous readout and the existing
space-time H¹--H⁻¹ density agree almost everywhere.  Pointwise gradient
summability is generated by the receipt and is not a theorem premise. -/
theorem receiptWholeInstantaneousNetPower_ae_eq_crossDensity
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime) :
    receiptWholeInstantaneousNetPower receipt =ᵐ[
      commonTimeMeasure requestedTime]
        receiptWholeCrossDensity receipt := by
  let tangent := puncturedEuclideanSpaceTimeState receipt.wholeTangent
  let viscous := puncturedEuclideanSpaceTimeState
    (receiptViscousNegativeOneState receipt)
  let crossRow :
      Icc (0 : Real) requestedTime → NonzeroIntegerWavevector → Real :=
    fun time wave =>
      (2 / nu.coeff) *
        (inner Complex (tangent time wave) (viscous time wave)).re
  have rowsAE : ∀ᵐ time ∂(commonTimeMeasure requestedTime),
      ∀ wave : NonzeroIntegerWavevector,
        crossRow time wave =
          instantaneousWholeNetPowerRow
            nu (receipt.wholePath time) wave.1 := by
    exact MeasureTheory.ae_all_iff.2 fun wave => by
      simpa only [crossRow, tangent, viscous] using
        receipt_crossRow_eq_instantaneous_ae receipt wave
  filter_upwards [rowsAE] with time rowEq
  let row : IntegerWavevector → Real :=
    instantaneousWholeNetPowerRow nu (receipt.wholePath time)
  have innerSummable :
      Summable fun wave : NonzeroIntegerWavevector =>
        inner Complex (tangent time wave) (viscous time wave) :=
    lp.summable_inner (𝕜 := Complex) (tangent time) (viscous time)
  have realHasSum :=
    innerSummable.hasSum.map Complex.reCLM Complex.reCLM.continuous
  have crossSummable : Summable (crossRow time) := by
    exact (realHasSum.mul_left (2 / nu.coeff)).summable
  have restrictedSummable :
      Summable fun wave : NonzeroIntegerWavevector => row wave.1 := by
    exact crossSummable.congr fun wave => rowEq wave
  have rowZero : row 0 = 0 := by
    exact instantaneousWholeNetPowerRow_zero
      (receipt.wholePath time) (receipt.wholePath_zero_row time)
  have indicatorEq :
      Set.indicator {wave : IntegerWavevector | wave ≠ 0} row = row := by
    funext wave
    by_cases waveZero : wave = 0
    · subst wave
      simp [rowZero]
    · simp [waveZero]
  have indicatorSummable :
      Summable (Set.indicator
        {wave : IntegerWavevector | wave ≠ 0} row) :=
    (summable_subtype_iff_indicator).mp restrictedSummable
  have fullSummable : Summable row := by
    rwa [indicatorEq] at indicatorSummable
  have restrictedTsum_eq_full :
      (∑' wave : NonzeroIntegerWavevector, row wave.1) =
        ∑' wave : IntegerWavevector, row wave := by
    calc
      (∑' wave : NonzeroIntegerWavevector, row wave.1) =
          ∑' wave : IntegerWavevector,
            Set.indicator {wave : IntegerWavevector | wave ≠ 0} row wave :=
        tsum_subtype {wave : IntegerWavevector | wave ≠ 0} row
      _ = ∑' wave : IntegerWavevector, row wave := by
        apply tsum_congr
        intro wave
        exact congrFun indicatorEq wave
  have crossTsum :
      (∑' wave : NonzeroIntegerWavevector, crossRow time wave) =
        (2 / nu.coeff) *
          (inner Complex (tangent time) (viscous time)).re := by
    rw [lp.inner_eq_tsum (𝕜 := Complex),
      Complex.re_tsum innerSummable, tsum_mul_left]
  change (∑' wave : IntegerWavevector, row wave) = _
  rw [← restrictedTsum_eq_full]
  rw [show
    (fun wave : NonzeroIntegerWavevector => row wave.1) =
      crossRow time by
      funext wave
      exact (rowEq wave).symm]
  rw [crossTsum]
  rfl

theorem receiptWholeInstantaneousNetPower_integrable
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime) :
    Integrable (receiptWholeInstantaneousNetPower receipt)
      (commonTimeMeasure requestedTime) :=
  (receiptWholeCrossDensity_integrable receipt).congr
    (receiptWholeInstantaneousNetPower_ae_eq_crossDensity receipt).symm

/-- Exact whole-receipt commuting square requested by the audit.  The
physical instantaneous whole sum, integrated row work, and terminal whole
coefficient-mass change are the same actual ledger entry. -/
theorem integral_receiptWholeInstantaneousNetPower_eq_tsum_netWork
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime) :
    (∫ time, receiptWholeInstantaneousNetPower receipt time
        ∂(commonTimeMeasure requestedTime)) =
      ∑' wave : IntegerWavevector,
        actualWholeRowNetWork receipt wave := by
  calc
    (∫ time, receiptWholeInstantaneousNetPower receipt time
        ∂(commonTimeMeasure requestedTime)) =
        ∫ time, receiptWholeCrossDensity receipt time
          ∂(commonTimeMeasure requestedTime) :=
      integral_congr_ae
        (receiptWholeInstantaneousNetPower_ae_eq_crossDensity receipt)
    _ = wholeVorticityEuclideanMass
          (receipt.wholePath
            ⟨requestedTime, ⟨receipt.requestedTimePos.le, le_rfl⟩⟩) -
        wholeVorticityEuclideanMass initialState :=
      integral_receiptWholeCrossDensity_eq_boundary receipt
    _ = ∑' wave : IntegerWavevector,
        actualWholeRowNetWork receipt wave :=
      (tsum_actualWholeRowNetWork_eq_terminal_sub_initial receipt).symm

theorem integral_receiptWholeInstantaneousNetPower_eq_boundary
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime) :
    (∫ time, receiptWholeInstantaneousNetPower receipt time
        ∂(commonTimeMeasure requestedTime)) =
      wholeVorticityEuclideanMass
          (receipt.wholePath
            ⟨requestedTime, ⟨receipt.requestedTimePos.le, le_rfl⟩⟩) -
        wholeVorticityEuclideanMass initialState := by
  rw [integral_receiptWholeInstantaneousNetPower_eq_tsum_netWork,
    tsum_actualWholeRowNetWork_eq_terminal_sub_initial]

/-- The arithmetic-fibre selector and the physical action ledger now commute
quantitatively on the emitted contact itself: both crossing and persistent
events retain more than half of every positive fixed-terminal debit. -/
theorem GeneratedWholeRestartKineticContact.emittedPrefix_wholeAction_gt_half_terminal
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    {receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime}
    {contact : GeneratedPositiveWholeRestartContact receipt}
    {replay : GeneratedWholeRestartCanonicalReplay contact}
    (generated : GeneratedWholeRestartKineticContact replay)
    (terminalPositive :
      0 < generatedWholeRestartTerminalNetEnstrophyDebit replay) :
    generatedWholeRestartTerminalNetEnstrophyDebit replay / 2 <
      ∫ time,
        receiptWholeInstantaneousNetPower
          generated.nextContact.prefixReceipt time
          ∂(commonTimeMeasure generated.nextContact.time.1) := by
  have retained :=
    generated.cellEffect_debit_gt_half_terminal_of_terminalDebit_pos
      terminalPositive
  rw [integral_receiptWholeInstantaneousNetPower_eq_tsum_netWork]
  rw [← _root_.SaturationMonoid.NavierStokes.ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeTemporalEnstrophyLedger.GeneratedWholeRestartCellDebitAt.netEnstrophyDebit_eq_tsum_action
    generated.cellEffect.debit]
  exact retained

/-- Exact average-action readout on the same emitted prefix. -/
theorem GeneratedWholeRestartKineticContact.emittedPrefix_averageWholePower_gt_terminal_over_two_horizon
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    {receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime}
    {contact : GeneratedPositiveWholeRestartContact receipt}
    {replay : GeneratedWholeRestartCanonicalReplay contact}
    (generated : GeneratedWholeRestartKineticContact replay)
    (terminalPositive :
      0 < generatedWholeRestartTerminalNetEnstrophyDebit replay) :
    generatedWholeRestartTerminalNetEnstrophyDebit replay /
          (2 * wholeRestartDuration contact) <
      (∫ time,
        receiptWholeInstantaneousNetPower
          generated.nextContact.prefixReceipt time
          ∂(commonTimeMeasure generated.nextContact.time.1)) /
        generated.nextContact.time.1 := by
  have retained :=
    _root_.SaturationMonoid.NavierStokes.ThreeDimensionalVorticityCoefficientWholeInstantaneousActionCommuting.GeneratedWholeRestartKineticContact.emittedPrefix_wholeAction_gt_half_terminal
      generated terminalPositive
  have horizonPositive := wholeRestartDuration_pos contact
  have timePositive := generated.nextContact.time_pos
  have timeLeHorizon := generated.nextContact.time.2.2
  rw [div_lt_div_iff₀ (mul_pos (by norm_num) horizonPositive) timePositive]
  have terminalTimesTimeLe :
      generatedWholeRestartTerminalNetEnstrophyDebit replay *
          generated.nextContact.time.1 ≤
        generatedWholeRestartTerminalNetEnstrophyDebit replay *
          wholeRestartDuration contact :=
    mul_le_mul_of_nonneg_left timeLeHorizon terminalPositive.le
  have terminalLtTwiceAction :
      generatedWholeRestartTerminalNetEnstrophyDebit replay <
        2 * (∫ time,
          receiptWholeInstantaneousNetPower
            generated.nextContact.prefixReceipt time
            ∂(commonTimeMeasure generated.nextContact.time.1)) := by
    linarith
  have scaledLt :=
    mul_lt_mul_of_pos_right terminalLtTwiceAction horizonPositive
  nlinarith

private theorem completeWork_commonTimeMeasure_univ_real
    (time : Real)
    (timeNonneg : 0 ≤ time) :
    (commonTimeMeasure time).real Set.univ = time := by
  let terminal : Set.Icc (0 : Real) time :=
    ⟨time, timeNonneg, le_rfl⟩
  have payment :=
    ThreeDimensionalVorticityCoefficientGeneratedIntegerShellWholeReceiptSquareContinuation.commonTimeMeasure_Iic_real
      time timeNonneg terminal
  have terminalIic : Set.Iic terminal = Set.univ := by
    ext current
    simp only [Set.mem_Iic, Set.mem_univ, iff_true]
    exact current.2.2
  simpa only [terminalIic, Measure.restrict_univ] using payment

theorem shortContact_completeInstantaneousAction_ge_floor_mul_time :
    netPowerFloor * shortContact.time.1 ≤
      ∫ time,
        receiptWholeInstantaneousNetPower shortContact.prefixReceipt time
          ∂(commonTimeMeasure shortContact.time.1) := by
  have finiteLower :
      netPowerFloor * shortContact.time.1 ≤
        ∫ actual in (0 : Real)..shortContact.time.1,
          actualProjectedWholeNetEnstrophyPower
            shortContact.prefixReceipt sourceIntegerModes actual := by
    have lower := intervalIntegral.integral_mono_on
      (μ := volume) shortContact.time_pos.le
      (continuous_const.intervalIntegrable 0 shortContact.time.1)
      ((actualProjectedWholeNetEnstrophyPower_continuous
        shortContact.prefixReceipt sourceIntegerModes).intervalIntegrable
          0 shortContact.time.1)
      (fun actual actualMem =>
        (shortContact_prefix_netPower_gt_floor actual actualMem).le)
    simpa [intervalIntegral.integral_const, smul_eq_mul,
      mul_comm] using lower
  have completeLower :=
    netPowerIntegral_le_tsum_actualWholeRowNetWork_of_initial_supported
      shortContact.prefixReceipt sourceIntegerModes
      sourceIntegerModes_zero_not_mem complexSourceState_supported
  rw [← integral_receiptWholeInstantaneousNetPower_eq_tsum_netWork]
    at completeLower
  exact finiteLower.trans completeLower

theorem shortContact_completeInstantaneousAction_pos :
    0 < ∫ time,
      receiptWholeInstantaneousNetPower shortContact.prefixReceipt time
        ∂(commonTimeMeasure shortContact.time.1) := by
  rw [integral_receiptWholeInstantaneousNetPower_eq_boundary,
    shortContact.prefixReceipt_terminal, complexSourceState_wholeMass_eq]
  linarith [shortContact_wholeMass_gt_source]

/-- The source-selected short receipt generates an actual positive-time,
gradient-good occurrence carrying strictly positive complete instantaneous
whole work.  Neither the time nor its pointwise H¹ certificate is supplied
by a caller. -/
theorem exists_shortContact_goodTime_completeInstantaneousWork_pos :
    ∃ time : Icc (0 : Real) shortContact.time.1,
      0 < time.1 ∧
      Summable (fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq
            (shortContact.prefixReceipt.wholePath time wave)) ∧
      FiniteStateFourierReality
        (shortContact.prefixReceipt.wholePath time) ∧
      Summable (instantaneousWholeNetPowerRow viscosity
        (shortContact.prefixReceipt.wholePath time)) ∧
      0 < receiptWholeInstantaneousNetPower
        shortContact.prefixReceipt time := by
  have gradientAE :
      ∀ᵐ time ∂(commonTimeMeasure shortContact.time.1),
        Summable (fun wave : IntegerWavevector =>
          integerWaveNormSq wave *
            complexCoordinateAmplitudeSq
              (shortContact.prefixReceipt.wholePath time wave)) := by
    filter_upwards [
      receiptPointwiseGradient_ae_summable shortContact.prefixReceipt,
      receiptStateLimit_eq_wholePath_ae shortContact.prefixReceipt] with
        time gradientSummable stateEq
    rwa [stateEq] at gradientSummable
  have timePosAE := commonTimeMeasure_ae_time_pos shortContact.time.1
  have realityAE :=
    wholePath_fourierReality_ae shortContact.prefixReceipt
  by_contra noWitness
  have nonposAE :
      receiptWholeInstantaneousNetPower shortContact.prefixReceipt ≤ᵐ[
        commonTimeMeasure shortContact.time.1] 0 := by
    filter_upwards [gradientAE, timePosAE, realityAE] with
        time gradientSummable timePos reality
    apply le_of_not_gt
    intro workPos
    have rowSummable :
        Summable (instantaneousWholeNetPowerRow viscosity
          (shortContact.prefixReceipt.wholePath time)) := by
      by_contra rowNotSummable
      have tsumZero := tsum_eq_zero_of_not_summable rowNotSummable
      change
        0 < ∑' wave : IntegerWavevector,
          instantaneousWholeNetPowerRow viscosity
            (shortContact.prefixReceipt.wholePath time) wave at workPos
      rw [tsumZero] at workPos
      exact (lt_irrefl 0 workPos)
    exact noWitness
      ⟨time, timePos, gradientSummable, reality, rowSummable, workPos⟩
  have integralNonpos := integral_nonpos_of_ae nonposAE
  linarith [shortContact_completeInstantaneousAction_pos]

/-- The same source fibre carries a quantitative complete-work margin: half
the exact finite source floor. -/
theorem exists_shortContact_goodTime_completeInstantaneousWork_gt_halfFloor :
    ∃ time : Icc (0 : Real) shortContact.time.1,
      0 < time.1 ∧
      Summable (fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq
            (shortContact.prefixReceipt.wholePath time wave)) ∧
      FiniteStateFourierReality
        (shortContact.prefixReceipt.wholePath time) ∧
      Summable (instantaneousWholeNetPowerRow viscosity
        (shortContact.prefixReceipt.wholePath time)) ∧
      netPowerFloor / 2 <
        receiptWholeInstantaneousNetPower
          shortContact.prefixReceipt time := by
  have gradientAE :
      ∀ᵐ time ∂(commonTimeMeasure shortContact.time.1),
        Summable (fun wave : IntegerWavevector =>
          integerWaveNormSq wave *
            complexCoordinateAmplitudeSq
              (shortContact.prefixReceipt.wholePath time wave)) := by
    filter_upwards [
      receiptPointwiseGradient_ae_summable shortContact.prefixReceipt,
      receiptStateLimit_eq_wholePath_ae shortContact.prefixReceipt] with
        time gradientSummable stateEq
    rwa [stateEq] at gradientSummable
  have timePosAE := commonTimeMeasure_ae_time_pos shortContact.time.1
  have realityAE := wholePath_fourierReality_ae shortContact.prefixReceipt
  by_contra noWitness
  have boundedAE :
      receiptWholeInstantaneousNetPower shortContact.prefixReceipt ≤ᵐ[
        commonTimeMeasure shortContact.time.1]
          fun _ => netPowerFloor / 2 := by
    filter_upwards [gradientAE, timePosAE, realityAE] with
        time gradientSummable timePos reality
    apply le_of_not_gt
    intro workLarge
    have rowSummable :
        Summable (instantaneousWholeNetPowerRow viscosity
          (shortContact.prefixReceipt.wholePath time)) := by
      by_contra rowNotSummable
      have tsumZero := tsum_eq_zero_of_not_summable rowNotSummable
      change netPowerFloor / 2 <
        ∑' wave : IntegerWavevector,
          instantaneousWholeNetPowerRow viscosity
            (shortContact.prefixReceipt.wholePath time) wave at workLarge
      rw [tsumZero] at workLarge
      linarith [netPowerFloor_pos]
    exact noWitness
      ⟨time, timePos, gradientSummable, reality, rowSummable, workLarge⟩
  have integralLe := integral_mono_ae
    (receiptWholeInstantaneousNetPower_integrable
      shortContact.prefixReceipt)
    (integrable_const (netPowerFloor / 2)) boundedAE
  rw [integral_const,
    completeWork_commonTimeMeasure_univ_real
      shortContact.time.1 shortContact.time_pos.le,
    smul_eq_mul] at integralLe
  have integralLower :=
    shortContact_completeInstantaneousAction_ge_floor_mul_time
  nlinarith [netPowerFloor_pos, shortContact.time_pos]

/-- Source-selected endpoint inside the complete-work-positive fibre. -/
noncomputable def completeWorkTime : Icc (0 : Real) shortContact.time.1 :=
  Classical.choose
    exists_shortContact_goodTime_completeInstantaneousWork_gt_halfFloor

theorem completeWorkTime_pos : 0 < completeWorkTime.1 :=
  (Classical.choose_spec
    exists_shortContact_goodTime_completeInstantaneousWork_gt_halfFloor).1

theorem completeWorkTime_gradient_summable :
    Summable (fun wave : IntegerWavevector =>
      integerWaveNormSq wave *
        complexCoordinateAmplitudeSq
          (shortContact.prefixReceipt.wholePath completeWorkTime wave)) :=
  (Classical.choose_spec
    exists_shortContact_goodTime_completeInstantaneousWork_gt_halfFloor).2.1

theorem completeWorkTime_reality :
    FiniteStateFourierReality
      (shortContact.prefixReceipt.wholePath completeWorkTime) :=
  (Classical.choose_spec
    exists_shortContact_goodTime_completeInstantaneousWork_gt_halfFloor).2.2.1

theorem completeWorkTime_row_summable :
    Summable (instantaneousWholeNetPowerRow viscosity
      (shortContact.prefixReceipt.wholePath completeWorkTime)) :=
  (Classical.choose_spec
    exists_shortContact_goodTime_completeInstantaneousWork_gt_halfFloor).2.2.2.1

theorem completeWorkTime_wholeWork_gt_halfFloor :
    netPowerFloor / 2 < receiptWholeInstantaneousNetPower
      shortContact.prefixReceipt completeWorkTime :=
  (Classical.choose_spec
    exists_shortContact_goodTime_completeInstantaneousWork_gt_halfFloor).2.2.2.2

theorem completeWorkTime_wholeWork_pos :
    0 < receiptWholeInstantaneousNetPower
      shortContact.prefixReceipt completeWorkTime :=
  (half_pos netPowerFloor_pos).trans
    completeWorkTime_wholeWork_gt_halfFloor

/-- The original physical seed restricted exactly to the selected complete
work endpoint. -/
noncomputable def completeWorkReceipt :
    WholeContinuousMildSerrinReceipt viscosity complexSourceState
      completeWorkTime.1 :=
  restrictWholeContinuousMildSerrinReceipt
    completeWorkTime_pos completeWorkTime.2.2
      shortContact.prefixReceipt

theorem completeWorkReceipt_terminal_state :
    completeWorkReceipt.wholePath
        ⟨completeWorkTime.1, ⟨completeWorkTime_pos.le, le_rfl⟩⟩ =
      shortContact.prefixReceipt.wholePath completeWorkTime := by
  change shortContact.prefixReceipt.wholePath
    (commonTimeInclusion completeWorkTime.2.2
      ⟨completeWorkTime.1, ⟨completeWorkTime_pos.le, le_rfl⟩⟩) = _
  congr 1

/-- Contact at the terminal endpoint of `completeWorkReceipt`.  All fields
are read from the choice predicate above; no second time is selected. -/
noncomputable def completeWorkContact :
    GeneratedPositiveWholeRestartContact completeWorkReceipt where
  time :=
    ⟨completeWorkTime.1, ⟨completeWorkTime_pos.le, le_rfl⟩⟩
  time_pos := completeWorkTime_pos
  time_half_lt := by linarith [completeWorkTime_pos]
  gradient_summable := by
    rw [completeWorkReceipt_terminal_state]
    exact completeWorkTime_gradient_summable
  transverse := wholePath_transverse completeWorkReceipt _
  reality := by
    rw [completeWorkReceipt_terminal_state]
    exact completeWorkTime_reality

/-- Concrete current whose selected endpoint itself carries positive
complete instantaneous whole work. -/
noncomputable def completeWorkSelectedInitial :
    GeneratedWholeRestartCurrent viscosity where
  initialState := complexSourceState
  duration := completeWorkTime.1
  receipt := completeWorkReceipt
  contact := completeWorkContact

theorem completeWorkSelectedInitial_wholeWork_pos :
    0 < ∑' wave : IntegerWavevector,
      instantaneousWholeNetPowerRow viscosity
        completeWorkSelectedInitial.contact.physicalState wave := by
  have stateEq :
      completeWorkSelectedInitial.contact.physicalState =
        shortContact.prefixReceipt.wholePath completeWorkTime := by
    change completeWorkReceipt.wholePath completeWorkContact.time = _
    exact completeWorkReceipt_terminal_state
  rw [stateEq]
  exact completeWorkTime_wholeWork_pos

theorem completeWorkSelectedInitial_wholeWork_gt_halfFloor :
    netPowerFloor / 2 < ∑' wave : IntegerWavevector,
      instantaneousWholeNetPowerRow viscosity
        completeWorkSelectedInitial.contact.physicalState wave := by
  have stateEq :
      completeWorkSelectedInitial.contact.physicalState =
        shortContact.prefixReceipt.wholePath completeWorkTime := by
    change completeWorkReceipt.wholePath completeWorkContact.time = _
    exact completeWorkReceipt_terminal_state
  rw [stateEq]
  exact completeWorkTime_wholeWork_gt_halfFloor

end


end ThreeDimensionalVorticityCoefficientWholeInstantaneousActionCommuting
end NavierStokes
end SaturationMonoid
