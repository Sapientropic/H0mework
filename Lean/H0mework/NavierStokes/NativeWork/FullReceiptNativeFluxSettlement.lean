import H0mework.NavierStokes.NativeWorkNative.FluxValueEscrow
import H0mework.NavierStokes.Accumulation.FiniteNormalizedWorkNativeJet
import H0mework.NavierStokes.EndpointTransport.CofinalNonlinearNegativeOneEuclideanBalance

/-!
# Full-receipt native-flux settlement

This scratch theorem keeps the canonical whole-restart duration unchanged.
It turns the pointwise Agmon native-flux escrow into one fixed-radius bound on
the complete generated next receipt.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

open scoped BigOperators ENNReal

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientFullReceiptNativeFluxSettlement

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientInfiniteNonlinearNegativeSobolev
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSourcePairOccurrence
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingFrequencySupportExhaustion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEnstrophyWork
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartWholeContinuousMildSerrin
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartActualFourierConeAdvance
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPositiveOutputWorkDualBudget
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeTemporalEnstrophyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationNativeTurbulenceLaw
open ThreeDimensionalVorticityCoefficientNativeFluxValueEscrow
open ThreeDimensionalVorticityCoefficientPuncturedCanonicalGalerkinTarget
open ThreeDimensionalVorticityCoefficientFiniteNormalizedWorkPhaseFace
open ThreeDimensionalVorticityCoefficientFiniteNormalizedWorkNativeJet
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime.GeneratedInfiniteWholeRestartEndpointMacroLineage.FullFrameBoundaryVorticityCofinalNonlinearNegativeOneEuclideanBalance

noncomputable section

/-- The physical vorticity-gradient mass of a whole mild receipt is an `L¹`
row on its exact common-time carrier. -/
theorem receipt_wholePath_gradientMass_integrable
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime) :
    Integrable
      (fun time =>
        wholeStateVorticityGradientMass (receipt.wholePath time))
      (commonTimeMeasure requestedTime) := by
  let viscousConstant := nu.coeff ^ 2 * (2 * Real.pi) ^ 2
  have viscousConstantPos : 0 < viscousConstant := by
    dsimp only [viscousConstant]
    exact mul_pos (sq_pos_of_pos nu.coeff_pos)
      (sq_pos_of_pos (mul_pos (by norm_num) Real.pi_pos))
  have mappedViscousSquareIntegrable :
      Integrable
        (fun time =>
          ‖puncturedEuclideanSpaceTimeState
            (receiptViscousNegativeOneState receipt) time‖ ^ 2)
        (commonTimeMeasure requestedTime) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (MeasureTheory.Lp.memLp
        (puncturedEuclideanSpaceTimeState
          (receiptViscousNegativeOneState receipt))).integrable_norm_rpow
        (by norm_num) (by norm_num)
  have weightedGradientIntegrable :
      Integrable
        (fun time => viscousConstant *
          wholeStateVorticityGradientMass (receipt.wholePath time))
        (commonTimeMeasure requestedTime) := by
    apply mappedViscousSquareIntegrable.congr
    filter_upwards [
      receiptViscousNegativeOneEuclideanMass_ae_eq_gradient receipt] with
        time pointEq
    simpa only [viscousConstant] using pointEq
  have scaled := weightedGradientIntegrable.const_mul viscousConstant⁻¹
  apply scaled.congr
  filter_upwards [] with time
  field_simp [viscousConstantPos.ne']

/-- Along one exact receipt, the fixed-mode native flux is continuous. -/
theorem receipt_nativeFlux_continuous
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (modes : Finset IntegerWavevector) :
    Continuous fun time : Icc (0 : Real) requestedTime =>
      nativeTurbulenceEnstrophyFlux modes (receipt.wholePath time) := by
  let power : Icc (0 : Real) requestedTime → Real := fun time =>
    actualProjectedWholeNetEnstrophyPower receipt modes time.1
  let resolved : Icc (0 : Real) requestedTime → Real := fun time =>
    finiteGeneratorRealWork modes nu.coeff
      (complexSharpSupportProjection modes (receipt.wholePath time))
  have powerContinuous : Continuous power :=
    (actualProjectedWholeNetEnstrophyPower_continuous receipt modes).comp
      continuous_subtype_val
  have projectedContinuous : Continuous fun time : Icc (0 : Real) requestedTime =>
      complexSharpSupportProjection modes (receipt.wholePath time) := by
    have composed := (sharpSupportProjectionCLM modes).continuous.comp
      receipt.wholePath.continuous
    apply composed.congr
    intro time
    exact sharpSupportProjectionCLM_apply modes (receipt.wholePath time)
  have resolvedContinuous : Continuous resolved :=
    (finiteGeneratorRealWork_contDiff modes nu.coeff).continuous.comp
      projectedContinuous
  have fluxEq :
      (fun time : Icc (0 : Real) requestedTime =>
        nativeTurbulenceEnstrophyFlux modes (receipt.wholePath time)) =
      fun time => power time / 2 - resolved time := by
    funext time
    have split :=
      actualProjectedWholeNetEnstrophyPower_eq_resolvedGenerator_add_nativeFlux
        receipt modes time.1
    dsimp only at split
    have stateEq :
        (actualWholeProjectedTransversePath receipt time.1).1 =
          receipt.wholePath time := by
      change receipt.wholePath
          (Set.projIcc (0 : Real) requestedTime
            receipt.requestedTimePos.le time.1) = receipt.wholePath time
      rw [Set.projIcc_of_mem receipt.requestedTimePos.le time.2]
    rw [stateEq] at split
    change
      power time = 2 *
        (finiteGeneratorRealWork modes nu.coeff
            (complexSharpSupportProjection modes (receipt.wholePath time)) +
          nativeTurbulenceEnstrophyFlux modes (receipt.wholePath time)) at split
    dsimp only [resolved]
    linarith
  rw [fluxEq]
  exact (powerContinuous.div_const 2).sub resolvedContinuous

/-- The complete generated next receipt obeys one fixed-radius pointwise
Agmon flux bound almost everywhere.  The coefficient is source-owned through
the current coefficient ceiling. -/
theorem current_nextReceipt_nativeFlux_ae_le
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (radius : Nat)
    (radiusPos : 0 < radius) :
    ∀ᵐ time ∂(commonTimeMeasure (wholeRestartDuration current.contact)),
      |nativeTurbulenceEnstrophyFlux (wholeRestartModes radius)
          (current.nextReceipt.wholePath time)| ≤
        (Real.sqrt
            (2184 * (2 * Real.pi) ^ 2 * biotSavartSerrinConstant *
              wholeRestartCoefficientCeiling current.contact) /
          Real.sqrt (radius : Real)) *
        wholeStateVorticityGradientMass
          (current.nextReceipt.wholePath time) := by
  let receipt := current.nextReceipt
  let ceiling := wholeRestartCoefficientCeiling current.contact
  let coefficient :=
    2184 * (2 * Real.pi) ^ 2 * biotSavartSerrinConstant * ceiling
  have radiusRealPos : 0 < (radius : Real) := by exact_mod_cast radiusPos
  have ceilingPos : 0 < ceiling :=
    wholeRestartCoefficientCeiling_pos current.contact
  have coefficientNonneg : 0 ≤ coefficient := by
    dsimp only [coefficient, ceiling]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) (sq_nonneg _))
        biotSavartSerrinConstant_nonneg)
      ceilingPos.le
  have massAE :
      ∀ᵐ time ∂(commonTimeMeasure (wholeRestartDuration current.contact)),
        wholeVorticityEuclideanMass (receipt.wholePath time) ≤ ceiling := by
    simpa only [receipt, GeneratedWholeRestartCurrent.nextReceipt] using
      generatedWholeRestartWholeContinuousMildSerrinReceipt_coefficientMass_ae_le
        (generatedWholeRestartCanonicalReplay current.contact)
  have gradientAE :
      ∀ᵐ time ∂(commonTimeMeasure (wholeRestartDuration current.contact)),
        Summable fun wave : IntegerWavevector =>
          integerWaveNormSq wave *
            complexCoordinateAmplitudeSq (receipt.wholePath time wave) := by
    filter_upwards [receiptPointwiseGradient_ae_summable receipt,
      receiptStateLimit_eq_wholePath_ae receipt] with
        time gradientSummable stateEq
    simpa only [stateEq] using gradientSummable
  filter_upwards [massAE, gradientAE] with time massLe gradientSummable
  let state := receipt.wholePath time
  let gradient := wholeStateVorticityGradientMass state
  have gradientNonneg : 0 ≤ gradient := by
    dsimp only [gradient]
    unfold wholeStateVorticityGradientMass
    exact tsum_nonneg fun wave =>
      mul_nonneg (integerWaveNormSq_nonneg wave)
        (complexCoordinateAmplitudeSq_nonneg _)
  have agmon := nativeTurbulenceEnstrophyFlux_sq_le_agmon
    radius radiusPos state (receipt.wholePath_zero_row time)
      (wholePath_transverse receipt time) gradientSummable
  have fluxSqLe :
      nativeTurbulenceEnstrophyFlux (wholeRestartModes radius) state ^ 2 ≤
        (coefficient * (radius : Real)⁻¹) * gradient ^ 2 := by
    calc
      nativeTurbulenceEnstrophyFlux (wholeRestartModes radius) state ^ 2 ≤
          (3 * (2 * Real.pi) ^ 2 * gradient) *
            (728 * biotSavartSerrinConstant * (radius : Real)⁻¹ *
              wholeVorticityEuclideanMass state * gradient) := agmon
      _ ≤ (3 * (2 * Real.pi) ^ 2 * gradient) *
            (728 * biotSavartSerrinConstant * (radius : Real)⁻¹ *
              ceiling * gradient) := by
        apply mul_le_mul_of_nonneg_left
        · apply mul_le_mul_of_nonneg_right
          · exact mul_le_mul_of_nonneg_left massLe
              (mul_nonneg
                (mul_nonneg (by norm_num) biotSavartSerrinConstant_nonneg)
                (inv_nonneg.mpr radiusRealPos.le))
          · exact gradientNonneg
        · exact mul_nonneg
            (mul_nonneg (by norm_num) (sq_nonneg _)) gradientNonneg
      _ = (coefficient * (radius : Real)⁻¹) * gradient ^ 2 := by
        dsimp only [coefficient]
        ring
  have coefficientRadiusNonneg :
      0 ≤ coefficient * (radius : Real)⁻¹ :=
    mul_nonneg coefficientNonneg (inv_nonneg.mpr radiusRealPos.le)
  have rhsNonneg :
      0 ≤ Real.sqrt (coefficient * (radius : Real)⁻¹) * gradient :=
    mul_nonneg (Real.sqrt_nonneg _) gradientNonneg
  have squareCompare :
      |nativeTurbulenceEnstrophyFlux (wholeRestartModes radius) state| ^ 2 ≤
        (Real.sqrt (coefficient * (radius : Real)⁻¹) * gradient) ^ 2 := by
    rw [sq_abs, mul_pow, Real.sq_sqrt coefficientRadiusNonneg]
    exact fluxSqLe
  have pointwise := (sq_le_sq₀ (abs_nonneg _) rhsNonneg).mp squareCompare
  have coefficientEq :
      Real.sqrt (coefficient * (radius : Real)⁻¹) =
        Real.sqrt coefficient / Real.sqrt (radius : Real) := by
    rw [Real.sqrt_mul coefficientNonneg, Real.sqrt_inv, div_eq_mul_inv]
  simpa only [receipt, state, gradient, ceiling, coefficient, coefficientEq]
    using pointwise

/-- Fixed-radius integrated native-flux escrow on the complete canonical
next receipt. -/
theorem current_nextReceipt_nativeFlux_integral_le
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (radius : Nat)
    (radiusPos : 0 < radius) :
    (∫ time,
      |nativeTurbulenceEnstrophyFlux (wholeRestartModes radius)
        (current.nextReceipt.wholePath time)|
      ∂(commonTimeMeasure (wholeRestartDuration current.contact))) ≤
      (Real.sqrt
          (2184 * (2 * Real.pi) ^ 2 * biotSavartSerrinConstant *
            wholeRestartCoefficientCeiling current.contact) /
        Real.sqrt (radius : Real)) *
      ∫ time,
        wholeStateVorticityGradientMass
          (current.nextReceipt.wholePath time)
        ∂(commonTimeMeasure (wholeRestartDuration current.contact)) := by
  let coefficient :=
    Real.sqrt
        (2184 * (2 * Real.pi) ^ 2 * biotSavartSerrinConstant *
          wholeRestartCoefficientCeiling current.contact) /
      Real.sqrt (radius : Real)
  have coefficientNonneg : 0 ≤ coefficient := by
    dsimp only [coefficient]
    exact div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have gradientIntegrable := receipt_wholePath_gradientMass_integrable
    current.nextReceipt
  have rightIntegrable : Integrable
      (fun time => coefficient *
        wholeStateVorticityGradientMass
          (current.nextReceipt.wholePath time))
      (commonTimeMeasure (wholeRestartDuration current.contact)) :=
    gradientIntegrable.const_mul coefficient
  have fluxContinuous := receipt_nativeFlux_continuous
    current.nextReceipt (wholeRestartModes radius)
  have fluxMeasurable : AEStronglyMeasurable
      (fun time =>
        |nativeTurbulenceEnstrophyFlux (wholeRestartModes radius)
          (current.nextReceipt.wholePath time)|)
      (commonTimeMeasure (wholeRestartDuration current.contact)) :=
    fluxContinuous.abs.aestronglyMeasurable
  have pointwise := current_nextReceipt_nativeFlux_ae_le
    current radius radiusPos
  have gradientNonneg : ∀ time,
      0 ≤ wholeStateVorticityGradientMass
        (current.nextReceipt.wholePath time) := by
    intro time
    unfold wholeStateVorticityGradientMass
    exact tsum_nonneg fun wave =>
      mul_nonneg (integerWaveNormSq_nonneg wave)
        (complexCoordinateAmplitudeSq_nonneg _)
  have fluxIntegrable : Integrable
      (fun time =>
        |nativeTurbulenceEnstrophyFlux (wholeRestartModes radius)
          (current.nextReceipt.wholePath time)|)
      (commonTimeMeasure (wholeRestartDuration current.contact)) := by
    apply rightIntegrable.mono' fluxMeasurable
    filter_upwards [pointwise] with time bound
    simpa only [Real.norm_eq_abs, abs_abs,
      abs_of_nonneg (mul_nonneg coefficientNonneg
        (gradientNonneg time))] using bound
  have integrated := integral_mono_ae fluxIntegrable rightIntegrable pointwise
  rw [integral_const_mul] at integrated
  simpa only [coefficient] using integrated

/-- Full-edge numerator computed entirely from the current's canonical
coefficient ceiling and the exact gradient ledger of its next receipt. -/
def currentNextReceiptNativeFluxIntegralNumerator
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu) : Real :=
  (2184 * (2 * Real.pi) ^ 2 * biotSavartSerrinConstant *
      wholeRestartCoefficientCeiling current.contact) *
    (∫ time,
      wholeStateVorticityGradientMass
        (current.nextReceipt.wholePath time)
      ∂(commonTimeMeasure (wholeRestartDuration current.contact))) ^ 2

theorem currentNextReceiptNativeFluxIntegralNumerator_nonneg
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu) :
    0 ≤ currentNextReceiptNativeFluxIntegralNumerator current := by
  unfold currentNextReceiptNativeFluxIntegralNumerator
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) (sq_nonneg _))
        biotSavartSerrinConstant_nonneg)
      (wholeRestartCoefficientCeiling_pos current.contact).le)
    (sq_nonneg _)

/-- Canonical fixed radius selected once from the same full receipt. -/
noncomputable def currentNextReceiptNativeFluxIntegralCaptureRadius
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (tolerance : {value : Real // 0 < value}) : Nat :=
  Nat.ceil
      (currentNextReceiptNativeFluxIntegralNumerator current /
        tolerance.1 ^ 2) + 1

theorem currentNextReceiptNativeFluxIntegralCaptureRadius_pos
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (tolerance : {value : Real // 0 < value}) :
    0 < currentNextReceiptNativeFluxIntegralCaptureRadius current tolerance := by
  unfold currentNextReceiptNativeFluxIntegralCaptureRadius
  omega

/-- Every larger fixed radius settles the absolute native coface value on
the same complete base horizon. -/
theorem current_nextReceipt_nativeFlux_integral_abs_lt_of_captureRadius_le
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (tolerance : {value : Real // 0 < value})
    (radius : Nat)
    (captureLe :
      currentNextReceiptNativeFluxIntegralCaptureRadius current tolerance ≤
        radius) :
    (∫ time,
      |nativeTurbulenceEnstrophyFlux (wholeRestartModes radius)
        (current.nextReceipt.wholePath time)|
      ∂(commonTimeMeasure (wholeRestartDuration current.contact))) <
      tolerance.1 := by
  let numerator := currentNextReceiptNativeFluxIntegralNumerator current
  let ratio := numerator / tolerance.1 ^ 2
  let captureRadius :=
    currentNextReceiptNativeFluxIntegralCaptureRadius current tolerance
  let gradientIntegral :=
    ∫ time,
      wholeStateVorticityGradientMass
        (current.nextReceipt.wholePath time)
      ∂(commonTimeMeasure (wholeRestartDuration current.contact))
  let coefficient :=
    2184 * (2 * Real.pi) ^ 2 * biotSavartSerrinConstant *
      wholeRestartCoefficientCeiling current.contact
  have numeratorNonneg : 0 ≤ numerator := by
    simpa only [numerator] using
      currentNextReceiptNativeFluxIntegralNumerator_nonneg current
  have toleranceSqPos : 0 < tolerance.1 ^ 2 :=
    sq_pos_of_pos tolerance.2
  have ratioNonneg : 0 ≤ ratio :=
    div_nonneg numeratorNonneg toleranceSqPos.le
  have ratioLeCeil : ratio ≤ (Nat.ceil ratio : Real) :=
    Nat.le_ceil ratio
  have ratioLtCapture : ratio < (captureRadius : Real) := by
    change ratio < ((Nat.ceil ratio + 1 : Nat) : Real)
    exact ratioLeCeil.trans_lt (by norm_num)
  have captureCastLe : (captureRadius : Real) ≤ (radius : Real) := by
    exact_mod_cast captureLe
  have ratioLtRadius : ratio < (radius : Real) :=
    ratioLtCapture.trans_le captureCastLe
  have radiusPosNat : 0 < radius := by
    exact (currentNextReceiptNativeFluxIntegralCaptureRadius_pos
      current tolerance).trans_le captureLe
  have radiusPos : 0 < (radius : Real) := by exact_mod_cast radiusPosNat
  have numeratorLt : numerator < tolerance.1 ^ 2 * (radius : Real) := by
    have scaled := mul_lt_mul_of_pos_left ratioLtRadius toleranceSqPos
    dsimp only [ratio] at scaled
    rw [mul_div_cancel₀ numerator toleranceSqPos.ne'] at scaled
    exact scaled
  have quotientLt : numerator / (radius : Real) < tolerance.1 ^ 2 := by
    exact (div_lt_iff₀ radiusPos).2 (by simpa [mul_comm] using numeratorLt)
  have coefficientNonneg : 0 ≤ coefficient := by
    dsimp only [coefficient]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) (sq_nonneg _))
        biotSavartSerrinConstant_nonneg)
      (wholeRestartCoefficientCeiling_pos current.contact).le
  have gradientIntegralNonneg : 0 ≤ gradientIntegral := by
    dsimp only [gradientIntegral]
    exact integral_nonneg fun time => by
      unfold wholeStateVorticityGradientMass
      exact tsum_nonneg fun wave =>
        mul_nonneg (integerWaveNormSq_nonneg wave)
          (complexCoordinateAmplitudeSq_nonneg _)
  let escrow :=
    Real.sqrt coefficient / Real.sqrt (radius : Real) * gradientIntegral
  have escrowNonneg : 0 ≤ escrow := by
    dsimp only [escrow]
    exact mul_nonneg
      (div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      gradientIntegralNonneg
  have escrowSq : escrow ^ 2 = numerator / (radius : Real) := by
    dsimp only [escrow, numerator,
      currentNextReceiptNativeFluxIntegralNumerator, coefficient,
      gradientIntegral]
    rw [mul_pow, div_pow, Real.sq_sqrt coefficientNonneg,
      Real.sq_sqrt radiusPos.le]
    ring
  have escrowLt : escrow < tolerance.1 := by
    apply (sq_lt_sq₀ escrowNonneg tolerance.2.le).mp
    rw [escrowSq]
    exact quotientLt
  have integralLe := current_nextReceipt_nativeFlux_integral_le
    current radius radiusPosNat
  change _ ≤ escrow at integralLe
  exact integralLe.trans_lt escrowLt

/-- The source-selected fixed radius settles the absolute native coface
value on the complete base horizon below any requested positive tolerance. -/
theorem current_nextReceipt_nativeFlux_integral_abs_lt_captureTolerance
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (tolerance : {value : Real // 0 < value}) :
    let radius :=
      currentNextReceiptNativeFluxIntegralCaptureRadius current tolerance
    (∫ time,
      |nativeTurbulenceEnstrophyFlux (wholeRestartModes radius)
        (current.nextReceipt.wholePath time)|
      ∂(commonTimeMeasure (wholeRestartDuration current.contact))) <
      tolerance.1 := by
  dsimp only
  exact current_nextReceipt_nativeFlux_integral_abs_lt_of_captureRadius_le
    current tolerance
      (currentNextReceiptNativeFluxIntegralCaptureRadius current tolerance)
      le_rfl

/-- Every fixed radius beyond the capture threshold settles the installed
native-flux work row on the same full receipt. -/
theorem current_nextReceipt_nativeFluxWork_abs_lt_of_captureRadius_le
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (tolerance : {value : Real // 0 < value})
    (radius : Nat)
    (captureLe :
      currentNextReceiptNativeFluxIntegralCaptureRadius current tolerance ≤
        radius) :
    |actualNativeTurbulenceEnstrophyFluxWork current.nextReceipt
        (wholeRestartModes radius)| < 2 * tolerance.1 := by
  let receipt := current.nextReceipt
  let flux : Set.Icc (0 : Real) (wholeRestartDuration current.contact) → Real :=
    fun time => nativeTurbulenceEnstrophyFlux (wholeRestartModes radius)
      (receipt.wholePath time)
  have workEq :
      actualNativeTurbulenceEnstrophyFluxWork receipt
          (wholeRestartModes radius) =
        2 * ∫ time, flux time
          ∂(commonTimeMeasure (wholeRestartDuration current.contact)) := by
    unfold actualNativeTurbulenceEnstrophyFluxWork
      actualNativeTurbulenceEnstrophyFluxPower
    rw [← commonTime_integral_eq_intervalIntegral
      (wholeRestartDuration current.contact)
      (wholeRestartDuration_pos current.contact).le]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with time
    dsimp only [flux, receipt]
    change
      2 * nativeTurbulenceEnstrophyFlux (wholeRestartModes radius)
          (current.nextReceipt.wholePath
            (Set.projIcc (0 : Real)
              (wholeRestartDuration current.contact)
              (wholeRestartDuration_pos current.contact).le time.1)) = _
    rw [Set.projIcc_of_mem
      (wholeRestartDuration_pos current.contact).le time.2]
  have integralAbsLt :=
    current_nextReceipt_nativeFlux_integral_abs_lt_of_captureRadius_le
      current tolerance radius captureLe
  change (∫ time, |flux time|
    ∂(commonTimeMeasure (wholeRestartDuration current.contact))) <
      tolerance.1 at integralAbsLt
  have absIntegralLe :
      |∫ time, flux time
          ∂(commonTimeMeasure (wholeRestartDuration current.contact))| ≤
        ∫ time, |flux time|
          ∂(commonTimeMeasure (wholeRestartDuration current.contact)) := by
    simpa only [Real.norm_eq_abs] using
      norm_integral_le_integral_norm
        (μ := commonTimeMeasure (wholeRestartDuration current.contact)) flux
  rw [workEq, abs_mul, abs_of_pos (by norm_num : (0 : Real) < 2)]
  nlinarith

/-- The full-receipt `L¹` escrow controls every prefix of the same native
work row.  This is the prefix form needed to retain finite mass without a
separate Hölder residence premise. -/
theorem current_nextReceipt_nativeFluxPrefixWork_abs_lt_of_captureRadius_le
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (tolerance : {value : Real // 0 < value})
    (radius : Nat)
    (captureLe :
      currentNextReceiptNativeFluxIntegralCaptureRadius current tolerance ≤
        radius)
    (time : Icc (0 : Real) (wholeRestartDuration current.contact)) :
    |∫ actual in (0 : Real)..time.1,
        actualNativeTurbulenceEnstrophyFluxPower current.nextReceipt
          (wholeRestartModes radius) actual| <
      2 * tolerance.1 := by
  let receipt := current.nextReceipt
  let modes := wholeRestartModes radius
  let flux : Real → Real := fun actual =>
    nativeTurbulenceEnstrophyFlux modes
      (receipt.wholePath
        (Set.projIcc (0 : Real) (wholeRestartDuration current.contact)
          (wholeRestartDuration_pos current.contact).le actual))
  have fluxContinuous : Continuous flux := by
    exact (receipt_nativeFlux_continuous receipt modes).comp
      continuous_projIcc
  have fluxAbsIntegrable : IntervalIntegrable (fun actual => |flux actual|)
      volume 0 (wholeRestartDuration current.contact) :=
    fluxContinuous.abs.intervalIntegrable _ _
  have fullCommonLt :=
    current_nextReceipt_nativeFlux_integral_abs_lt_of_captureRadius_le
      current tolerance radius captureLe
  have fullIntervalEq :
      (∫ actual in (0 : Real)..wholeRestartDuration current.contact,
          |flux actual|) =
        ∫ physicalTime,
          |nativeTurbulenceEnstrophyFlux modes
            (receipt.wholePath physicalTime)|
          ∂(commonTimeMeasure (wholeRestartDuration current.contact)) := by
    rw [← commonTime_integral_eq_intervalIntegral
      (wholeRestartDuration current.contact)
      (wholeRestartDuration_pos current.contact).le]
    apply integral_congr_ae
    filter_upwards [] with physicalTime
    dsimp only [flux]
    rw [Set.projIcc_of_mem
      (wholeRestartDuration_pos current.contact).le physicalTime.2]
  have fullIntervalLt :
      (∫ actual in (0 : Real)..wholeRestartDuration current.contact,
          |flux actual|) < tolerance.1 := by
    rw [fullIntervalEq]
    simpa only [receipt, modes] using fullCommonLt
  have prefixAbsLeFull :
      (∫ actual in (0 : Real)..time.1, |flux actual|) ≤
        ∫ actual in (0 : Real)..wholeRestartDuration current.contact,
          |flux actual| := by
    apply intervalIntegral.integral_mono_interval
    · exact le_rfl
    · exact time.2.1
    · exact time.2.2
    · exact Filter.Eventually.of_forall fun actual => abs_nonneg _
    · exact fluxAbsIntegrable
  have prefixAbsLt :
      (∫ actual in (0 : Real)..time.1, |flux actual|) < tolerance.1 :=
    prefixAbsLeFull.trans_lt fullIntervalLt
  have signedAbsLe :
      |∫ actual in (0 : Real)..time.1, flux actual| ≤
        ∫ actual in (0 : Real)..time.1, |flux actual| := by
    have normLe :=
      intervalIntegral.norm_integral_le_integral_norm_uIoc
        (μ := volume) (f := flux) (a := (0 : Real)) (b := time.1)
    rw [uIoc_of_le time.2.1] at normLe
    calc
      |∫ actual in (0 : Real)..time.1, flux actual| =
          ‖∫ actual in (0 : Real)..time.1, flux actual‖ := by
            rw [Real.norm_eq_abs]
      _ ≤ ∫ actual in Set.Ioc (0 : Real) time.1,
          ‖flux actual‖ ∂volume := normLe
      _ = ∫ actual in (0 : Real)..time.1, |flux actual| := by
        simp only [Real.norm_eq_abs]
        exact (intervalIntegral.integral_of_le time.2.1).symm
  have signedAbsLt :
      |∫ actual in (0 : Real)..time.1, flux actual| < tolerance.1 :=
    signedAbsLe.trans_lt prefixAbsLt
  have nativeEq :
      (∫ actual in (0 : Real)..time.1,
          actualNativeTurbulenceEnstrophyFluxPower receipt modes actual) =
        2 * ∫ actual in (0 : Real)..time.1, flux actual := by
    unfold actualNativeTurbulenceEnstrophyFluxPower
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro actual actualMem
    have actualMemIcc : actual ∈ Set.Icc (0 : Real) time.1 := by
      rw [Set.uIcc_of_le time.2.1] at actualMem
      exact actualMem
    have actualMemFull : actual ∈ Set.Icc (0 : Real)
        (wholeRestartDuration current.contact) :=
      ⟨actualMemIcc.1, actualMemIcc.2.trans time.2.2⟩
    dsimp only [flux, receipt, modes]
    change
      2 * nativeTurbulenceEnstrophyFlux (wholeRestartModes radius)
          (current.nextReceipt.wholePath
            (Set.projIcc (0 : Real)
              (wholeRestartDuration current.contact)
              (wholeRestartDuration_pos current.contact).le actual)) = _
    rw [Set.projIcc_of_mem
      (wholeRestartDuration_pos current.contact).le actualMemFull]
  rw [nativeEq, abs_mul, abs_of_pos (by norm_num : (0 : Real) < 2)]
  nlinarith

/-- The source-selected radius settles the installed native-flux work row.
Its factor two is the exact enstrophy-power convention. -/
theorem current_nextReceipt_nativeFluxWork_abs_lt_captureTolerance
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (tolerance : {value : Real // 0 < value}) :
    let radius :=
      currentNextReceiptNativeFluxIntegralCaptureRadius current tolerance
    |actualNativeTurbulenceEnstrophyFluxWork current.nextReceipt
        (wholeRestartModes radius)| < 2 * tolerance.1 := by
  dsimp only
  exact current_nextReceipt_nativeFluxWork_abs_lt_of_captureRadius_le
    current tolerance
      (currentNextReceiptNativeFluxIntegralCaptureRadius current tolerance)
      le_rfl

/-! ## One fixed cube for the current value and the full-edge settlement -/

/-- Every positive source tolerance generates a canonical radius beyond
which the current occurrence has less than that tolerance of coefficient
mass outside the punctured cube.  The witness is selected from convergence
of this current's own Fourier projections; it contains no terminal state or
future inventory. -/
theorem exists_currentCanonicalTailCaptureRadius
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (tolerance : {value : Real // 0 < value}) :
    ∃ threshold : Nat, ∀ radius ≥ threshold,
      wholeTailVorticityMass (wholeRestartModes radius)
        current.contact.physicalState < tolerance.1 := by
  have convergence := finiteRestartInventoryMass_tendsto_wholeMass
    current.contact.physicalState current.contact.physicalState_zero
  have eventuallyCaptured : ∀ᶠ radius : Nat in atTop,
      wholeVorticityEuclideanMass current.contact.physicalState -
          tolerance.1 <
        finiteStateVorticityCoefficientEnstrophy
          (wholeRestartModes radius) current.contact.physicalState := by
    apply convergence.eventually
    exact Ioi_mem_nhds (sub_lt_self _ tolerance.2)
  rcases (eventually_atTop.1 eventuallyCaptured) with
    ⟨threshold, thresholdSpec⟩
  refine ⟨threshold, ?_⟩
  intro radius thresholdLe
  rw [wholeTailVorticityMass_eq_whole_sub_finite]
  linarith [thresholdSpec radius thresholdLe]

/-- Least source-generated threshold for the current occurrence's initial
tail.  This retains the numerical reason why a later explicit tail envelope
is sufficient. -/
noncomputable def currentCanonicalTailCaptureRadius
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (tolerance : {value : Real // 0 < value}) : Nat := by
  classical
  exact Nat.find
    (exists_currentCanonicalTailCaptureRadius current tolerance)

/-- Every larger radius inherits the current occurrence's canonical tail
capture. -/
theorem currentCanonicalTailCaptureRadius_spec
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (tolerance : {value : Real // 0 < value})
    (radius : Nat)
    (captureLe :
      currentCanonicalTailCaptureRadius current tolerance ≤ radius) :
    wholeTailVorticityMass (wholeRestartModes radius)
        current.contact.physicalState < tolerance.1 := by
  classical
  exact Nat.find_spec
    (exists_currentCanonicalTailCaptureRadius current tolerance)
      radius captureLe

/-- Any explicit monotone tail threshold bounds the canonical least one. -/
theorem currentCanonicalTailCaptureRadius_le_of_spec
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (tolerance : {value : Real // 0 < value})
    (threshold : Nat)
    (thresholdSpec : ∀ radius ≥ threshold,
      wholeTailVorticityMass (wholeRestartModes radius)
        current.contact.physicalState < tolerance.1) :
    currentCanonicalTailCaptureRadius current tolerance ≤ threshold := by
  classical
  exact Nat.find_min'
    (exists_currentCanonicalTailCaptureRadius current tolerance)
    thresholdSpec

/-- A single source-selected radius simultaneously captures the complete
instantaneous signed work, the time-zero native value, the arbitrarily small
initial whole tail, and the full-receipt native work. -/
noncomputable def currentFullReceiptResolvedCaptureRadius
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (tolerance : {value : Real // 0 < value}) : Nat :=
  max (currentResolvedWorkCaptureRadius current tolerance)
    (max (currentMassCaptureRadius current)
      (max (currentCanonicalTailCaptureRadius current tolerance)
        (currentNextReceiptNativeFluxIntegralCaptureRadius current tolerance)))

def currentFullReceiptResolvedCaptureModes
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (tolerance : {value : Real // 0 < value}) :
    Finset IntegerWavevector :=
  wholeRestartModes
    (currentFullReceiptResolvedCaptureRadius current tolerance)

theorem currentFullReceiptResolvedCaptureModes_zeroNotMem
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (tolerance : {value : Real // 0 < value}) :
    (0 : IntegerWavevector) ∉
      currentFullReceiptResolvedCaptureModes current tolerance := by
  exact zero_not_mem_puncturedIntegerWaveFrequencyCube _

private theorem wholeRestartModes_mono_fullReceipt
    {small large : Nat}
    (smallLe : small ≤ large) :
    wholeRestartModes small ⊆ wholeRestartModes large := by
  intro wave waveMem
  rw [wholeRestartModes, puncturedIntegerWaveFrequencyCube] at waveMem ⊢
  rw [Finset.mem_erase] at waveMem ⊢
  exact ⟨waveMem.1, integerWaveFrequencyCube_mono smallLe waveMem.2⟩

/-- The joint cube captures the current whole coefficient mass within the
same absolute unit used by the scale clock. -/
theorem current_fullReceipt_wholeMass_lt_finiteMassBase
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (tolerance : {value : Real // 0 < value}) :
    wholeVorticityEuclideanMass current.contact.physicalState <
      finiteStateVorticityCoefficientEnstrophy
          (currentFullReceiptResolvedCaptureModes current tolerance)
          current.contact.physicalState + 1 := by
  have captured := currentMassCaptureModes_spec current
  have radiusLe : currentMassCaptureRadius current ≤
      currentFullReceiptResolvedCaptureRadius current tolerance :=
    (le_max_left _ _).trans (le_max_right _ _)
  have modesSubset : currentMassCaptureModes current ⊆
      currentFullReceiptResolvedCaptureModes current tolerance := by
    exact wholeRestartModes_mono_fullReceipt radiusLe
  have finiteLe :
      finiteStateVorticityCoefficientEnstrophy
          (currentMassCaptureModes current) current.contact.physicalState ≤
        finiteStateVorticityCoefficientEnstrophy
          (currentFullReceiptResolvedCaptureModes current tolerance)
          current.contact.physicalState := by
    unfold finiteStateVorticityCoefficientEnstrophy
    exact Finset.sum_le_sum_of_subset_of_nonneg modesSubset
      (fun wave _ _ => complexCoordinateAmplitudeSq_nonneg _)
  linarith

/-- Every cube beyond the joint threshold retains the same strict whole-to-
finite mass-base comparison. -/
theorem current_fullReceipt_wholeMass_lt_finiteMassBase_of_captureRadius_le
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (tolerance : {value : Real // 0 < value})
    (radius : Nat)
    (captureLe :
      currentFullReceiptResolvedCaptureRadius current tolerance ≤ radius) :
    wholeVorticityEuclideanMass current.contact.physicalState <
      currentFiniteEulerMassBase current (wholeRestartModes radius) := by
  have jointMass := current_fullReceipt_wholeMass_lt_finiteMassBase
    current tolerance
  have jointSubset :
      currentFullReceiptResolvedCaptureModes current tolerance ⊆
        wholeRestartModes radius := by
    unfold currentFullReceiptResolvedCaptureModes
    exact wholeRestartModes_mono_fullReceipt captureLe
  have finiteLe :
      finiteStateVorticityCoefficientEnstrophy
          (currentFullReceiptResolvedCaptureModes current tolerance)
          current.contact.physicalState ≤
        finiteStateVorticityCoefficientEnstrophy
          (wholeRestartModes radius) current.contact.physicalState := by
    unfold finiteStateVorticityCoefficientEnstrophy
    exact Finset.sum_le_sum_of_subset_of_nonneg jointSubset
      (fun wave _ _ => complexCoordinateAmplitudeSq_nonneg _)
  unfold currentFiniteEulerMassBase
  linarith

/-- Any cube beyond the joint threshold contains the current's canonical
mass-capture core, so the quantized coefficient ceiling is covered by the
same fixed factor four used by the seventh-order duration law. -/
theorem current_fullReceipt_ceiling_add_one_le_four_mul_finiteMassBase_of_captureRadius_le
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (tolerance : {value : Real // 0 < value})
    (radius : Nat)
    (captureLe :
      currentFullReceiptResolvedCaptureRadius current tolerance ≤ radius) :
    wholeRestartCoefficientCeiling current.contact + 1 ≤
      4 * currentFiniteEulerMassBase current (wholeRestartModes radius) := by
  have massRadiusLeJoint : currentMassCaptureRadius current ≤
      currentFullReceiptResolvedCaptureRadius current tolerance :=
    (le_max_left _ _).trans (le_max_right _ _)
  have captureSubset : currentMassCaptureModes current ⊆
      wholeRestartModes radius := by
    unfold currentMassCaptureModes
    exact wholeRestartModes_mono_fullReceipt
      (massRadiusLeJoint.trans captureLe)
  exact
    wholeRestartCoefficientCeiling_add_one_le_four_mul_currentFiniteEulerMassBase
      current (wholeRestartModes radius) captureSubset

/-- Every cube beyond the joint threshold retains the current occurrence's
whole coefficient mass up to the requested source tolerance. -/
theorem current_fullReceipt_initialTail_lt_of_captureRadius_le
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (tolerance : {value : Real // 0 < value})
    (radius : Nat)
    (captureLe :
      currentFullReceiptResolvedCaptureRadius current tolerance ≤ radius) :
    wholeTailVorticityMass (wholeRestartModes radius)
        current.contact.physicalState < tolerance.1 := by
  have tailLeJoint :
      currentCanonicalTailCaptureRadius current tolerance ≤
        currentFullReceiptResolvedCaptureRadius current tolerance :=
    (le_max_left _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _))
  exact currentCanonicalTailCaptureRadius_spec current tolerance radius
    (tailLeJoint.trans captureLe)

/-- The one source-selected full-receipt cube has arbitrarily small initial
whole tail. -/
theorem current_fullReceipt_initialTail_lt
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (tolerance : {value : Real // 0 < value}) :
    wholeTailVorticityMass
        (currentFullReceiptResolvedCaptureModes current tolerance)
        current.contact.physicalState < tolerance.1 := by
  exact current_fullReceipt_initialTail_lt_of_captureRadius_le
    current tolerance
      (currentFullReceiptResolvedCaptureRadius current tolerance) le_rfl

/-- On the joint full-receipt cube, the current complete signed work still
determines the resolved finite work to the same three-tolerance accuracy. -/
theorem current_fullReceipt_wholePower_sub_two_resolved_abs_lt
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (tolerance : {value : Real // 0 < value}) :
    let modes := currentFullReceiptResolvedCaptureModes current tolerance
    |currentInstantaneousWholePower current -
        2 * finiteGeneratorRealWork modes nu.coeff
          (complexSharpSupportProjection modes
            current.contact.physicalState)| <
      3 * tolerance.1 := by
  dsimp only [currentFullReceiptResolvedCaptureModes]
  exact current_wholePower_sub_two_resolved_abs_lt_of_captureRadius_le
    current tolerance
      (currentFullReceiptResolvedCaptureRadius current tolerance)
      (le_max_left _ _)

/-- Positive complete instantaneous headroom therefore gives a positive
resolved finite instruction on the identical full-receipt cube. -/
theorem current_fullReceipt_resolvedGeneratorWork_pos_of_wholePower_headroom
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (tolerance : {value : Real // 0 < value})
    (headroom : 3 * tolerance.1 < currentInstantaneousWholePower current) :
    let modes := currentFullReceiptResolvedCaptureModes current tolerance
    0 < finiteGeneratorRealWork modes nu.coeff
      (complexSharpSupportProjection modes current.contact.physicalState) := by
  dsimp only
  have close := current_fullReceipt_wholePower_sub_two_resolved_abs_lt
    current tolerance
  rcases abs_lt.mp close with ⟨_lower, upper⟩
  linarith

/-- The same cube settles the absolute native value throughout the complete
base horizon. -/
theorem current_fullReceipt_nativeFlux_integral_abs_lt
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (tolerance : {value : Real // 0 < value}) :
    let modes := currentFullReceiptResolvedCaptureModes current tolerance
    (∫ time,
      |nativeTurbulenceEnstrophyFlux modes
        (current.nextReceipt.wholePath time)|
      ∂(commonTimeMeasure (wholeRestartDuration current.contact))) <
      tolerance.1 := by
  dsimp only [currentFullReceiptResolvedCaptureModes]
  exact current_nextReceipt_nativeFlux_integral_abs_lt_of_captureRadius_le
    current tolerance
      (currentFullReceiptResolvedCaptureRadius current tolerance)
      ((le_max_right _ _).trans
        ((le_max_right _ _).trans (le_max_right _ _)))

/-- The installed native-work row on that identical cube is below twice the
requested source tolerance. -/
theorem current_fullReceipt_nativeFluxWork_abs_lt
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (tolerance : {value : Real // 0 < value}) :
    let modes := currentFullReceiptResolvedCaptureModes current tolerance
    |actualNativeTurbulenceEnstrophyFluxWork current.nextReceipt modes| <
      2 * tolerance.1 := by
  dsimp only [currentFullReceiptResolvedCaptureModes]
  exact current_nextReceipt_nativeFluxWork_abs_lt_of_captureRadius_le
    current tolerance
      (currentFullReceiptResolvedCaptureRadius current tolerance)
      ((le_max_right _ _).trans
        ((le_max_right _ _).trans (le_max_right _ _)))

/-- The same source-selected cube reads the complete actual tangent through
one exact scalar action fold.  Its initial endpoint is definitionally this
current's physical contact, so no inventory or initial-state transport is
left outside the edge. -/
theorem current_fullReceipt_actualJet_integral_eq_boundary
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (tolerance : {value : Real // 0 < value}) :
    let modes := currentFullReceiptResolvedCaptureModes current tolerance
    (∫ time,
      finiteNormalizedWorkActualJet modes nu.coeff
        (current.nextReceipt.wholePath time)
      ∂(commonTimeMeasure (wholeRestartDuration current.contact))) =
      finiteNormalizedGeneratorWork modes nu.coeff
          (complexSharpSupportProjection modes
            (current.nextReceipt.wholePath
              ⟨wholeRestartDuration current.contact,
                ⟨(wholeRestartDuration_pos current.contact).le, le_rfl⟩⟩)) -
        finiteNormalizedGeneratorWork modes nu.coeff
          (complexSharpSupportProjection modes
            current.contact.physicalState) := by
  dsimp only
  exact receipt_finiteNormalizedWorkActualJet_integral_eq_boundary
    current.nextReceipt
      (currentFullReceiptResolvedCaptureModes current tolerance)
      (currentFullReceiptResolvedCaptureModes_zeroNotMem current tolerance)

end
end ThreeDimensionalVorticityCoefficientFullReceiptNativeFluxSettlement
end NavierStokes
end SaturationMonoid
