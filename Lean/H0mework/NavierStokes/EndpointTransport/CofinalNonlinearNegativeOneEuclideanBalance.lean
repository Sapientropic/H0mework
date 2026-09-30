import H0mework.NavierStokes.Fourier.PuncturedEuclideanWholeCarrierMorphism
import H0mework.NavierStokes.Restart.EnstrophyWork
import H0mework.NavierStokes.Restart.FiniteTimeVorticityDivergence
import H0mework.NavierStokes.Restart.VelocityPairDiagonalAction
import H0mework.NavierStokes.Crossing.FrequencySupportExhaustion
import H0mework.NavierStokes.Fourier.NonlinearOutputCompiler
import H0mework.NavierStokes.Fourier.CoarseFilterProcess
import H0mework.NavierStokes.Restart.HalfCriticalComponentGluing
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Euclidean balance of the cofinal nonlinear negative-one action

The existing cofinal source prefix is measured in the ambient coordinate
sup norm.  This module first places every actual receipt on the complete
nonzero-wave Euclidean time-`L²` carrier, before any output or pair quotient.
On that carrier the unforced equation gives the exact same-receipt identity

`nonlinear square = tangent square + viscous square + endpoint enstrophy change`.

The endpoint term telescopes along the shifted native restart prefix.  Thus
the original divergent source prefix forces the exact sum of tangent square,
viscous square, and the one final boundary mass to diverge.  The accumulation
interface remains the source-owned `T` current; every positive-time state is
used only as the next current written by its actual receipt.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

open scoped BigOperators ENNReal Pointwise

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicUnitCellDivergence
open ThreeDimensionalPeriodicLocalEnergyAlgebra
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeSubsequence
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellWholeReceiptSquareContinuation
open ThreeDimensionalVorticityCoefficientStrongContinuationKineticDifferenceGronwall
open ThreeDimensionalVorticityCoefficientCoarseFilterProcess
open ThreeDimensionalVorticityCoefficientPhysicalCompiler
open ThreeDimensionalVorticityCoefficientPhysicalFourierCoordinateObserver
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientInfiniteNonlinearNegativeSobolev
open ThreeDimensionalVorticityCoefficientWholeNonlinearDifferenceNegativeOne
open ThreeDimensionalVorticityCoefficientWholeKineticDifferenceCancellation
open
  ThreeDimensionalVorticityCoefficientGeneratedPathInfiniteNonlinearNegativeOneTimeBudget
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageHilbertCompletion
open ThreeDimensionalVorticityCoefficientTransverseSpaceTimeNonlinearRow
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeNonlinearNegativeOne
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeCriticalSerrin
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeGradientLowerSemicontinuity
open ThreeDimensionalVorticityCoefficientWholeTangentEnergyTransport
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellWholeReceiptEnergyWriteBack
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeCoordinateParseval
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPositiveOutputWorkDualBudget
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairOccurrenceWork
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPreQuotientNonlinearWork
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEnstrophyWork
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartFiniteTimeObstruction
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartFiniteTimeVorticityDivergence
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSourcePairOccurrence
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairOccurrenceRateSettlement
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelKineticTriadRedirect
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityPairDiagonalAction
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingFrequencySupportExhaustion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartHalfCriticalComponentGluing
open ThreeDimensionalVorticityCoefficientNonlinearOutputCompiler
open ThreeDimensionalVorticityCoefficientWholeSerrinEnstrophyGronwall
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent

noncomputable section

namespace GeneratedInfiniteWholeRestartEndpointMacroLineage
namespace FullFrameBoundaryVorticityCofinalNonlinearNegativeOneEuclideanBalance

variable {nu : Viscosity}

/-! ## Whole nonzero-wave Euclidean time carrier -/

/-- Apply the already bounded nonzero-wave Euclideanization at every time of
one whole space-time state. -/
def puncturedEuclideanSpaceTimeState
    {requestedTime : Real}
    (state : SpaceTimeState requestedTime) :
    MeasureTheory.Lp WholeRestartKineticEndpointState 2
      (commonTimeMeasure requestedTime) :=
  (puncturedEuclideanizeCLM.compLpL 2
    (commonTimeMeasure requestedTime)) state

/-- Complete Euclidean square action of a whole space-time state, before any
frequency observation is selected. -/
def puncturedEuclideanSpaceTimeSquare
    {requestedTime : Real}
    (state : SpaceTimeState requestedTime) : Real :=
  ‖puncturedEuclideanSpaceTimeState state‖ ^ 2

theorem puncturedEuclideanSpaceTimeState_apply_ae
    {requestedTime : Real}
    (state : SpaceTimeState requestedTime) :
    ∀ᵐ time ∂(commonTimeMeasure requestedTime),
      puncturedEuclideanSpaceTimeState state time =
        puncturedEuclideanize (state time) := by
  exact puncturedEuclideanizeCLM.coeFn_compLpL state

theorem puncturedEuclideanSpaceTimeState_norm_sq_eq_integral
    {requestedTime : Real}
    (state : SpaceTimeState requestedTime) :
    ‖puncturedEuclideanSpaceTimeState state‖ ^ 2 =
      ∫ time,
        ‖puncturedEuclideanSpaceTimeState state time‖ ^ 2
        ∂(commonTimeMeasure requestedTime) := by
  let mapped := puncturedEuclideanSpaceTimeState state
  rw [MeasureTheory.Lp.norm_def]
  rw [MeasureTheory.toReal_eLpNorm
    (MeasureTheory.Lp.aestronglyMeasurable mapped)]
  rw [MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal
    (p := (2 : ℝ≥0∞)) (by norm_num) (by simp)
    (MeasureTheory.Lp.aestronglyMeasurable mapped)]
  norm_num
  have powerIdentity :
      ((∫ time,
          ‖mapped time‖ ^ 2 ∂(commonTimeMeasure requestedTime)) ^
            ((2 : Real)⁻¹)) ^ 2 =
        ∫ time,
          ‖mapped time‖ ^ 2 ∂(commonTimeMeasure requestedTime) :=
    Real.rpow_inv_natCast_pow (n := 2)
      (integral_nonneg fun _ => sq_nonneg _) (by norm_num)
  convert powerIdentity using 1
  all_goals norm_num

/-- The nonlinear negative-one state of an actual receipt has no zero row.
This is forced by its tangent-plus-viscous definition and the two generated
zero-row laws. -/
theorem receiptNonlinearNegativeOneState_zero_row_ae
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime) :
    ∀ᵐ time ∂(commonTimeMeasure requestedTime),
      (receiptNonlinearNegativeOneState receipt time) 0 = 0 := by
  filter_upwards [
    MeasureTheory.Lp.coeFn_add
      receipt.wholeTangent (receiptViscousNegativeOneState receipt),
    receiptWholeTangent_zero_row_ae receipt,
    receiptViscousNegativeOneState_row_ae receipt 0] with
      time nonlinearEq tangentZero viscousEq
  rw [receiptNonlinearNegativeOneState, nonlinearEq]
  change
    (receipt.wholeTangent time) 0 +
        (receiptViscousNegativeOneState receipt time) 0 = 0
  rw [tangentZero, viscousEq]
  simp [integerWaveViscousMultiplier, integerWaveNormSq]

/-- Replacing the ambient coordinate sup norm by the complete nonzero-wave
Euclidean observation cannot lose the source-generated nonlinear square.
No frequency, support, or faithfulness certificate is supplied. -/
theorem receiptNonlinearNegativeOneSquare_le_euclideanSquare
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime) :
    ‖receiptNonlinearNegativeOneState receipt‖ ^ 2 ≤
      puncturedEuclideanSpaceTimeSquare
        (receiptNonlinearNegativeOneState receipt) := by
  have mappedAE :=
    puncturedEuclideanSpaceTimeState_apply_ae
      (receiptNonlinearNegativeOneState receipt)
  have pointwiseNormLe :
      ∀ᵐ time ∂(commonTimeMeasure requestedTime),
        ‖receiptNonlinearNegativeOneState receipt time‖ ≤
          ‖puncturedEuclideanSpaceTimeState
            (receiptNonlinearNegativeOneState receipt) time‖ := by
    filter_upwards [mappedAE,
      receiptNonlinearNegativeOneState_zero_row_ae receipt] with
        time mappedEq zeroRow
    rw [mappedEq]
    have squareLe :=
      state_norm_sq_le_puncturedEuclideanize_of_zero_row
        (receiptNonlinearNegativeOneState receipt time) zeroRow
    nlinarith [norm_nonneg
        (receiptNonlinearNegativeOneState receipt time),
      norm_nonneg
        (puncturedEuclideanize
          (receiptNonlinearNegativeOneState receipt time))]
  have normLe := MeasureTheory.Lp.norm_le_norm_of_ae_le pointwiseNormLe
  unfold puncturedEuclideanSpaceTimeSquare
  nlinarith [norm_nonneg (receiptNonlinearNegativeOneState receipt),
    norm_nonneg
      (puncturedEuclideanSpaceTimeState
        (receiptNonlinearNegativeOneState receipt))]

/-- On almost every physical time of one actual receipt, the complete
negative-one nonlinear row is exactly the inverse-Laplacian weighted
aggregate of that receipt's literal velocity--vorticity pair incidences.
This is the same PDE write on two carriers, not an estimate or a new
boundary outcome. -/
theorem receiptNonlinearNegativeOneEuclideanMass_ae_eq_pairAggregate
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime) :
    ∀ᵐ time ∂(commonTimeMeasure requestedTime),
      ‖puncturedEuclideanize
        (receiptNonlinearNegativeOneState receipt time)‖ ^ 2 =
        ∑' output : IntegerWavevector,
          actualWholeContinuousPairAggregateNegativeOneDensity
            receipt time output := by
  have rowAE :
      ∀ᵐ time ∂(commonTimeMeasure requestedTime),
        ∀ output : IntegerWavevector, output ≠ 0 →
          (Real.sqrt (integerWaveViscousMultiplier output) : Real) •
              (receiptNonlinearNegativeOneState receipt time) output =
            wholeStateVorticityBilinearCoefficientAt
              (receipt.transverseLimit time).1
              (receipt.transverseLimit time).1 output := by
    exact eventually_countable_forall.2 fun output => by
      by_cases outputZero : output = 0
      · filter_upwards with time
        intro outputNonzero
        exact (outputNonzero outputZero).elim
      · filter_upwards [
          receiptNonlinearNegativeOneState_row_ae
            receipt output outputZero] with time rowEq
        intro _outputNonzero
        exact rowEq
  filter_upwards [
    receiptNonlinearNegativeOneState_zero_row_ae receipt,
    receipt.wholePath_eq_transverse_ae,
    rowAE] with time zeroRow pathEq rowEq
  rw [puncturedEuclideanize_norm_sq]
  change
    puncturedWholeVorticityEuclideanMass
        (receiptNonlinearNegativeOneState receipt time) =
      ∑' output : IntegerWavevector,
        actualWholeContinuousPairAggregateNegativeOneDensity
          receipt time output
  rw [puncturedWholeVorticityEuclideanMass_eq_whole_of_zero_row
    _ zeroRow]
  unfold wholeVorticityEuclideanMass
  apply tsum_congr
  intro output
  rw [vorticityRowAmplitude_sq]
  rw [← complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
  by_cases outputZero : output = 0
  · subst output
    simp [zeroRow, actualWholeContinuousPairAggregateNegativeOneDensity,
      integerWaveViscousMultiplier, complexCoordinateAmplitudeSq]
  · have multiplierPos :
        0 < integerWaveViscousMultiplier output := by
      unfold integerWaveViscousMultiplier
      exact mul_pos
        (sq_pos_of_pos (mul_pos zero_lt_two Real.pi_pos))
        (integerWaveNormSq_pos outputZero)
    have pairEq :=
      tsum_actualWholeContinuousPairVector_eq_nonlinearOutput
        receipt output time
    rw [pathEq] at pairEq
    have weightedEq := rowEq output outputZero
    rw [wholeStateVorticityBilinearCoefficientAt_self,
      ← pairEq] at weightedEq
    have amplitudeEq :=
      congrArg complexCoordinateAmplitudeSq weightedEq
    rw [complexCoordinateAmplitudeSq_real_smul,
      Real.sq_sqrt multiplierPos.le] at amplitudeEq
    unfold actualWholeContinuousPairAggregateNegativeOneDensity
    rw [← amplitudeEq]
    field_simp [multiplierPos.ne']

/-- The complete nonlinear Euclidean square on one source-selected edge is
the ordinary time integral of the identical pair-aggregate density. -/
theorem
    wholeRestartNextPrefixNonlinearNegativeOneEuclideanSquare_eq_pairAggregate
    (current : GeneratedWholeRestartCurrent nu) :
    puncturedEuclideanSpaceTimeSquare
        (receiptNonlinearNegativeOneState
          current.nextContact.prefixReceipt) =
      ∫ time,
        (∑' output : IntegerWavevector,
          actualWholeContinuousPairAggregateNegativeOneDensity
            current.nextContact.prefixReceipt time output)
        ∂(commonTimeMeasure current.nextContact.time.1) := by
  unfold puncturedEuclideanSpaceTimeSquare
  rw [puncturedEuclideanSpaceTimeState_norm_sq_eq_integral]
  apply integral_congr_ae
  filter_upwards [
    puncturedEuclideanSpaceTimeState_apply_ae
      (receiptNonlinearNegativeOneState
        current.nextContact.prefixReceipt),
    receiptNonlinearNegativeOneEuclideanMass_ae_eq_pairAggregate
      current.nextContact.prefixReceipt] with time mappedEq pairEq
  rw [mappedEq, pairEq]

theorem receiptPairAggregateNegativeOneMass_ae_eq_diagonal_add_literalCross
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime) :
    ∀ᵐ time ∂(commonTimeMeasure requestedTime),
      (∑' output : IntegerWavevector,
        actualWholeContinuousPairAggregateNegativeOneDensity
          receipt time output) =
        actualWholeSymmetricVorticityPairNegativeOneDiagonalMass
            receipt time +
          actualWholeSymmetricVorticityPairNegativeOneLiteralCrossMass
            receipt time := by
  have gradientSummable :
      Summable fun wave : IntegerWavevector =>
        wholeSpaceTimeVorticityGradientDensity requestedTime
          (transverseSpaceTimeInclusion requestedTime
            receipt.transverseLimit) wave := by
    simpa only [receipt.stateLimit_eq_transverse] using
      receipt.gradient_summable
  have gradientAE :=
    transversePointwiseGradient_ae_summable
      receipt.transverseLimit gradientSummable
  filter_upwards [gradientAE, receipt.wholePath_eq_transverse_ae] with
      time timeGradientSummable pathEq
  have wholePathGradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (receipt.wholePath time wave) := by
    simpa only [pathEq] using timeGradientSummable
  simpa only [actualWholeContinuousPairAggregateNegativeOneDensity] using
    actualWholeContinuousPairAggregateNegativeOneMass_eq_diagonal_add_literalCross
      receipt time wholePathGradientSummable

theorem integrable_receiptPairAggregateNegativeOneMass
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime) :
    Integrable
      (fun time =>
        ∑' output : IntegerWavevector,
          actualWholeContinuousPairAggregateNegativeOneDensity
            receipt time output)
      (commonTimeMeasure requestedTime) := by
  have mappedSquareIntegrable :
      Integrable
        (fun time =>
          ‖puncturedEuclideanSpaceTimeState
            (receiptNonlinearNegativeOneState receipt) time‖ ^ 2)
        (commonTimeMeasure requestedTime) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (MeasureTheory.Lp.memLp
        (puncturedEuclideanSpaceTimeState
          (receiptNonlinearNegativeOneState receipt))).integrable_norm_rpow
        (by norm_num) (by norm_num)
  apply mappedSquareIntegrable.congr
  filter_upwards [
    puncturedEuclideanSpaceTimeState_apply_ae
      (receiptNonlinearNegativeOneState receipt),
    receiptNonlinearNegativeOneEuclideanMass_ae_eq_pairAggregate
      receipt] with time mappedEq pairEq
  rw [mappedEq, pairEq]

theorem
    integrable_nextContactPrefixSymmetricVorticityPairNegativeOneLiteralCrossMass
    (current : GeneratedWholeRestartCurrent nu) :
    Integrable
      (actualWholeSymmetricVorticityPairNegativeOneLiteralCrossMass
        current.nextContact.prefixReceipt)
      (commonTimeMeasure current.nextContact.time.1) := by
  have aggregateIntegrable :=
    integrable_receiptPairAggregateNegativeOneMass
      current.nextContact.prefixReceipt
  have diagonalIntegrable :=
    integrable_nextContactPrefixSymmetricVorticityPairNegativeOneDiagonalMass
      current
  have differenceIntegrable := aggregateIntegrable.sub diagonalIntegrable
  apply differenceIntegrable.congr
  filter_upwards [
    receiptPairAggregateNegativeOneMass_ae_eq_diagonal_add_literalCross
      current.nextContact.prefixReceipt] with time splitEq
  change
    (∑' output : IntegerWavevector,
        actualWholeContinuousPairAggregateNegativeOneDensity
          current.nextContact.prefixReceipt time output) -
        actualWholeSymmetricVorticityPairNegativeOneDiagonalMass
          current.nextContact.prefixReceipt time =
      actualWholeSymmetricVorticityPairNegativeOneLiteralCrossMass
        current.nextContact.prefixReceipt time
  rw [splitEq]
  ring

/-- Signed literal cross-pair incidence accumulated on one actual native
edge.  Unlike the diagonal, this quantity is not declared nonnegative; its
sign and cancellation remain part of the original NS write. -/
def wholeRestartNextPrefixSymmetricVorticityPairLiteralCrossAction
    (current : GeneratedWholeRestartCurrent nu) : Real :=
  ∫ time,
    actualWholeSymmetricVorticityPairNegativeOneLiteralCrossMass
      current.nextContact.prefixReceipt time
    ∂(commonTimeMeasure current.nextContact.time.1)

/-- Exact same-edge polarization of the generated nonlinear action.  The
first term is already paid by the kinetic--viscous ledger; the second is the
remaining literal cross-incidence responsibility. -/
theorem
    nextPrefix_receiptNonlinearNegativeOneEuclideanSquare_eq_diagonal_add_literalCross
    (current : GeneratedWholeRestartCurrent nu) :
    puncturedEuclideanSpaceTimeSquare
        (receiptNonlinearNegativeOneState
          current.nextContact.prefixReceipt) =
      wholeRestartNextPrefixSymmetricVorticityPairDiagonalActionReal current +
        wholeRestartNextPrefixSymmetricVorticityPairLiteralCrossAction
          current := by
  rw [
    wholeRestartNextPrefixNonlinearNegativeOneEuclideanSquare_eq_pairAggregate]
  rw [wholeRestartNextPrefixSymmetricVorticityPairDiagonalActionReal_eq_integral]
  unfold wholeRestartNextPrefixSymmetricVorticityPairLiteralCrossAction
  rw [← integral_add
    (integrable_nextContactPrefixSymmetricVorticityPairNegativeOneDiagonalMass
      current)
    (integrable_nextContactPrefixSymmetricVorticityPairNegativeOneLiteralCrossMass
      current)]
  apply integral_congr_ae
  exact
    receiptPairAggregateNegativeOneMass_ae_eq_diagonal_add_literalCross
      current.nextContact.prefixReceipt

/-! ## Same-receipt cross term -/

private theorem complexCoordinateRealInner_comm
    (left right : ComplexCoordinateVector) :
    complexCoordinateRealInner left right =
      complexCoordinateRealInner right left := by
  unfold complexCoordinateRealInner
  apply Finset.sum_congr rfl
  intro coordinate _coordinateMem
  ring

/-- On one nonzero row, the Euclidean tangent/viscous cross term is exactly
viscosity times the receipt's physical net-work row.  Both sides use the
same actual interval and the same receipt occurrence. -/
private theorem receipt_puncturedEuclidean_crossRowIntegral_eq_netWork
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (wave : NonzeroIntegerWavevector) :
    (∫ time,
        2 * RCLike.re (inner ℂ
          (puncturedEuclideanSpaceTimeState receipt.wholeTangent time wave)
          (puncturedEuclideanSpaceTimeState
            (receiptViscousNegativeOneState receipt) time wave))
        ∂(commonTimeMeasure requestedTime)) =
      nu.coeff * actualWholeRowNetWork receipt wave.1 := by
  have tangentMapped :=
    puncturedEuclideanSpaceTimeState_apply_ae receipt.wholeTangent
  have viscousMapped :=
    puncturedEuclideanSpaceTimeState_apply_ae
      (receiptViscousNegativeOneState receipt)
  have tangentRow :=
    receipt.rowTangent_eq_wholeTangent_ae wave.1 wave.2
  have viscousRow :=
    receiptViscousNegativeOneState_row_ae receipt wave.1
  rw [actualWholeRowNetWork, dif_neg wave.2]
  rw [← commonTime_integral_eq_intervalIntegral
    requestedTime receipt.requestedTimePos.le
    (fun actual =>
      2 * complexCoordinateRealInner
        (receipt.rowExtension wave.1 wave.2 actual)
        (commonTimeZeroExtension requestedTime
          (receipt.rowTangent wave.1 wave.2) actual))]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [tangentMapped, viscousMapped,
    tangentRow, viscousRow] with
      time tangentMappedEq viscousMappedEq tangentRowEq viscousRowEq
  rw [tangentMappedEq, viscousMappedEq]
  change
    2 * (inner ℂ
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
  rw [receipt.rowExtension_on_interval,
    commonTimeZeroExtension_of_mem requestedTime
      (receipt.rowTangent wave.1 wave.2) time.1 time.property]
  rw [← tangentRowEqReal]
  rw [complexCoordinateRealInner_real_smul_right]
  rw [complexCoordinateRealInner_real_smul_right]
  rw [complexCoordinateRealInner_comm
    ((receipt.wholeTangent time) wave.1)
    (receipt.wholePath time wave.1)]
  ring

/-- Time integration and the complete nonzero-wave cross series commute for
the two actual `L²` states of one receipt.  The majorant is generated by
their own square norms. -/
private theorem hasSum_receipt_puncturedEuclidean_crossRowIntegral
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime) :
    HasSum
      (fun wave : NonzeroIntegerWavevector =>
        ∫ time,
          2 * (inner ℂ
            (puncturedEuclideanSpaceTimeState
              receipt.wholeTangent time wave)
            (puncturedEuclideanSpaceTimeState
              (receiptViscousNegativeOneState receipt) time wave)).re
          ∂(commonTimeMeasure requestedTime))
      (2 * (inner ℂ
        (puncturedEuclideanSpaceTimeState receipt.wholeTangent)
        (puncturedEuclideanSpaceTimeState
          (receiptViscousNegativeOneState receipt))).re) := by
  let tangent :=
    puncturedEuclideanSpaceTimeState receipt.wholeTangent
  let viscous :=
    puncturedEuclideanSpaceTimeState
      (receiptViscousNegativeOneState receipt)
  let crossDensity :
      NonzeroIntegerWavevector →
        Icc (0 : Real) requestedTime → Real :=
    fun wave time =>
      2 * (inner ℂ
        (tangent time wave) (viscous time wave)).re
  let squareBound :
      NonzeroIntegerWavevector →
        Icc (0 : Real) requestedTime → Real :=
    fun wave time =>
      2 * (‖tangent time wave‖ ^ 2 +
        ‖viscous time wave‖ ^ 2)
  have crossDensityMeasurable :
      ∀ wave : NonzeroIntegerWavevector,
        AEStronglyMeasurable
          (crossDensity wave)
          (commonTimeMeasure requestedTime) := by
    intro wave
    have tangentRowMeasurable :
        AEStronglyMeasurable
          (fun time => tangent time wave)
          (commonTimeMeasure requestedTime) :=
      (lp.evalCLM ℂ
        (fun _ : NonzeroIntegerWavevector =>
          ComplexCoordinateEuclidean) 2 wave).continuous
        |>.comp_aestronglyMeasurable
          (MeasureTheory.Lp.aestronglyMeasurable tangent)
    have viscousRowMeasurable :
        AEStronglyMeasurable
          (fun time => viscous time wave)
          (commonTimeMeasure requestedTime) :=
      (lp.evalCLM ℂ
        (fun _ : NonzeroIntegerWavevector =>
          ComplexCoordinateEuclidean) 2 wave).continuous
        |>.comp_aestronglyMeasurable
          (MeasureTheory.Lp.aestronglyMeasurable viscous)
    exact ((Complex.continuous_re.comp_aestronglyMeasurable
      (tangentRowMeasurable.inner viscousRowMeasurable)).const_mul 2)
  have integratedHasSum :
      HasSum
        (fun wave : NonzeroIntegerWavevector =>
          ∫ time, crossDensity wave time
            ∂(commonTimeMeasure requestedTime))
        (∫ time,
          2 * (inner ℂ
            (tangent time) (viscous time)).re
          ∂(commonTimeMeasure requestedTime)) := by
    apply
      MeasureTheory.hasSum_integral_of_dominated_convergence
        squareBound crossDensityMeasurable
    · intro wave
      filter_upwards with time
      change
        ‖2 * (inner ℂ
            (tangent time wave) (viscous time wave)).re‖ ≤
          2 * (‖tangent time wave‖ ^ 2 +
            ‖viscous time wave‖ ^ 2)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : Real) ≤ 2)]
      have reLe := Complex.abs_re_le_norm
        (inner ℂ (tangent time wave) (viscous time wave))
      have innerLe := norm_inner_le_norm (𝕜 := ℂ)
        (tangent time wave) (viscous time wave)
      calc
        2 * |(inner ℂ
            (tangent time wave) (viscous time wave)).re| ≤
            2 * ‖inner ℂ
              (tangent time wave) (viscous time wave)‖ :=
          mul_le_mul_of_nonneg_left reLe (by norm_num)
        _ ≤ 2 * (‖tangent time wave‖ *
            ‖viscous time wave‖) :=
          mul_le_mul_of_nonneg_left innerLe (by norm_num)
        _ ≤ 2 * (‖tangent time wave‖ ^ 2 +
            ‖viscous time wave‖ ^ 2) := by
          nlinarith [sq_nonneg
            (‖tangent time wave‖ - ‖viscous time wave‖)]
    · filter_upwards with time
      have tangentHasSum :=
        lp.hasSum_norm (p := (2 : ℝ≥0∞))
          (by norm_num) (tangent time)
      have viscousHasSum :=
        lp.hasSum_norm (p := (2 : ℝ≥0∞))
          (by norm_num) (viscous time)
      simpa only [squareBound, ENNReal.toReal_ofNat,
        Real.rpow_two] using
          ((tangentHasSum.add viscousHasSum).mul_left 2).summable
    · rw [show
        (fun time =>
          ∑' wave : NonzeroIntegerWavevector,
            squareBound wave time) =
          (fun time =>
            2 * (‖tangent time‖ ^ 2 +
              ‖viscous time‖ ^ 2)) by
        funext time
        have tangentHasSum :=
          lp.hasSum_norm (p := (2 : ℝ≥0∞))
            (by norm_num) (tangent time)
        have viscousHasSum :=
          lp.hasSum_norm (p := (2 : ℝ≥0∞))
            (by norm_num) (viscous time)
        simpa only [squareBound, ENNReal.toReal_ofNat,
          Real.rpow_two] using
            ((tangentHasSum.add viscousHasSum).mul_left 2).tsum_eq]
      exact (((MeasureTheory.Lp.memLp tangent).integrable_norm_pow
        (by norm_num)).add
          ((MeasureTheory.Lp.memLp viscous).integrable_norm_pow
            (by norm_num))).const_mul 2
    · filter_upwards with time
      rw [lp.inner_eq_tsum (𝕜 := ℂ)]
      have innerHasSum :=
        (lp.summable_inner (𝕜 := ℂ)
          (tangent time) (viscous time)).hasSum
      have realHasSum :=
        innerHasSum.map Complex.reCLM Complex.reCLM.continuous
      simpa only [crossDensity, Function.comp_apply,
        Complex.reCLM_apply] using realHasSum.mul_left 2
  have totalCrossIntegral :
      (∫ time,
          2 * (inner ℂ
            (tangent time) (viscous time)).re
          ∂(commonTimeMeasure requestedTime)) =
        2 * (inner ℂ tangent viscous).re := by
    rw [MeasureTheory.L2.inner_def]
    have reIntegral :
        (∫ time,
            (inner ℂ (tangent time) (viscous time)).re
            ∂(commonTimeMeasure requestedTime)) =
          (∫ time,
            inner ℂ (tangent time) (viscous time)
            ∂(commonTimeMeasure requestedTime)).re := by
      exact integral_re (𝕜 := ℂ)
        (MeasureTheory.L2.integrable_inner tangent viscous)
    calc
      _ = 2 * (∫ time,
          (inner ℂ (tangent time) (viscous time)).re
          ∂(commonTimeMeasure requestedTime)) := by
        rw [integral_const_mul]
      _ = _ := by rw [reIntegral]
  rw [totalCrossIntegral] at integratedHasSum
  simpa only [tangent, viscous, crossDensity] using integratedHasSum

/-- The complete Euclidean tangent/viscous cross term is the exact
coefficient-enstrophy change of the same actual unforced receipt. -/
theorem receipt_puncturedEuclidean_cross_eq_boundary
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime) :
    2 * RCLike.re (inner ℂ
        (puncturedEuclideanSpaceTimeState receipt.wholeTangent)
        (puncturedEuclideanSpaceTimeState
          (receiptViscousNegativeOneState receipt))) =
      nu.coeff *
        (wholeVorticityEuclideanMass
            (receipt.wholePath
              ⟨requestedTime,
                ⟨receipt.requestedTimePos.le, le_rfl⟩⟩) -
          wholeVorticityEuclideanMass initialState) := by
  change
    2 * (inner ℂ
        (puncturedEuclideanSpaceTimeState receipt.wholeTangent)
        (puncturedEuclideanSpaceTimeState
          (receiptViscousNegativeOneState receipt))).re = _
  have crossHasSum :=
    hasSum_receipt_puncturedEuclidean_crossRowIntegral receipt
  rw [← crossHasSum.tsum_eq]
  rw [show
      (fun wave : NonzeroIntegerWavevector =>
        ∫ time,
          2 * (inner ℂ
            (puncturedEuclideanSpaceTimeState
              receipt.wholeTangent time wave)
            (puncturedEuclideanSpaceTimeState
              (receiptViscousNegativeOneState receipt) time wave)).re
          ∂(commonTimeMeasure requestedTime)) =
        (fun wave : NonzeroIntegerWavevector =>
          nu.coeff * actualWholeRowNetWork receipt wave.1) by
    funext wave
    exact receipt_puncturedEuclidean_crossRowIntegral_eq_netWork
      receipt wave]
  rw [tsum_mul_left]
  simp_rw [actualWholeRowNetWork_eq_terminal_sub_initial]
  rw [Summable.tsum_sub
    (summable_puncturedWholeVorticityEuclideanMass
      (receipt.wholePath
        ⟨requestedTime,
          ⟨receipt.requestedTimePos.le, le_rfl⟩⟩))
    (summable_puncturedWholeVorticityEuclideanMass initialState)]
  change
    nu.coeff *
        (puncturedWholeVorticityEuclideanMass
            (receipt.wholePath
              ⟨requestedTime,
                ⟨receipt.requestedTimePos.le, le_rfl⟩⟩) -
          puncturedWholeVorticityEuclideanMass initialState) = _
  have terminalZero :
      receipt.wholePath
          ⟨requestedTime,
            ⟨receipt.requestedTimePos.le, le_rfl⟩⟩ 0 = 0 :=
    receipt.wholePath_zero_row _
  have initialZero : initialState 0 = 0 := by
    rw [← receipt.wholePath_initial]
    exact receipt.wholePath_zero_row _
  rw [puncturedWholeVorticityEuclideanMass_eq_whole_of_zero_row
      _ terminalZero,
    puncturedWholeVorticityEuclideanMass_eq_whole_of_zero_row
      _ initialZero]

/-- The complete tangent/viscous cross term telescopes on every exact `Ico`
of the original whole-restart run.  Every summand is the same receipt's
whole-vorticity boundary write; no cofinal selector or auxiliary relation is
part of the theorem mouth. -/
theorem wholeRestartIcoPuncturedEuclideanCross_telescope
    (initial : GeneratedWholeRestartCurrent nu)
    (start finish : Nat)
    (startLeFinish : start ≤ finish) :
    (∑ index ∈ Finset.Ico start finish,
      2 * RCLike.re (inner ℂ
        (puncturedEuclideanSpaceTimeState
          (run initial index).nextContact.prefixReceipt.wholeTangent)
        (puncturedEuclideanSpaceTimeState
          (receiptViscousNegativeOneState
            (run initial index).nextContact.prefixReceipt)))) =
      nu.coeff *
        (restartPhysicalVorticityMass initial finish -
          restartPhysicalVorticityMass initial start) := by
  let mass : Nat → Real := fun index =>
    restartPhysicalVorticityMass initial index
  have edgeTrace (index : Nat) :
      2 * RCLike.re (inner ℂ
          (puncturedEuclideanSpaceTimeState
            (run initial index).nextContact.prefixReceipt.wholeTangent)
          (puncturedEuclideanSpaceTimeState
            (receiptViscousNegativeOneState
              (run initial index).nextContact.prefixReceipt))) =
        nu.coeff * (mass (index + 1) - mass index) := by
    rw [receipt_puncturedEuclidean_cross_eq_boundary]
    rw [(run initial index).nextContact_prefix_terminal]
    rfl
  calc
    (∑ index ∈ Finset.Ico start finish,
        2 * RCLike.re (inner ℂ
          (puncturedEuclideanSpaceTimeState
            (run initial index).nextContact.prefixReceipt.wholeTangent)
          (puncturedEuclideanSpaceTimeState
            (receiptViscousNegativeOneState
              (run initial index).nextContact.prefixReceipt)))) =
        ∑ index ∈ Finset.Ico start finish,
          nu.coeff * (mass (index + 1) - mass index) := by
      apply Finset.sum_congr rfl
      intro index _indexMem
      exact edgeTrace index
    _ = nu.coeff *
        ∑ index ∈ Finset.Ico start finish,
          (mass (index + 1) - mass index) := by
      rw [Finset.mul_sum]
    _ = nu.coeff *
        ((∑ index ∈ Finset.range finish,
            (mass (index + 1) - mass index)) -
          ∑ index ∈ Finset.range start,
            (mass (index + 1) - mass index)) := by
      rw [Finset.sum_Ico_eq_sub _ startLeFinish]
    _ = nu.coeff *
        ((mass finish - mass 0) - (mass start - mass 0)) := by
      rw [Finset.sum_range_sub, Finset.sum_range_sub]
    _ = nu.coeff * (mass finish - mass start) := by ring
    _ = nu.coeff *
        (restartPhysicalVorticityMass initial finish -
          restartPhysicalVorticityMass initial start) := by
      rfl

/-- Exact `N = T + V + boundary cross` identity on the complete punctured
Euclidean space-time carrier.  This is a same-event equality, not an
estimate and not a caller-supplied energy law. -/
theorem receiptNonlinearNegativeOneEuclideanBalance
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime) :
    puncturedEuclideanSpaceTimeSquare
          (receiptNonlinearNegativeOneState receipt) +
        nu.coeff * wholeVorticityEuclideanMass initialState =
      puncturedEuclideanSpaceTimeSquare receipt.wholeTangent +
        puncturedEuclideanSpaceTimeSquare
          (receiptViscousNegativeOneState receipt) +
        nu.coeff *
          wholeVorticityEuclideanMass
            (receipt.wholePath
              ⟨requestedTime,
                ⟨receipt.requestedTimePos.le, le_rfl⟩⟩) := by
  have nonlinearMapped :
      puncturedEuclideanSpaceTimeState
          (receiptNonlinearNegativeOneState receipt) =
        puncturedEuclideanSpaceTimeState receipt.wholeTangent +
          puncturedEuclideanSpaceTimeState
            (receiptViscousNegativeOneState receipt) := by
    unfold receiptNonlinearNegativeOneState
      puncturedEuclideanSpaceTimeState
    exact map_add _ _ _
  unfold puncturedEuclideanSpaceTimeSquare
  rw [nonlinearMapped, norm_add_sq (𝕜 := ℂ),
    receipt_puncturedEuclidean_cross_eq_boundary receipt]
  ring

/-- Pairing the actual nonlinear row with the actual viscous row retains
both the whole-vorticity boundary gain and the complete viscous square.  This
is the signed same-receipt identity used to absorb finite-band projection
errors; no projected dynamics or boundary conclusion is supplied at the
theorem mouth. -/
theorem receiptNonlinearViscousCross_eq_boundary_add_viscousSquare
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime) :
    2 * RCLike.re (inner ℂ
        (puncturedEuclideanSpaceTimeState
          (receiptNonlinearNegativeOneState receipt))
        (puncturedEuclideanSpaceTimeState
          (receiptViscousNegativeOneState receipt))) =
      nu.coeff *
          (wholeVorticityEuclideanMass
              (receipt.wholePath
                ⟨requestedTime,
                  ⟨receipt.requestedTimePos.le, le_rfl⟩⟩) -
            wholeVorticityEuclideanMass initialState) +
        2 * puncturedEuclideanSpaceTimeSquare
          (receiptViscousNegativeOneState receipt) := by
  have nonlinearMapped :
      puncturedEuclideanSpaceTimeState
          (receiptNonlinearNegativeOneState receipt) =
        puncturedEuclideanSpaceTimeState receipt.wholeTangent +
          puncturedEuclideanSpaceTimeState
            (receiptViscousNegativeOneState receipt) := by
    unfold receiptNonlinearNegativeOneState
      puncturedEuclideanSpaceTimeState
    exact map_add _ _ _
  have viscousSelf :
      RCLike.re (inner ℂ
          (puncturedEuclideanSpaceTimeState
            (receiptViscousNegativeOneState receipt))
          (puncturedEuclideanSpaceTimeState
            (receiptViscousNegativeOneState receipt))) =
        ‖puncturedEuclideanSpaceTimeState
          (receiptViscousNegativeOneState receipt)‖ ^ 2 := by
    rw [inner_self_eq_norm_sq (𝕜 := ℂ)]
  have reAdd (left right : ℂ) :
      RCLike.re (left + right) =
        RCLike.re left + RCLike.re right := by
    rw [← RCLike.reCLM_apply]
    exact map_add (RCLike.reCLM : StrongDual ℝ ℂ) left right
  have tangentViscousCross :=
    receipt_puncturedEuclidean_cross_eq_boundary receipt
  rw [nonlinearMapped, inner_add_left, reAdd, viscousSelf]
  unfold puncturedEuclideanSpaceTimeSquare
  linear_combination tangentViscousCross

private theorem two_mul_viscosity_complexCoordinateRealInner_le
    (wave : IntegerWavevector)
    (waveNe : wave ≠ 0)
    (left right : ComplexCoordinateVector) :
    2 * nu.coeff * complexCoordinateRealInner left right ≤
      nu.coeff ^ 2 * integerWaveViscousMultiplier wave *
          complexCoordinateAmplitudeSq left +
        (integerWaveViscousMultiplier wave)⁻¹ *
          complexCoordinateAmplitudeSq right := by
  let weight := nu.coeff * integerWaveViscousMultiplier wave
  have multiplierPos : 0 < integerWaveViscousMultiplier wave := by
    unfold integerWaveViscousMultiplier
    exact mul_pos
      (sq_pos_of_pos (mul_pos zero_lt_two Real.pi_pos))
      (integerWaveNormSq_pos waveNe)
  have weightPos : 0 < weight := mul_pos nu.coeff_pos multiplierPos
  have coordinateBound :
      ∀ coordinate : Coordinate,
        2 * weight *
              ((left coordinate).re * (right coordinate).re +
                (left coordinate).im * (right coordinate).im) ≤
            weight ^ 2 * Complex.normSq (left coordinate) +
              Complex.normSq (right coordinate) := by
    intro coordinate
    rw [Complex.normSq_apply, Complex.normSq_apply]
    nlinarith
      [sq_nonneg
        (weight * (left coordinate).re - (right coordinate).re),
       sq_nonneg
        (weight * (left coordinate).im - (right coordinate).im)]
  have summed :=
    Finset.sum_le_sum fun coordinate
        (_ : coordinate ∈ (Finset.univ : Finset Coordinate)) =>
      coordinateBound coordinate
  have weighted :
      2 * weight * complexCoordinateRealInner left right ≤
        weight ^ 2 * complexCoordinateAmplitudeSq left +
          complexCoordinateAmplitudeSq right := by
    calc
      2 * weight * complexCoordinateRealInner left right =
          ∑ coordinate : Coordinate,
            2 * weight *
              ((left coordinate).re * (right coordinate).re +
                (left coordinate).im * (right coordinate).im) := by
        rw [complexCoordinateRealInner, Finset.mul_sum]
      _ ≤
          ∑ coordinate : Coordinate,
            (weight ^ 2 * Complex.normSq (left coordinate) +
              Complex.normSq (right coordinate)) := summed
      _ =
          weight ^ 2 * complexCoordinateAmplitudeSq left +
            complexCoordinateAmplitudeSq right := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        rfl
  have divided :
      2 * complexCoordinateRealInner left right ≤
        weight * complexCoordinateAmplitudeSq left +
          complexCoordinateAmplitudeSq right / weight := by
    calc
      2 * complexCoordinateRealInner left right ≤
          (weight ^ 2 * complexCoordinateAmplitudeSq left +
            complexCoordinateAmplitudeSq right) / weight := by
        apply (le_div_iff₀ weightPos).2
        calc
          2 * complexCoordinateRealInner left right * weight =
              2 * weight * complexCoordinateRealInner left right := by ring
          _ ≤ _ := weighted
      _ = weight * complexCoordinateAmplitudeSq left +
          complexCoordinateAmplitudeSq right / weight := by
        field_simp [weightPos.ne']
  have scaled := mul_le_mul_of_nonneg_left divided nu.coeff_pos.le
  calc
    2 * nu.coeff * complexCoordinateRealInner left right =
        nu.coeff * (2 * complexCoordinateRealInner left right) := by ring
    _ ≤ nu.coeff *
        (weight * complexCoordinateAmplitudeSq left +
          complexCoordinateAmplitudeSq right / weight) := scaled
    _ = nu.coeff ^ 2 * integerWaveViscousMultiplier wave *
          complexCoordinateAmplitudeSq left +
        (integerWaveViscousMultiplier wave)⁻¹ *
          complexCoordinateAmplitudeSq right := by
      dsimp only [weight]
      field_simp [nu.coeff_pos.ne', multiplierPos.ne']

private theorem subtype_viscousEuclideanDensity_tsum_eq_wholeGradient
    (state : ComplexVorticityHilbertState)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (state wave)) :
    (∑' wave : NonzeroIntegerWavevector,
      nu.coeff ^ 2 * integerWaveViscousMultiplier wave.1 *
        complexCoordinateAmplitudeSq (state wave.1)) =
      nu.coeff ^ 2 * (2 * Real.pi) ^ 2 *
        wholeStateVorticityGradientMass state := by
  let density := fun wave : IntegerWavevector =>
    integerWaveNormSq wave * complexCoordinateAmplitudeSq (state wave)
  have complementZero :
      (∑' wave :
          ↥({ wave : IntegerWavevector | wave ≠ 0 }ᶜ :
            Set IntegerWavevector),
        density wave.1) = 0 := by
    rw [show
        (fun wave :
          ↥({ wave : IntegerWavevector | wave ≠ 0 }ᶜ :
            Set IntegerWavevector) =>
          density wave.1) = 0 by
      funext wave
      have waveZero : wave.1 = 0 := by simpa using wave.2
      simp [density, waveZero, integerWaveNormSq]]
    exact tsum_zero
  have split :=
    gradientSummable.tsum_subtype_add_tsum_subtype_compl
      { wave : IntegerWavevector | wave ≠ 0 }
  have subtypeEq :
      (∑' wave : NonzeroIntegerWavevector, density wave.1) =
        ∑' wave : IntegerWavevector, density wave := by
    rw [← split, complementZero, add_zero]
  calc
    (∑' wave : NonzeroIntegerWavevector,
      nu.coeff ^ 2 * integerWaveViscousMultiplier wave.1 *
        complexCoordinateAmplitudeSq (state wave.1)) =
      nu.coeff ^ 2 * (2 * Real.pi) ^ 2 *
        ∑' wave : NonzeroIntegerWavevector, density wave.1 := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro wave
      unfold integerWaveViscousMultiplier density
      ring
    _ = nu.coeff ^ 2 * (2 * Real.pi) ^ 2 *
        ∑' wave : IntegerWavevector, density wave := by
      rw [subtypeEq]
    _ = nu.coeff ^ 2 * (2 * Real.pi) ^ 2 *
        wholeStateVorticityGradientMass state := by
      rfl

/-- The Euclidean viscous row is exactly the actual gradient density on
almost every time slice of the same receipt. -/
theorem receiptViscousNegativeOneEuclideanMass_ae_eq_gradient
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime) :
    ∀ᵐ time ∂(commonTimeMeasure requestedTime),
      ‖puncturedEuclideanSpaceTimeState
        (receiptViscousNegativeOneState receipt) time‖ ^ 2 =
      nu.coeff ^ 2 * (2 * Real.pi) ^ 2 *
        wholeStateVorticityGradientMass (receipt.wholePath time) := by
  have rowAE :
      ∀ᵐ time ∂(commonTimeMeasure requestedTime),
        ∀ wave : NonzeroIntegerWavevector,
          (receiptViscousNegativeOneState receipt time) wave.1 =
            (nu.coeff *
              Real.sqrt (integerWaveViscousMultiplier wave.1)) •
                receipt.wholePath time wave.1 := by
    exact eventually_countable_forall.2 fun wave =>
      receiptViscousNegativeOneState_row_ae receipt wave.1
  filter_upwards [
    puncturedEuclideanSpaceTimeState_apply_ae
      (receiptViscousNegativeOneState receipt),
    rowAE,
    receiptPointwiseGradient_ae_summable receipt,
    receiptStateLimit_eq_wholePath_ae receipt] with
      time mappedEq rowEq gradientSummable stateEq
  have pathGradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq
            (receipt.wholePath time wave) := by
    simpa only [stateEq] using gradientSummable
  rw [mappedEq, puncturedEuclideanize_norm_sq]
  calc
    (∑' wave : NonzeroIntegerWavevector,
      complexCoordinateAmplitudeSq
        ((receiptViscousNegativeOneState receipt time) wave.1)) =
      ∑' wave : NonzeroIntegerWavevector,
        nu.coeff ^ 2 * integerWaveViscousMultiplier wave.1 *
          complexCoordinateAmplitudeSq
            (receipt.wholePath time wave.1) := by
      apply tsum_congr
      intro wave
      have multiplierNonneg :
          0 ≤ integerWaveViscousMultiplier wave.1 := by
        unfold integerWaveViscousMultiplier
        exact mul_nonneg (sq_nonneg _)
          (integerWaveNormSq_nonneg wave.1)
      rw [rowEq wave, complexCoordinateAmplitudeSq_real_smul, mul_pow,
        Real.sq_sqrt multiplierNonneg]
    _ = nu.coeff ^ 2 * (2 * Real.pi) ^ 2 *
        wholeStateVorticityGradientMass (receipt.wholePath time) :=
      subtype_viscousEuclideanDensity_tsum_eq_wholeGradient
        (receipt.wholePath time) pathGradientSummable

/-- The full viscous Euclidean square is the exact time integral of the
same receipt's gradient density, with its original Fourier normalization. -/
theorem receiptViscousNegativeOneEuclideanSquare_eq_gradient
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime) :
    puncturedEuclideanSpaceTimeSquare
        (receiptViscousNegativeOneState receipt) =
      nu.coeff ^ 2 * (2 * Real.pi) ^ 2 *
        ∫ time,
          wholeStateVorticityGradientMass (receipt.wholePath time)
          ∂(commonTimeMeasure requestedTime) := by
  unfold puncturedEuclideanSpaceTimeSquare
  rw [puncturedEuclideanSpaceTimeState_norm_sq_eq_integral]
  calc
    (∫ time,
      ‖puncturedEuclideanSpaceTimeState
        (receiptViscousNegativeOneState receipt) time‖ ^ 2
      ∂(commonTimeMeasure requestedTime)) =
      ∫ time,
        nu.coeff ^ 2 * (2 * Real.pi) ^ 2 *
          wholeStateVorticityGradientMass (receipt.wholePath time)
        ∂(commonTimeMeasure requestedTime) :=
      integral_congr_ae
        (receiptViscousNegativeOneEuclideanMass_ae_eq_gradient receipt)
    _ = nu.coeff ^ 2 * (2 * Real.pi) ^ 2 *
        ∫ time,
          wholeStateVorticityGradientMass (receipt.wholePath time)
          ∂(commonTimeMeasure requestedTime) := by
      rw [integral_const_mul]

/-- The complete pair-aggregate action beyond twice a positive output radius
is paid by the same receipt's whole vorticity mass and gradient ledger. -/
theorem receiptPairAggregateNegativeOneHighOutputMass_le_agmon
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (time : Icc (0 : Real) requestedTime)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (receipt.wholePath time wave))
    (radius : Nat)
    (radiusPos : 0 < radius) :
    (∑' output :
        {output : IntegerWavevector //
          output ∉ integerWaveFrequencyCube (2 * radius)},
        actualWholeContinuousPairAggregateNegativeOneDensity
          receipt time output.1) ≤
      2184 * biotSavartSerrinConstant * (radius : Real)⁻¹ *
        wholeVorticityEuclideanMass (receipt.wholePath time) *
        wholeStateVorticityGradientMass (receipt.wholePath time) := by
  let high := fun output : IntegerWavevector =>
    output ∉ integerWaveFrequencyCube (2 * radius)
  let nonlinearDensity := fun output : IntegerWavevector =>
    wholeStateVorticityNonlinearNegativeOneDensity
      (receipt.wholePath time) output
  let pairDensity := fun output : IntegerWavevector =>
    actualWholeContinuousPairAggregateNegativeOneDensity
      receipt time output
  have nonlinearSummable : Summable nonlinearDensity := by
    simpa [nonlinearDensity] using
      summable_wholeStateVorticityNonlinearNegativeOneDensity
        (receipt.wholePath time) (wholePath_transverse receipt time)
        gradientSummable
  have pairSummable : Summable pairDensity := by
    simpa [pairDensity] using
      summable_actualWholeContinuousPairAggregateNegativeOneDensity
        receipt time gradientSummable
  have nonlinearHighSummable :
      Summable (fun output : {output // high output} =>
        nonlinearDensity output.1) :=
    nonlinearSummable.subtype high
  have pairHighSummable :
      Summable (fun output : {output // high output} =>
        pairDensity output.1) :=
    pairSummable.subtype high
  have nonlinearHighBound :
      (∑' output : {output // high output}, nonlinearDensity output.1) ≤
        728 * biotSavartSerrinConstant * (radius : Real)⁻¹ *
          wholeVorticityEuclideanMass (receipt.wholePath time) *
          wholeStateVorticityGradientMass (receipt.wholePath time) := by
    apply nonlinearHighSummable.tsum_le_of_sum_le
    intro finiteOutputs
    let outputs : Finset IntegerWavevector :=
      finiteOutputs.map ⟨Subtype.val, Subtype.val_injective⟩
    have outputsHigh :
        ∀ output ∈ outputs,
          output ∉ integerWaveFrequencyCube (2 * radius) := by
      intro output outputMem
      simp only [outputs, Finset.mem_map] at outputMem
      obtain ⟨source, sourceMem, rfl⟩ := outputMem
      exact source.2
    have finiteBound :=
      wholeStateVorticityNonlinearNegativeOneDensity_highOutputs_sum_le_agmon
        outputs (receipt.wholePath time)
        (wholePath_transverse receipt time) gradientSummable
        radius radiusPos outputsHigh
    simpa [outputs, nonlinearDensity] using finiteBound
  have pairLeNonlinear :
      (∑' output : {output // high output}, pairDensity output.1) ≤
        3 * ∑' output : {output // high output},
          nonlinearDensity output.1 := by
    calc
      (∑' output : {output // high output}, pairDensity output.1) ≤
          ∑' output : {output // high output},
            3 * nonlinearDensity output.1 := by
        exact Summable.tsum_le_tsum
          (fun output => by
            simpa [pairDensity, nonlinearDensity] using
              actualWholeContinuousPairAggregateNegativeOneDensity_le
                receipt time output.1)
          pairHighSummable (nonlinearHighSummable.mul_left 3)
      _ = 3 * ∑' output : {output // high output},
          nonlinearDensity output.1 := by
        rw [tsum_mul_left]
  change (∑' output : {output // high output}, pairDensity output.1) ≤ _
  calc
    (∑' output : {output // high output}, pairDensity output.1) ≤
        3 * ∑' output : {output // high output},
          nonlinearDensity output.1 := pairLeNonlinear
    _ ≤ 3 *
        (728 * biotSavartSerrinConstant * (radius : Real)⁻¹ *
          wholeVorticityEuclideanMass (receipt.wholePath time) *
          wholeStateVorticityGradientMass (receipt.wholePath time)) :=
      mul_le_mul_of_nonneg_left nonlinearHighBound (by norm_num)
    _ = 2184 * biotSavartSerrinConstant * (radius : Real)⁻¹ *
        wholeVorticityEuclideanMass (receipt.wholePath time) *
        wholeStateVorticityGradientMass (receipt.wholePath time) := by
      ring

/-- On a same-receipt mass-ceiling window, a sufficiently large finite
output cube leaves at most half of the complete viscous payment outside the
cube.  Thus the entire nonlinear Euclidean action is paid by that half plus
the action visible on the finite output cube. -/
theorem receiptNonlinearNegativeOneEuclideanSquare_le_halfViscous_add_lowOutput
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (ceiling : Real)
    (radius : Nat)
    (radiusPos : 0 < radius)
    (massBound :
      ∀ time : Icc (0 : Real) requestedTime,
        wholeVorticityEuclideanMass (receipt.wholePath time) ≤ ceiling)
    (radiusAbsorbs :
      4368 * biotSavartSerrinConstant * ceiling ≤
        (radius : Real) * (nu.coeff ^ 2 * (2 * Real.pi) ^ 2)) :
    puncturedEuclideanSpaceTimeSquare
        (receiptNonlinearNegativeOneState receipt) ≤
      (1 / 2 : Real) *
          puncturedEuclideanSpaceTimeSquare
            (receiptViscousNegativeOneState receipt) +
        ∫ time,
          ∑ output ∈ integerWaveFrequencyCube (2 * radius),
            actualWholeContinuousPairAggregateNegativeOneDensity
              receipt time output
          ∂(commonTimeMeasure requestedTime) := by
  let viscousConstant := nu.coeff ^ 2 * (2 * Real.pi) ^ 2
  let pairDensity := fun
      (time : Icc (0 : Real) requestedTime) (output : IntegerWavevector) =>
    actualWholeContinuousPairAggregateNegativeOneDensity
      receipt time output
  let fullMass := fun time : Icc (0 : Real) requestedTime =>
    ∑' output : IntegerWavevector, pairDensity time output
  let lowMass := fun time : Icc (0 : Real) requestedTime =>
    ∑ output ∈ integerWaveFrequencyCube (2 * radius),
      pairDensity time output
  let highMass := fun time : Icc (0 : Real) requestedTime =>
    ∑' output :
        {output : IntegerWavevector //
          output ∉ integerWaveFrequencyCube (2 * radius)},
      pairDensity time output.1
  let gradient := fun time : Icc (0 : Real) requestedTime =>
    wholeStateVorticityGradientMass (receipt.wholePath time)
  have viscousConstantPos : 0 < viscousConstant := by
    unfold viscousConstant
    exact mul_pos
      (sq_pos_of_pos nu.coeff_pos)
      (sq_pos_of_pos (mul_pos zero_lt_two Real.pi_pos))
  have radiusRealPos : 0 < (radius : Real) := by
    exact_mod_cast radiusPos
  have coefficientNonneg :
      0 ≤ 2184 * biotSavartSerrinConstant * (radius : Real)⁻¹ := by
    exact mul_nonneg
      (mul_nonneg (by norm_num) biotSavartSerrinConstant_nonneg)
      (inv_nonneg.mpr radiusRealPos.le)
  have coefficientLe :
      2184 * biotSavartSerrinConstant * (radius : Real)⁻¹ * ceiling ≤
        viscousConstant / 2 := by
    rw [show
      2184 * biotSavartSerrinConstant * (radius : Real)⁻¹ * ceiling =
        (2184 * biotSavartSerrinConstant * ceiling) / (radius : Real) by
          field_simp]
    rw [div_le_iff₀ radiusRealPos]
    change
      2184 * biotSavartSerrinConstant * ceiling ≤
        viscousConstant / 2 * (radius : Real)
    change
      4368 * biotSavartSerrinConstant * ceiling ≤
        (radius : Real) * viscousConstant at radiusAbsorbs
    nlinarith
  have fullIntegrable :
      Integrable fullMass (commonTimeMeasure requestedTime) := by
    simpa only [fullMass, pairDensity] using
      integrable_receiptPairAggregateNegativeOneMass receipt
  have pairDensityContinuous :
      ∀ output : IntegerWavevector,
        Continuous (fun time : Icc (0 : Real) requestedTime =>
          pairDensity time output) := by
    intro output
    have rowContinuous :
        Continuous (fun time : Icc (0 : Real) requestedTime =>
          actualWholeContinuousNonlinearRow receipt output time.1) :=
      (actualWholeContinuousNonlinearRow_continuous receipt output).comp
        continuous_subtype_val
    have sourceContinuous :
        Continuous (fun time : Icc (0 : Real) requestedTime =>
          (integerWaveViscousMultiplier output)⁻¹ *
            complexCoordinateAmplitudeSq
              (actualWholeContinuousNonlinearRow
                receipt output time.1)) :=
      continuous_const.mul
        (complexCoordinateAmplitudeSq_continuous.comp rowContinuous)
    apply sourceContinuous.congr
    intro time
    simp only [pairDensity]
    unfold actualWholeContinuousPairAggregateNegativeOneDensity
    rw [tsum_actualWholeContinuousPairVector_eq_continuousNonlinearRow]
  have lowContinuous : Continuous lowMass := by
    unfold lowMass
    exact continuous_finsetSum
      (integerWaveFrequencyCube (2 * radius))
      (fun output _ => pairDensityContinuous output)
  have lowIntegrable :
      Integrable lowMass (commonTimeMeasure requestedTime) := by
    simpa only [MeasureTheory.integrableOn_univ] using
      (ContinuousOn.integrableOn_compact isCompact_univ
        lowContinuous.continuousOn)
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
      Integrable (fun time => viscousConstant * gradient time)
        (commonTimeMeasure requestedTime) := by
    apply mappedViscousSquareIntegrable.congr
    filter_upwards [
      receiptViscousNegativeOneEuclideanMass_ae_eq_gradient receipt] with
        time pointEq
    simpa only [viscousConstant, gradient] using pointEq
  have halfGradientIntegrable :
      Integrable (fun time => (viscousConstant / 2) * gradient time)
        (commonTimeMeasure requestedTime) := by
    have scaled := weightedGradientIntegrable.const_mul (1 / 2 : Real)
    convert scaled using 1
    funext time
    ring
  have pointwiseAE :
      ∀ᵐ time ∂(commonTimeMeasure requestedTime),
        fullMass time ≤
          lowMass time + (viscousConstant / 2) * gradient time := by
    filter_upwards [
      receiptPointwiseGradient_ae_summable receipt,
      receiptStateLimit_eq_wholePath_ae receipt] with
        time gradientSummable stateEq
    have pathGradientSummable :
        Summable fun wave : IntegerWavevector =>
          integerWaveNormSq wave *
            complexCoordinateAmplitudeSq
              (receipt.wholePath time wave) := by
      simpa only [stateEq] using gradientSummable
    have pairSummable :
        Summable (pairDensity time) := by
      simpa only [pairDensity] using
        summable_actualWholeContinuousPairAggregateNegativeOneDensity
          receipt time pathGradientSummable
    have split :=
      pairSummable.tsum_subtype_add_tsum_subtype_compl
        {output : IntegerWavevector |
          output ∈ integerWaveFrequencyCube (2 * radius)}
    have lowSubtypeEq :
        (∑' output :
            {output : IntegerWavevector //
              output ∈
                (↑(integerWaveFrequencyCube (2 * radius)) :
                  Set IntegerWavevector)},
            pairDensity time output.1) = lowMass time := by
      rw [tsum_fintype]
      unfold lowMass
      symm
      exact Finset.sum_subtype
        (integerWaveFrequencyCube (2 * radius))
        (fun _ => Iff.rfl) (pairDensity time)
    have splitEq : fullMass time = lowMass time + highMass time := by
      unfold fullMass highMass
      calc
        (∑' output : IntegerWavevector, pairDensity time output) =
            (∑' output :
                {output : IntegerWavevector //
                  output ∈
                    (↑(integerWaveFrequencyCube (2 * radius)) :
                      Set IntegerWavevector)},
                pairDensity time output.1) +
              ∑' output :
                  {output : IntegerWavevector //
                    output ∈
                      (↑(integerWaveFrequencyCube (2 * radius)) :
                        Set IntegerWavevector)ᶜ},
                pairDensity time output.1 := split.symm
        _ = lowMass time + highMass time := by
          rw [lowSubtypeEq]
          congr 1
    have highBound :=
      receiptPairAggregateNegativeOneHighOutputMass_le_agmon
        receipt time pathGradientSummable radius radiusPos
    have gradientNonneg : 0 ≤ gradient time := by
      unfold gradient wholeStateVorticityGradientMass
      exact tsum_nonneg fun wave =>
        mul_nonneg (integerWaveNormSq_nonneg wave)
          (complexCoordinateAmplitudeSq_nonneg _)
    have highLeHalf :
        highMass time ≤ (viscousConstant / 2) * gradient time := by
      calc
        highMass time ≤
            2184 * biotSavartSerrinConstant * (radius : Real)⁻¹ *
              wholeVorticityEuclideanMass (receipt.wholePath time) *
              gradient time := by
          simpa only [highMass, pairDensity, gradient] using highBound
        _ ≤
            2184 * biotSavartSerrinConstant * (radius : Real)⁻¹ *
              ceiling * gradient time := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (massBound time)
              coefficientNonneg)
            gradientNonneg
        _ ≤ (viscousConstant / 2) * gradient time :=
          mul_le_mul_of_nonneg_right coefficientLe gradientNonneg
    rw [splitEq]
    exact add_le_add_right highLeHalf _
  have integralLe :
      (∫ time, fullMass time ∂(commonTimeMeasure requestedTime)) ≤
        ∫ time,
          lowMass time + (viscousConstant / 2) * gradient time
          ∂(commonTimeMeasure requestedTime) := by
    exact integral_mono_ae fullIntegrable
      (lowIntegrable.add halfGradientIntegrable) pointwiseAE
  have nonlinearSquareEq :
      puncturedEuclideanSpaceTimeSquare
          (receiptNonlinearNegativeOneState receipt) =
        ∫ time, fullMass time
          ∂(commonTimeMeasure requestedTime) := by
    unfold puncturedEuclideanSpaceTimeSquare
    rw [puncturedEuclideanSpaceTimeState_norm_sq_eq_integral]
    apply integral_congr_ae
    filter_upwards [
      puncturedEuclideanSpaceTimeState_apply_ae
        (receiptNonlinearNegativeOneState receipt),
      receiptNonlinearNegativeOneEuclideanMass_ae_eq_pairAggregate
        receipt] with time mappedEq pairEq
    rw [mappedEq, pairEq]
  rw [nonlinearSquareEq]
  calc
    (∫ time, fullMass time ∂(commonTimeMeasure requestedTime)) ≤
        ∫ time,
          lowMass time + (viscousConstant / 2) * gradient time
          ∂(commonTimeMeasure requestedTime) := integralLe
    _ = (∫ time, lowMass time ∂(commonTimeMeasure requestedTime)) +
        (viscousConstant / 2) *
          ∫ time, gradient time
            ∂(commonTimeMeasure requestedTime) := by
      rw [integral_add lowIntegrable halfGradientIntegrable,
        integral_const_mul]
    _ = (1 / 2 : Real) *
          puncturedEuclideanSpaceTimeSquare
            (receiptViscousNegativeOneState receipt) +
        ∫ time,
          ∑ output ∈ integerWaveFrequencyCube (2 * radius),
            actualWholeContinuousPairAggregateNegativeOneDensity
              receipt time output
          ∂(commonTimeMeasure requestedTime) := by
      rw [receiptViscousNegativeOneEuclideanSquare_eq_gradient receipt]
      unfold lowMass pairDensity viscousConstant gradient
      ring

/-- The exact same-receipt PDE balance consumes the high-output absorption:
every positive vorticity-mass increment is already visible in the finite
low-output pair action selected by that absorption radius. -/
theorem receiptVorticityMass_increment_le_lowOutputPayment
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (ceiling : Real)
    (radius : Nat)
    (radiusPos : 0 < radius)
    (massBound :
      ∀ time : Icc (0 : Real) requestedTime,
        wholeVorticityEuclideanMass (receipt.wholePath time) ≤ ceiling)
    (radiusAbsorbs :
      4368 * biotSavartSerrinConstant * ceiling ≤
        (radius : Real) * (nu.coeff ^ 2 * (2 * Real.pi) ^ 2)) :
    nu.coeff *
        (wholeVorticityEuclideanMass
            (receipt.wholePath
              ⟨requestedTime,
                ⟨receipt.requestedTimePos.le, le_rfl⟩⟩) -
          wholeVorticityEuclideanMass initialState) ≤
      ∫ time,
        ∑ output ∈ integerWaveFrequencyCube (2 * radius),
          actualWholeContinuousPairAggregateNegativeOneDensity
            receipt time output
        ∂(commonTimeMeasure requestedTime) := by
  have balance := receiptNonlinearNegativeOneEuclideanBalance receipt
  have absorption :=
    receiptNonlinearNegativeOneEuclideanSquare_le_halfViscous_add_lowOutput
      receipt ceiling radius radiusPos massBound radiusAbsorbs
  have tangentNonneg :
      0 ≤ puncturedEuclideanSpaceTimeSquare receipt.wholeTangent := by
    unfold puncturedEuclideanSpaceTimeSquare
    positivity
  have viscousNonneg :
      0 ≤ puncturedEuclideanSpaceTimeSquare
        (receiptViscousNegativeOneState receipt) := by
    unfold puncturedEuclideanSpaceTimeSquare
    positivity
  linarith

/-- The receipt itself selects the least convenient integer output scale (up
to one lattice unit) that absorbs its complete high-output action.  Besides
the resulting finite-output mass-increment payment, the witness retains the
linear-in-ceiling radius bound needed by parabolic rescaling consumers. -/
theorem receiptVorticityMass_increment_le_sourceSelectedLowOutputPayment
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (ceiling : Real)
    (ceilingNonneg : 0 ≤ ceiling)
    (massBound :
      ∀ time : Icc (0 : Real) requestedTime,
        wholeVorticityEuclideanMass (receipt.wholePath time) ≤ ceiling) :
    ∃ radius : Nat,
      0 < radius ∧
      4368 * biotSavartSerrinConstant * ceiling ≤
        (radius : Real) * (nu.coeff ^ 2 * (2 * Real.pi) ^ 2) ∧
      (radius : Real) ≤
        (4368 * biotSavartSerrinConstant * ceiling) /
            (nu.coeff ^ 2 * (2 * Real.pi) ^ 2) + 2 ∧
      nu.coeff *
          (wholeVorticityEuclideanMass
              (receipt.wholePath
                ⟨requestedTime,
                  ⟨receipt.requestedTimePos.le, le_rfl⟩⟩) -
            wholeVorticityEuclideanMass initialState) ≤
        ∫ time,
          ∑ output ∈ integerWaveFrequencyCube (2 * radius),
            actualWholeContinuousPairAggregateNegativeOneDensity
              receipt time output
          ∂(commonTimeMeasure requestedTime) := by
  let viscousConstant := nu.coeff ^ 2 * (2 * Real.pi) ^ 2
  let numerator := 4368 * biotSavartSerrinConstant * ceiling
  let ratio := numerator / viscousConstant
  let radius := Nat.ceil ratio + 1
  have viscousConstantPos : 0 < viscousConstant := by
    unfold viscousConstant
    exact mul_pos
      (sq_pos_of_pos nu.coeff_pos)
      (sq_pos_of_pos (mul_pos zero_lt_two Real.pi_pos))
  have numeratorNonneg : 0 ≤ numerator := by
    unfold numerator
    exact mul_nonneg
      (mul_nonneg (by norm_num) biotSavartSerrinConstant_nonneg)
      ceilingNonneg
  have ratioNonneg : 0 ≤ ratio := by
    exact div_nonneg numeratorNonneg viscousConstantPos.le
  have radiusPos : 0 < radius := by
    unfold radius
    omega
  have ratioLeRadius : ratio ≤ (radius : Real) := by
    calc
      ratio ≤ (Nat.ceil ratio : Real) := Nat.le_ceil ratio
      _ ≤ (radius : Real) := by
        have ceilLe : Nat.ceil ratio ≤ radius := by
          unfold radius
          omega
        exact_mod_cast ceilLe
  have radiusUpper : (radius : Real) ≤ ratio + 2 := by
    have ceilLt : (Nat.ceil ratio : Real) < ratio + 1 :=
      Nat.ceil_lt_add_one ratioNonneg
    unfold radius
    push_cast
    linarith
  have numeratorEq : numerator = ratio * viscousConstant := by
    unfold ratio
    field_simp [viscousConstantPos.ne']
  have radiusAbsorbs : numerator ≤ (radius : Real) * viscousConstant := by
    rw [numeratorEq]
    exact mul_le_mul_of_nonneg_right ratioLeRadius viscousConstantPos.le
  refine ⟨radius, radiusPos, ?_, ?_, ?_⟩
  · simpa only [numerator, viscousConstant] using radiusAbsorbs
  · simpa only [ratio, numerator, viscousConstant] using radiusUpper
  · exact receiptVorticityMass_increment_le_lowOutputPayment
      receipt ceiling radius radiusPos massBound
        (by simpa only [numerator, viscousConstant] using radiusAbsorbs)

private def wholeNonlinearEuclideanDensity
    (state : ComplexVorticityHilbertState)
    (output : IntegerWavevector) : Real :=
  (integerWaveViscousMultiplier output)⁻¹ *
    complexCoordinateAmplitudeSq
      (wholeStateVorticityNonlinearCoefficientAt state output)

private def wholeNonlinearEuclideanMass
    (state : ComplexVorticityHilbertState) : Real :=
  ∑' output : IntegerWavevector,
    wholeNonlinearEuclideanDensity state output

private theorem euclideanBalance_norm_add_sq_le_two_mul
    {E : Type*}
    [NormedAddCommGroup E]
    (left right : E) :
    ‖left + right‖ ^ 2 ≤ 2 * ‖left‖ ^ 2 + 2 * ‖right‖ ^ 2 := by
  have normLe : ‖left + right‖ ≤ ‖left‖ + ‖right‖ := norm_add_le _ _
  have squareLe :
      ‖left + right‖ ^ 2 ≤ (‖left‖ + ‖right‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _)
      (add_nonneg (norm_nonneg _) (norm_nonneg _))).2 normLe
  nlinarith [sq_nonneg (‖left‖ - ‖right‖)]

private theorem euclideanBalance_complexCoordinateAmplitudeSq_add_le_two_mul
    (left right : ComplexCoordinateVector) :
    complexCoordinateAmplitudeSq (left + right) ≤
      2 * complexCoordinateAmplitudeSq left +
        2 * complexCoordinateAmplitudeSq right := by
  unfold complexCoordinateAmplitudeSq
  calc
    (∑ coordinate : Coordinate,
        Complex.normSq ((left + right) coordinate)) ≤
        ∑ coordinate : Coordinate,
          (2 * Complex.normSq (left coordinate) +
            2 * Complex.normSq (right coordinate)) := by
      apply Finset.sum_le_sum
      intro coordinate _coordinateMem
      simpa only [Pi.add_apply, Complex.normSq_eq_norm_sq] using
        (euclideanBalance_norm_add_sq_le_two_mul
          (left coordinate) (right coordinate))
    _ =
        2 * (∑ coordinate : Coordinate,
          Complex.normSq (left coordinate)) +
        2 * (∑ coordinate : Coordinate,
          Complex.normSq (right coordinate)) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

private theorem summable_wholeNonlinearEuclideanDensity
    (state : ComplexVorticityHilbertState)
    (stateTransverse : WholeStateTransverse state)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (state wave)) :
    Summable (wholeNonlinearEuclideanDensity state) := by
  have normSummable :=
    summable_wholeStateVorticityNonlinearNegativeOneDensity
      state stateTransverse gradientSummable
  apply (normSummable.mul_left 3).of_nonneg_of_le
  · intro output
    exact mul_nonneg (inv_nonneg.mpr (by
      unfold integerWaveViscousMultiplier
      exact mul_nonneg (sq_nonneg _)
        (integerWaveNormSq_nonneg output)))
      (complexCoordinateAmplitudeSq_nonneg _)
  · intro output
    by_cases outputZero : output = 0
    · subst output
      simp [wholeNonlinearEuclideanDensity,
        wholeStateVorticityNonlinearNegativeOneDensity,
        integerWaveViscousMultiplier, integerWaveNormSq]
    · have amplitudeLe :=
        complexCoordinateAmplitudeSq_le_three_mul_norm_sq
          (wholeStateVorticityNonlinearCoefficientAt state output)
      have inverseNonneg :
          0 ≤ (integerWaveViscousMultiplier output)⁻¹ :=
        inv_nonneg.mpr (by
          unfold integerWaveViscousMultiplier
          exact mul_nonneg (sq_nonneg _)
            (integerWaveNormSq_nonneg output))
      unfold wholeNonlinearEuclideanDensity
        wholeStateVorticityNonlinearNegativeOneDensity
      rw [if_neg outputZero]
      rw [div_eq_mul_inv]
      nlinarith [mul_le_mul_of_nonneg_left amplitudeLe inverseNonneg]

private theorem wholeNonlinearEuclideanMass_le_projected_add_difference
    (state : ComplexVorticityHilbertState)
    (stateTransverse : WholeStateTransverse state)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (state wave))
    (radius : Nat) :
    wholeNonlinearEuclideanMass state ≤
      2 * wholeNonlinearEuclideanMass
          (complexSharpSupportProjection
            (integerWaveFrequencyCube radius) state) +
        6 * wholeStateVorticityNonlinearDifferenceNegativeOneMass
          (complexSharpSupportProjection
            (integerWaveFrequencyCube radius) state)
          state := by
  let modes := integerWaveFrequencyCube radius
  let projected := complexSharpSupportProjection modes state
  have projectedTransverse : WholeStateTransverse projected :=
    wholeStateTransverse_sharpSupportProjection
      modes state stateTransverse
  have projectedGradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (projected wave) :=
    summable_wholeStateVorticityGradientDensity_of_supported
      modes projected
      (complexSharpSupportProjection_supported modes state)
  have differenceGradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq ((projected - state) wave) :=
    summable_wholeStateVorticityGradientDensity_sub
      projected state projectedGradientSummable gradientSummable
  have fullSummable :=
    summable_wholeNonlinearEuclideanDensity
      state stateTransverse gradientSummable
  have projectedSummable :=
    summable_wholeNonlinearEuclideanDensity
      projected projectedTransverse projectedGradientSummable
  have differenceSummable :=
    summable_wholeStateVorticityNonlinearDifferenceNegativeOneDensity
      projected state projectedTransverse stateTransverse
      projectedGradientSummable gradientSummable
      differenceGradientSummable
  have pointwise (output : IntegerWavevector) :
      wholeNonlinearEuclideanDensity state output ≤
        2 * wholeNonlinearEuclideanDensity projected output +
          6 * wholeStateVorticityNonlinearDifferenceNegativeOneDensity
            projected state output := by
    by_cases outputZero : output = 0
    · subst output
      simp [wholeNonlinearEuclideanDensity,
        wholeStateVorticityNonlinearDifferenceNegativeOneDensity,
        integerWaveViscousMultiplier, integerWaveNormSq]
    · let fullRow := wholeStateVorticityNonlinearCoefficientAt state output
      let projectedRow :=
        wholeStateVorticityNonlinearCoefficientAt projected output
      have amplitudeLe :
          complexCoordinateAmplitudeSq fullRow ≤
            2 * complexCoordinateAmplitudeSq projectedRow +
              6 * ‖projectedRow - fullRow‖ ^ 2 := by
        calc
          complexCoordinateAmplitudeSq fullRow =
              complexCoordinateAmplitudeSq
                (projectedRow + (fullRow - projectedRow)) := by
            congr 1
            abel
          _ ≤ 2 * complexCoordinateAmplitudeSq projectedRow +
              2 * complexCoordinateAmplitudeSq (fullRow - projectedRow) :=
            euclideanBalance_complexCoordinateAmplitudeSq_add_le_two_mul _ _
          _ = 2 * complexCoordinateAmplitudeSq projectedRow +
              2 * complexCoordinateAmplitudeSq (projectedRow - fullRow) := by
            congr 1
            congr 1
            unfold complexCoordinateAmplitudeSq
            apply Finset.sum_congr rfl
            intro coordinate _coordinateMem
            change
              Complex.normSq
                  (fullRow coordinate - projectedRow coordinate) =
                Complex.normSq
                  (projectedRow coordinate - fullRow coordinate)
            rw [show
              fullRow coordinate - projectedRow coordinate =
                -(projectedRow coordinate - fullRow coordinate) by
              abel, Complex.normSq_neg]
          _ ≤ 2 * complexCoordinateAmplitudeSq projectedRow +
              6 * ‖projectedRow - fullRow‖ ^ 2 := by
            have differenceLe :=
              complexCoordinateAmplitudeSq_le_three_mul_norm_sq
                (projectedRow - fullRow)
            nlinarith
      have inverseNonneg :
          0 ≤ (integerWaveViscousMultiplier output)⁻¹ :=
        inv_nonneg.mpr (by
          unfold integerWaveViscousMultiplier
          exact mul_nonneg (sq_nonneg _)
            (integerWaveNormSq_nonneg output))
      have weighted :=
        mul_le_mul_of_nonneg_left amplitudeLe inverseNonneg
      unfold wholeNonlinearEuclideanDensity
        wholeStateVorticityNonlinearDifferenceNegativeOneDensity
      rw [if_neg outputZero]
      dsimp only [fullRow, projectedRow] at weighted
      rw [div_eq_mul_inv]
      nlinarith
  unfold wholeNonlinearEuclideanMass
  calc
    (∑' output : IntegerWavevector,
        wholeNonlinearEuclideanDensity state output) ≤
        ∑' output : IntegerWavevector,
          (2 * wholeNonlinearEuclideanDensity projected output +
            6 * wholeStateVorticityNonlinearDifferenceNegativeOneDensity
              projected state output) := by
      exact Summable.tsum_le_tsum pointwise fullSummable
        ((projectedSummable.mul_left 2).add
          (differenceSummable.mul_left 6))
    _ = 2 * (∑' output : IntegerWavevector,
          wholeNonlinearEuclideanDensity projected output) +
        6 * (∑' output : IntegerWavevector,
          wholeStateVorticityNonlinearDifferenceNegativeOneDensity
            projected state output) := by
      rw [Summable.tsum_add (projectedSummable.mul_left 2)
        (differenceSummable.mul_left 6), tsum_mul_left, tsum_mul_left]
    _ = 2 * (∑' output : IntegerWavevector,
          wholeNonlinearEuclideanDensity projected output) +
        6 * wholeStateVorticityNonlinearDifferenceNegativeOneMass
          projected state := by
      rfl

private theorem wholeNonlinearEuclideanMass_eq_finiteSupport
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState)
    (supported :
      ∀ wave : IntegerWavevector,
        wave ∉ modes → state wave = 0) :
    wholeNonlinearEuclideanMass state =
      ∑ output ∈ finiteVorticityPairOutputSupport modes,
        wholeNonlinearEuclideanDensity state output := by
  unfold wholeNonlinearEuclideanMass
  rw [tsum_eq_sum (s := finiteVorticityPairOutputSupport modes)]
  intro output outputOutside
  unfold wholeNonlinearEuclideanDensity
  rw [wholeStateVorticityNonlinearCoefficientAt_eq_zero_of_supported
    modes state supported output outputOutside]
  simp [complexCoordinateAmplitudeSq]

/-- On one actual receipt and one finite inventory, the source-generated
finite endpoint gain is paid by the autonomous nonlinear work of the sharp
input projection, up to the exact nonlinear projection error on that same
inventory.  The projected work tests `P_modes ω` against `N(P_modes ω)`, so
it is the finite-state physical work rather than a mixed whole-state readout.
The retained half-viscous debit is what lets a downstream source-selected
inventory absorb the projection error without losing the signed gain. -/
theorem
    viscosity_mul_actualWholeFiniteNetWork_le_finiteInputNonlinearWork_add_projectionError
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (modes : Finset IntegerWavevector) :
    nu.coeff * actualWholeFiniteNetWork receipt modes +
        (nu.coeff / 2) * actualWholeFiniteViscousPayment receipt modes ≤
      ∫ time,
        2 * nu.coeff *
            ∑ wave ∈ modes,
              complexCoordinateRealInner
                (complexSharpSupportProjection modes
                  (receipt.wholePath time) wave)
                (wholeStateVorticityNonlinearCoefficientAt
                  (complexSharpSupportProjection modes
                    (receipt.wholePath time)) wave) +
          ∑ wave ∈ modes,
            (integerWaveViscousMultiplier wave)⁻¹ *
              complexCoordinateAmplitudeSq
                (wholeStateVorticityNonlinearCoefficientAt
                    (receipt.wholePath time) wave -
                  wholeStateVorticityNonlinearCoefficientAt
                    (complexSharpSupportProjection modes
                      (receipt.wholePath time)) wave)
        ∂(commonTimeMeasure requestedTime) := by
  let projectedPath :
      Icc (0 : Real) requestedTime → ComplexVorticityHilbertState :=
    fun time =>
      complexSharpSupportProjection modes (receipt.wholePath time)
  let fullPower : Icc (0 : Real) requestedTime → Real := fun time =>
    ∑ wave ∈ modes,
      2 * nu.coeff * complexCoordinateRealInner
        (receipt.wholePath time wave)
        (wholeStateVorticityBilinearCoefficientAt
          (receipt.transverseLimit time).1
          (receipt.transverseLimit time).1 wave)
  let projectedPower : Icc (0 : Real) requestedTime → Real := fun time =>
    2 * nu.coeff *
      ∑ wave ∈ modes,
        complexCoordinateRealInner
          (projectedPath time wave)
          (wholeStateVorticityNonlinearCoefficientAt
            (projectedPath time) wave)
  let viscousHalfPower : Icc (0 : Real) requestedTime → Real := fun time =>
    (nu.coeff / 2) *
      ∑ wave ∈ modes, receiptRowViscousPower receipt wave time
  let errorPower : Icc (0 : Real) requestedTime → Real := fun time =>
    ∑ wave ∈ modes,
      (integerWaveViscousMultiplier wave)⁻¹ *
        complexCoordinateAmplitudeSq
          (wholeStateVorticityNonlinearCoefficientAt
              (receipt.wholePath time) wave -
            wholeStateVorticityNonlinearCoefficientAt
              (projectedPath time) wave)
  have projectedPathContinuous : Continuous projectedPath := by
    rw [show projectedPath =
        (sharpSupportProjectionCLM modes) ∘ receipt.wholePath by
      funext time
      exact (sharpSupportProjectionCLM_apply
        modes (receipt.wholePath time)).symm]
    exact (sharpSupportProjectionCLM modes).continuous.comp
      receipt.wholePath.continuous
  have projectedPathTransverse :
      ∀ time, WholeStateTransverse (projectedPath time) := by
    intro time
    exact wholeStateTransverse_sharpSupportProjection
      modes (receipt.wholePath time) (wholePath_transverse receipt time)
  let projectedTransversePath :
      Icc (0 : Real) requestedTime → WholeTransverseVorticityState :=
    fun time => ⟨projectedPath time, projectedPathTransverse time⟩
  have projectedTransversePathContinuous :
      Continuous projectedTransversePath :=
    projectedPathContinuous.subtype_mk projectedPathTransverse
  have projectedPowerContinuous : Continuous projectedPower := by
    unfold projectedPower
    apply continuous_const.mul
    apply continuous_finsetSum
    intro wave _waveMem
    have stateRowContinuous :
        Continuous (fun time => projectedPath time wave) :=
      (lp.evalCLM ℂ
        (fun _ : IntegerWavevector => ComplexCoordinateVector)
        2 wave).continuous.comp projectedPathContinuous
    have nonlinearRowContinuous :
        Continuous (fun time =>
          wholeStateVorticityNonlinearCoefficientAt
            (projectedPath time) wave) := by
      have rowContinuous :
          Continuous (fun time =>
            wholeStateVorticityNonlinearCoefficientAt
              (projectedTransversePath time).1 wave) :=
        (wholeStateVorticityNonlinearCoefficientAt_continuous wave).comp
          projectedTransversePathContinuous
      simpa only [projectedTransversePath] using rowContinuous
    exact complexCoordinateRealInner_prod_continuous.comp
      (stateRowContinuous.prodMk nonlinearRowContinuous)
  have projectedPowerIntegrable :
      Integrable projectedPower (commonTimeMeasure requestedTime) := by
    simpa only [MeasureTheory.integrableOn_univ] using
      (ContinuousOn.integrableOn_compact isCompact_univ
        projectedPowerContinuous.continuousOn)
  have errorPowerContinuous : Continuous errorPower := by
    unfold errorPower
    apply continuous_finsetSum
    intro wave _waveMem
    let wholeTransversePath :
        Icc (0 : Real) requestedTime → WholeTransverseVorticityState :=
      fun time => ⟨receipt.wholePath time, wholePath_transverse receipt time⟩
    have wholeTransversePathContinuous : Continuous wholeTransversePath :=
      receipt.wholePath.continuous.subtype_mk
        (wholePath_transverse receipt)
    have fullRowContinuous :
        Continuous (fun time =>
          wholeStateVorticityNonlinearCoefficientAt
            (receipt.wholePath time) wave) := by
      have rowContinuous :
          Continuous (fun time =>
            wholeStateVorticityNonlinearCoefficientAt
              (wholeTransversePath time).1 wave) :=
        (wholeStateVorticityNonlinearCoefficientAt_continuous wave).comp
          wholeTransversePathContinuous
      simpa only [wholeTransversePath] using rowContinuous
    have projectedRowContinuous :
        Continuous (fun time =>
          wholeStateVorticityNonlinearCoefficientAt
            (projectedPath time) wave) := by
      have rowContinuous :
          Continuous (fun time =>
            wholeStateVorticityNonlinearCoefficientAt
              (projectedTransversePath time).1 wave) :=
        (wholeStateVorticityNonlinearCoefficientAt_continuous wave).comp
          projectedTransversePathContinuous
      simpa only [projectedTransversePath] using rowContinuous
    exact continuous_const.mul
      (complexCoordinateAmplitudeSq_continuous.comp
        (fullRowContinuous.sub projectedRowContinuous))
  have errorPowerIntegrable :
      Integrable errorPower (commonTimeMeasure requestedTime) := by
    simpa only [MeasureTheory.integrableOn_univ] using
      (ContinuousOn.integrableOn_compact isCompact_univ
        errorPowerContinuous.continuousOn)
  have viscousHalfPowerIntegrable :
      Integrable viscousHalfPower (commonTimeMeasure requestedTime) := by
    unfold viscousHalfPower
    apply Integrable.const_mul
    apply integrable_finset_sum
    intro wave _waveMem
    exact receiptRowViscousPower_integrable receipt wave
  have fullPowerIntegrable :
      Integrable fullPower (commonTimeMeasure requestedTime) := by
    unfold fullPower
    apply integrable_finset_sum
    intro wave _waveMem
    by_cases waveZero : wave = 0
    · subst wave
      have zeroAE :
          (fun time : Icc (0 : Real) requestedTime =>
            2 * nu.coeff * complexCoordinateRealInner
              (receipt.wholePath time 0)
              (wholeStateVorticityBilinearCoefficientAt
                (receipt.transverseLimit time).1
                (receipt.transverseLimit time).1 0)) = 0 := by
        funext time
        rw [receipt.wholePath_zero_row]
        unfold complexCoordinateRealInner
        simp
      rw [zeroAE]
      exact integrable_zero
        (Icc (0 : Real) requestedTime) Real
        (commonTimeMeasure requestedTime)
    · let power : Icc (0 : Real) requestedTime → Real := fun time =>
        2 * complexCoordinateRealInner
          (receipt.wholePath time wave)
          (wholeStateVorticityBilinearCoefficientAt
            (receipt.transverseLimit time).1
            (receipt.transverseLimit time).1 wave)
      have densityIntegrable := receiptRowDualDensity_integrable receipt wave
      have pointwiseBound :=
        receiptWholeNonlinearPower_abs_ae_le receipt wave waveZero
      have powerIntegrable :
          Integrable power (commonTimeMeasure requestedTime) := by
        apply densityIntegrable.mono'
        · exact receiptWholeNonlinearPower_aestronglyMeasurable receipt wave
        · filter_upwards [pointwiseBound] with time bound
          rw [Real.norm_eq_abs]
          exact bound
      rw [show
        (fun time =>
          2 * nu.coeff * complexCoordinateRealInner
            (receipt.wholePath time wave)
            (wholeStateVorticityBilinearCoefficientAt
              (receipt.transverseLimit time).1
              (receipt.transverseLimit time).1 wave)) =
        (fun time => nu.coeff * power time) by
          funext time
          unfold power
          ring]
      exact powerIntegrable.const_mul nu.coeff
  have pointwiseAE :
      ∀ᵐ time ∂(commonTimeMeasure requestedTime),
        fullPower time ≤
          projectedPower time + viscousHalfPower time + errorPower time := by
    filter_upwards [receipt.wholePath_eq_transverse_ae] with time pathEq
    unfold fullPower projectedPower viscousHalfPower errorPower
    have each (wave : IntegerWavevector) (waveMem : wave ∈ modes) :
        2 * nu.coeff * complexCoordinateRealInner
            (receipt.wholePath time wave)
            (wholeStateVorticityBilinearCoefficientAt
              (receipt.transverseLimit time).1
              (receipt.transverseLimit time).1 wave) ≤
          2 * nu.coeff * complexCoordinateRealInner
            (projectedPath time wave)
            (wholeStateVorticityNonlinearCoefficientAt
              (projectedPath time) wave) +
            (nu.coeff / 2) * receiptRowViscousPower receipt wave time +
            (integerWaveViscousMultiplier wave)⁻¹ *
              complexCoordinateAmplitudeSq
                (wholeStateVorticityNonlinearCoefficientAt
                    (receipt.wholePath time) wave -
                  wholeStateVorticityNonlinearCoefficientAt
                    (projectedPath time) wave) := by
      by_cases waveZero : wave = 0
      · subst wave
        have projectedZero : projectedPath time 0 = 0 := by
          simp [projectedPath, complexSharpSupportProjection_apply,
            receipt.wholePath_zero_row]
        rw [receipt.wholePath_zero_row, projectedZero]
        unfold receiptRowViscousPower complexCoordinateRealInner
          integerWaveViscousMultiplier
        simp [complexCoordinateAmplitudeSq]
      · have pathNonlinearEq :
            wholeStateVorticityBilinearCoefficientAt
                (receipt.transverseLimit time).1
                (receipt.transverseLimit time).1 wave =
              wholeStateVorticityNonlinearCoefficientAt
                (receipt.wholePath time) wave := by
          rw [pathEq, wholeStateVorticityBilinearCoefficientAt_self]
        have projectionEq : projectedPath time wave =
            receipt.wholePath time wave := by
          simp [projectedPath, complexSharpSupportProjection_apply, waveMem]
        have errorBound :=
          two_mul_viscosity_complexCoordinateRealInner_le
            (nu := nu) wave waveZero (receipt.wholePath time wave)
              (wholeStateVorticityNonlinearCoefficientAt
                  (receipt.wholePath time) wave -
                wholeStateVorticityNonlinearCoefficientAt
                  (projectedPath time) wave)
        have errorBound' :
            2 * nu.coeff * complexCoordinateRealInner
                (receipt.wholePath time wave)
                (wholeStateVorticityNonlinearCoefficientAt
                    (receipt.wholePath time) wave -
                  wholeStateVorticityNonlinearCoefficientAt
                    (projectedPath time) wave) ≤
              (nu.coeff / 2) * receiptRowViscousPower receipt wave time +
                (integerWaveViscousMultiplier wave)⁻¹ *
                  complexCoordinateAmplitudeSq
                    (wholeStateVorticityNonlinearCoefficientAt
                        (receipt.wholePath time) wave -
                      wholeStateVorticityNonlinearCoefficientAt
                        (projectedPath time) wave) := by
          unfold receiptRowViscousPower
          nlinarith
        rw [pathNonlinearEq, projectionEq]
        calc
          2 * nu.coeff * complexCoordinateRealInner
              (receipt.wholePath time wave)
              (wholeStateVorticityNonlinearCoefficientAt
                (receipt.wholePath time) wave) =
            2 * nu.coeff * complexCoordinateRealInner
                (receipt.wholePath time wave)
                (wholeStateVorticityNonlinearCoefficientAt
                  (projectedPath time) wave) +
              2 * nu.coeff * complexCoordinateRealInner
                (receipt.wholePath time wave)
                (wholeStateVorticityNonlinearCoefficientAt
                    (receipt.wholePath time) wave -
                  wholeStateVorticityNonlinearCoefficientAt
                    (projectedPath time) wave) := by
            rw [show
              wholeStateVorticityNonlinearCoefficientAt
                  (receipt.wholePath time) wave =
                wholeStateVorticityNonlinearCoefficientAt
                    (projectedPath time) wave +
                  (wholeStateVorticityNonlinearCoefficientAt
                      (receipt.wholePath time) wave -
                    wholeStateVorticityNonlinearCoefficientAt
                      (projectedPath time) wave) by abel,
              complexCoordinateRealInner_add_right]
            ring
          _ ≤ _ := by
            linarith
    calc
      (∑ wave ∈ modes,
          2 * nu.coeff * complexCoordinateRealInner
            (receipt.wholePath time wave)
            (wholeStateVorticityBilinearCoefficientAt
              (receipt.transverseLimit time).1
              (receipt.transverseLimit time).1 wave)) ≤
          ∑ wave ∈ modes,
            (2 * nu.coeff * complexCoordinateRealInner
                (projectedPath time wave)
                (wholeStateVorticityNonlinearCoefficientAt
                  (projectedPath time) wave) +
              (nu.coeff / 2) * receiptRowViscousPower receipt wave time +
              (integerWaveViscousMultiplier wave)⁻¹ *
                complexCoordinateAmplitudeSq
                  (wholeStateVorticityNonlinearCoefficientAt
                      (receipt.wholePath time) wave -
                    wholeStateVorticityNonlinearCoefficientAt
                      (projectedPath time) wave)) := by
        exact Finset.sum_le_sum fun wave waveMem => each wave waveMem
      _ = 2 * nu.coeff *
              ∑ wave ∈ modes,
                complexCoordinateRealInner
                  (projectedPath time wave)
                  (wholeStateVorticityNonlinearCoefficientAt
                    (projectedPath time) wave) +
            (nu.coeff / 2) *
              ∑ wave ∈ modes, receiptRowViscousPower receipt wave time +
            ∑ wave ∈ modes,
              (integerWaveViscousMultiplier wave)⁻¹ *
                complexCoordinateAmplitudeSq
                  (wholeStateVorticityNonlinearCoefficientAt
                      (receipt.wholePath time) wave -
                    wholeStateVorticityNonlinearCoefficientAt
                      (projectedPath time) wave) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
          Finset.mul_sum, Finset.mul_sum]
  have integralLe :
      (∫ time, fullPower time ∂(commonTimeMeasure requestedTime)) ≤
        ∫ time,
          projectedPower time + viscousHalfPower time + errorPower time
          ∂(commonTimeMeasure requestedTime) := by
    exact integral_mono_ae fullPowerIntegrable
      ((projectedPowerIntegrable.add viscousHalfPowerIntegrable).add
        errorPowerIntegrable) pointwiseAE
  have fullIntegralEq :
      nu.coeff * actualWholeFiniteBilinearWork receipt modes =
        ∫ time, fullPower time ∂(commonTimeMeasure requestedTime) := by
    unfold actualWholeFiniteBilinearWork fullPower
    rw [Finset.mul_sum]
    calc
      (∑ wave ∈ modes,
          nu.coeff * actualWholeRowBilinearWork receipt wave) =
          ∑ wave ∈ modes,
            ∫ time,
              2 * nu.coeff * complexCoordinateRealInner
                (receipt.wholePath time wave)
                (wholeStateVorticityBilinearCoefficientAt
                  (receipt.transverseLimit time).1
                  (receipt.transverseLimit time).1 wave)
              ∂(commonTimeMeasure requestedTime) := by
        apply Finset.sum_congr rfl
        intro wave _waveMem
        by_cases waveZero : wave = 0
        · subst wave
          simp [actualWholeRowBilinearWork,
            receipt.wholePath_zero_row, complexCoordinateRealInner]
        · rw [actualWholeRowBilinearWork_eq_commonTimeIntegral
            receipt wave waveZero]
          rw [← integral_const_mul]
          congr 1
          funext time
          ring
      _ = ∫ time,
          ∑ wave ∈ modes,
            2 * nu.coeff * complexCoordinateRealInner
              (receipt.wholePath time wave)
              (wholeStateVorticityBilinearCoefficientAt
                (receipt.transverseLimit time).1
                (receipt.transverseLimit time).1 wave)
            ∂(commonTimeMeasure requestedTime) := by
        rw [integral_finset_sum]
        intro wave _waveMem
        by_cases waveZero : wave = 0
        · subst wave
          simp [receipt.wholePath_zero_row, complexCoordinateRealInner]
        · let power : Icc (0 : Real) requestedTime → Real := fun time =>
            2 * complexCoordinateRealInner
              (receipt.wholePath time wave)
              (wholeStateVorticityBilinearCoefficientAt
                (receipt.transverseLimit time).1
                (receipt.transverseLimit time).1 wave)
          have densityIntegrable := receiptRowDualDensity_integrable receipt wave
          have pointwiseBound :=
            receiptWholeNonlinearPower_abs_ae_le receipt wave waveZero
          have powerIntegrable :
              Integrable power (commonTimeMeasure requestedTime) := by
            apply densityIntegrable.mono'
            · exact receiptWholeNonlinearPower_aestronglyMeasurable receipt wave
            · filter_upwards [pointwiseBound] with time bound
              rw [Real.norm_eq_abs]
              exact bound
          rw [show
            (fun time =>
              2 * nu.coeff * complexCoordinateRealInner
                (receipt.wholePath time wave)
                (wholeStateVorticityBilinearCoefficientAt
                  (receipt.transverseLimit time).1
                  (receipt.transverseLimit time).1 wave)) =
            (fun time => nu.coeff * power time) by
              funext time
              unfold power
              ring]
          exact powerIntegrable.const_mul nu.coeff
  have viscousIntegralEq :
      (nu.coeff / 2) * actualWholeFiniteViscousPayment receipt modes =
        ∫ time, viscousHalfPower time
          ∂(commonTimeMeasure requestedTime) := by
    unfold actualWholeFiniteViscousPayment viscousHalfPower
    rw [integral_const_mul]
    congr 1
    calc
      (∑ wave ∈ modes, actualWholeRowViscousPayment receipt wave) =
          ∑ wave ∈ modes,
            ∫ time, receiptRowViscousPower receipt wave time
              ∂(commonTimeMeasure requestedTime) := by
        apply Finset.sum_congr rfl
        intro wave _waveMem
        rw [actualWholeRowViscousPayment_eq_commonTimeIntegral]
      _ = ∫ time,
          ∑ wave ∈ modes, receiptRowViscousPower receipt wave time
            ∂(commonTimeMeasure requestedTime) := by
        rw [integral_finset_sum]
        intro wave _waveMem
        exact receiptRowViscousPower_integrable receipt wave
  have ledger :=
    actualWholeFiniteNetWork_add_viscousPayment receipt modes
  rw [actualWholeFiniteNonlinearWork_eq_bilinearWork] at ledger
  have integralSplit :
      (∫ time,
          projectedPower time + viscousHalfPower time + errorPower time
          ∂(commonTimeMeasure requestedTime)) =
        (∫ time, projectedPower time
          ∂(commonTimeMeasure requestedTime)) +
          (∫ time, viscousHalfPower time
            ∂(commonTimeMeasure requestedTime)) +
          ∫ time, errorPower time
            ∂(commonTimeMeasure requestedTime) := by
    calc
      (∫ time,
          projectedPower time + viscousHalfPower time + errorPower time
          ∂(commonTimeMeasure requestedTime)) =
          (∫ time, (projectedPower + viscousHalfPower) time +
            errorPower time ∂(commonTimeMeasure requestedTime)) := by
            rfl
      _ = (∫ time, (projectedPower + viscousHalfPower) time
              ∂(commonTimeMeasure requestedTime)) +
            ∫ time, errorPower time
              ∂(commonTimeMeasure requestedTime) := by
        exact integral_add
          (projectedPowerIntegrable.add viscousHalfPowerIntegrable)
          errorPowerIntegrable
      _ = (∫ time, projectedPower time
              ∂(commonTimeMeasure requestedTime)) +
            (∫ time, viscousHalfPower time
              ∂(commonTimeMeasure requestedTime)) +
            ∫ time, errorPower time
              ∂(commonTimeMeasure requestedTime) := by
        simpa only [Pi.add_apply] using
          congrArg
            (fun value => value +
              ∫ time, errorPower time
                ∂(commonTimeMeasure requestedTime))
            (integral_add projectedPowerIntegrable
              viscousHalfPowerIntegrable)
  rw [← fullIntegralEq, integralSplit, ← viscousIntegralEq] at integralLe
  have viscousNonneg := actualWholeFiniteViscousPayment_nonneg receipt modes
  have viscosityViscousNonneg :
      0 ≤ nu.coeff * actualWholeFiniteViscousPayment receipt modes :=
    mul_nonneg nu.coeff_pos.le viscousNonneg
  have scaledLedger :
      nu.coeff * actualWholeFiniteNetWork receipt modes +
          nu.coeff * actualWholeFiniteViscousPayment receipt modes =
        nu.coeff * actualWholeFiniteBilinearWork receipt modes := by
    calc
      nu.coeff * actualWholeFiniteNetWork receipt modes +
          nu.coeff * actualWholeFiniteViscousPayment receipt modes =
          nu.coeff *
            (actualWholeFiniteNetWork receipt modes +
              actualWholeFiniteViscousPayment receipt modes) := by
        ring
      _ = nu.coeff * actualWholeFiniteBilinearWork receipt modes := by
        rw [ledger]
  have finalSeparated :
      nu.coeff * actualWholeFiniteNetWork receipt modes +
          (nu.coeff / 2) * actualWholeFiniteViscousPayment receipt modes ≤
        (∫ time, projectedPower time
          ∂(commonTimeMeasure requestedTime)) +
          ∫ time, errorPower time
            ∂(commonTimeMeasure requestedTime) := by
    nlinarith
  rw [← integral_add projectedPowerIntegrable errorPowerIntegrable]
    at finalSeparated
  simpa only [projectedPower, errorPower, projectedPath, Pi.add_apply] using
    finalSeparated

/-- A same-receipt mass ceiling selects a finite input projection whose
complete nonlinear output is still sufficient, together with the original
viscous debit, to pay the whole nonlinear Euclidean square. -/
theorem
    receiptNonlinearNegativeOneEuclideanSquare_le_viscous_add_two_finiteInputOutput
    {initialState : ComplexVorticityHilbertState}
    {requestedTime ceiling : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (radius : Nat)
    (radiusPos : 0 < radius)
    (massBound :
      ∀ᵐ time ∂(commonTimeMeasure requestedTime),
        wholeVorticityEuclideanMass (receipt.wholePath time) ≤ ceiling)
    (radiusAbsorbs :
      4368 * biotSavartSerrinConstant * ceiling ≤
        (radius : Real) * (nu.coeff ^ 2 * (2 * Real.pi) ^ 2)) :
    puncturedEuclideanSpaceTimeSquare
        (receiptNonlinearNegativeOneState receipt) ≤
      puncturedEuclideanSpaceTimeSquare
          (receiptViscousNegativeOneState receipt) +
        2 * ∫ time,
          ∑ output ∈
              finiteVorticityPairOutputSupport
                (integerWaveFrequencyCube radius),
            (integerWaveViscousMultiplier output)⁻¹ *
              complexCoordinateAmplitudeSq
                (wholeStateVorticityNonlinearCoefficientAt
                  (complexSharpSupportProjection
                    (integerWaveFrequencyCube radius)
                    (receipt.wholePath time))
                  output)
          ∂(commonTimeMeasure requestedTime) := by
  let modes := integerWaveFrequencyCube radius
  let projectedPath :
      Icc (0 : Real) requestedTime → ComplexVorticityHilbertState :=
    fun time => complexSharpSupportProjection modes (receipt.wholePath time)
  let fullMass : Icc (0 : Real) requestedTime → Real := fun time =>
    wholeNonlinearEuclideanMass (receipt.wholePath time)
  let projectedMass : Icc (0 : Real) requestedTime → Real := fun time =>
    ∑ output ∈ finiteVorticityPairOutputSupport modes,
      wholeNonlinearEuclideanDensity (projectedPath time) output
  let gradient : Icc (0 : Real) requestedTime → Real := fun time =>
    wholeStateVorticityGradientMass (receipt.wholePath time)
  let viscousConstant := nu.coeff ^ 2 * (2 * Real.pi) ^ 2
  have radiusRealPos : 0 < (radius : Real) := by
    exact_mod_cast radiusPos
  have coefficientNonneg :
      0 ≤ 4368 * biotSavartSerrinConstant * (radius : Real)⁻¹ := by
    exact mul_nonneg
      (mul_nonneg (by norm_num) biotSavartSerrinConstant_nonneg)
      (inv_nonneg.mpr radiusRealPos.le)
  have coefficientLe :
      4368 * biotSavartSerrinConstant * (radius : Real)⁻¹ * ceiling ≤
        viscousConstant := by
    rw [show
      4368 * biotSavartSerrinConstant * (radius : Real)⁻¹ * ceiling =
        (4368 * biotSavartSerrinConstant * ceiling) / (radius : Real) by
      field_simp]
    rw [div_le_iff₀ radiusRealPos]
    simpa only [viscousConstant, mul_comm] using radiusAbsorbs
  have projectedPathContinuous : Continuous projectedPath := by
    rw [show projectedPath =
        (sharpSupportProjectionCLM modes) ∘ receipt.wholePath by
      funext time
      exact (sharpSupportProjectionCLM_apply
        modes (receipt.wholePath time)).symm]
    exact (sharpSupportProjectionCLM modes).continuous.comp
      receipt.wholePath.continuous
  have projectedPathTransverse :
      ∀ time, WholeStateTransverse (projectedPath time) := by
    intro time
    exact wholeStateTransverse_sharpSupportProjection
      modes (receipt.wholePath time) (wholePath_transverse receipt time)
  let projectedTransversePath :
      Icc (0 : Real) requestedTime → WholeTransverseVorticityState :=
    fun time => ⟨projectedPath time, projectedPathTransverse time⟩
  have projectedTransversePathContinuous :
      Continuous projectedTransversePath :=
    projectedPathContinuous.subtype_mk projectedPathTransverse
  have projectedMassContinuous : Continuous projectedMass := by
    unfold projectedMass wholeNonlinearEuclideanDensity
    apply continuous_finsetSum
    intro output _outputMem
    have rowContinuous :
        Continuous (fun time =>
          wholeStateVorticityNonlinearCoefficientAt
            (projectedTransversePath time).1 output) :=
      (wholeStateVorticityNonlinearCoefficientAt_continuous output).comp
        projectedTransversePathContinuous
    have amplitudeContinuous :
        Continuous (fun time =>
          complexCoordinateAmplitudeSq
            (wholeStateVorticityNonlinearCoefficientAt
              (projectedTransversePath time).1 output)) :=
      complexCoordinateAmplitudeSq_continuous.comp rowContinuous
    exact continuous_const.mul amplitudeContinuous
  have projectedMassIntegrable :
      Integrable projectedMass (commonTimeMeasure requestedTime) := by
    simpa only [MeasureTheory.integrableOn_univ] using
      (ContinuousOn.integrableOn_compact isCompact_univ
        projectedMassContinuous.continuousOn)
  have fullMassEqPair (time : Icc (0 : Real) requestedTime) :
      fullMass time =
        ∑' output : IntegerWavevector,
          actualWholeContinuousPairAggregateNegativeOneDensity
            receipt time output := by
    unfold fullMass wholeNonlinearEuclideanMass
    apply tsum_congr
    intro output
    unfold wholeNonlinearEuclideanDensity
      actualWholeContinuousPairAggregateNegativeOneDensity
    rw [tsum_actualWholeContinuousPairVector_eq_nonlinearOutput]
  have fullMassIntegrable :
      Integrable fullMass (commonTimeMeasure requestedTime) := by
    exact (integrable_receiptPairAggregateNegativeOneMass receipt).congr
      (Filter.Eventually.of_forall fun time => (fullMassEqPair time).symm)
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
      Integrable (fun time => viscousConstant * gradient time)
        (commonTimeMeasure requestedTime) := by
    apply mappedViscousSquareIntegrable.congr
    filter_upwards [
      receiptViscousNegativeOneEuclideanMass_ae_eq_gradient receipt] with
        time pointEq
    simpa only [viscousConstant, gradient] using pointEq
  have pointwiseAE :
      ∀ᵐ time ∂(commonTimeMeasure requestedTime),
        fullMass time ≤
          2 * projectedMass time + viscousConstant * gradient time := by
    filter_upwards [
      receiptPointwiseGradient_ae_summable receipt,
      receiptStateLimit_eq_wholePath_ae receipt,
      massBound] with time gradientSummable stateEq pathMassLe
    have pathGradientSummable :
        Summable fun wave : IntegerWavevector =>
          integerWaveNormSq wave *
            complexCoordinateAmplitudeSq
              (receipt.wholePath time wave) := by
      simpa only [stateEq] using gradientSummable
    have comparison :=
      wholeNonlinearEuclideanMass_le_projected_add_difference
        (receipt.wholePath time) (wholePath_transverse receipt time)
        pathGradientSummable radius
    have differenceBound :=
      wholeStateVorticityNonlinearDifferenceNegativeOneMass_projection_le_agmon
        (receipt.wholePath time) (wholePath_transverse receipt time)
        pathGradientSummable radius radiusPos
    have gradientNonneg : 0 ≤ gradient time := by
      unfold gradient wholeStateVorticityGradientMass
      exact tsum_nonneg fun wave =>
        mul_nonneg (integerWaveNormSq_nonneg wave)
          (complexCoordinateAmplitudeSq_nonneg _)
    have differencePayment :
        6 *
            wholeStateVorticityNonlinearDifferenceNegativeOneMass
              (projectedPath time) (receipt.wholePath time) ≤
          viscousConstant * gradient time := by
      calc
        6 *
              wholeStateVorticityNonlinearDifferenceNegativeOneMass
                (projectedPath time) (receipt.wholePath time) ≤
            6 *
              (728 * biotSavartSerrinConstant * (radius : Real)⁻¹ *
                wholeVorticityEuclideanMass (receipt.wholePath time) *
                gradient time) := by
          simpa only [projectedPath, modes, gradient] using
            (mul_le_mul_of_nonneg_left differenceBound (by norm_num))
        _ =
            (4368 * biotSavartSerrinConstant * (radius : Real)⁻¹ *
              wholeVorticityEuclideanMass (receipt.wholePath time)) *
                gradient time := by ring
        _ ≤
            (4368 * biotSavartSerrinConstant * (radius : Real)⁻¹ *
              ceiling) * gradient time := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left pathMassLe coefficientNonneg)
            gradientNonneg
        _ ≤ viscousConstant * gradient time :=
          mul_le_mul_of_nonneg_right coefficientLe gradientNonneg
    have projectedEq :
        wholeNonlinearEuclideanMass (projectedPath time) =
          projectedMass time := by
      exact wholeNonlinearEuclideanMass_eq_finiteSupport
        modes (projectedPath time)
        (complexSharpSupportProjection_supported
          modes (receipt.wholePath time))
    have paid :
        2 * wholeNonlinearEuclideanMass (projectedPath time) +
              6 * wholeStateVorticityNonlinearDifferenceNegativeOneMass
                (projectedPath time) (receipt.wholePath time) ≤
            2 * wholeNonlinearEuclideanMass (projectedPath time) +
              viscousConstant * gradient time := by
      exact add_le_add_right differencePayment _
    have combined := comparison.trans (by
      simpa only [projectedPath, modes] using paid)
    rw [projectedEq] at combined
    simpa only [fullMass, projectedMass, gradient] using combined
  have integralLe :
      (∫ time, fullMass time ∂(commonTimeMeasure requestedTime)) ≤
        ∫ time,
          2 * projectedMass time + viscousConstant * gradient time
          ∂(commonTimeMeasure requestedTime) := by
    exact integral_mono_ae fullMassIntegrable
      ((projectedMassIntegrable.const_mul 2).add
        weightedGradientIntegrable) pointwiseAE
  have nonlinearSquareEq :
      puncturedEuclideanSpaceTimeSquare
          (receiptNonlinearNegativeOneState receipt) =
        ∫ time, fullMass time
          ∂(commonTimeMeasure requestedTime) := by
    unfold puncturedEuclideanSpaceTimeSquare
    rw [puncturedEuclideanSpaceTimeState_norm_sq_eq_integral]
    apply integral_congr_ae
    filter_upwards [
      puncturedEuclideanSpaceTimeState_apply_ae
        (receiptNonlinearNegativeOneState receipt),
      receiptNonlinearNegativeOneEuclideanMass_ae_eq_pairAggregate
        receipt] with time mappedEq pairEq
    rw [mappedEq, pairEq, ← fullMassEqPair]
  rw [nonlinearSquareEq]
  calc
    (∫ time, fullMass time ∂(commonTimeMeasure requestedTime)) ≤
        ∫ time,
          2 * projectedMass time + viscousConstant * gradient time
          ∂(commonTimeMeasure requestedTime) := integralLe
    _ = 2 * ∫ time, projectedMass time
          ∂(commonTimeMeasure requestedTime) +
        viscousConstant * ∫ time, gradient time
          ∂(commonTimeMeasure requestedTime) := by
      rw [integral_add (projectedMassIntegrable.const_mul 2)
        weightedGradientIntegrable, integral_const_mul,
        integral_const_mul]
    _ = puncturedEuclideanSpaceTimeSquare
          (receiptViscousNegativeOneState receipt) +
        2 * ∫ time, projectedMass time
          ∂(commonTimeMeasure requestedTime) := by
      rw [receiptViscousNegativeOneEuclideanSquare_eq_gradient receipt]
      unfold viscousConstant gradient
      ring
    _ = puncturedEuclideanSpaceTimeSquare
          (receiptViscousNegativeOneState receipt) +
        2 * ∫ time,
          ∑ output ∈
              finiteVorticityPairOutputSupport
                (integerWaveFrequencyCube radius),
            (integerWaveViscousMultiplier output)⁻¹ *
              complexCoordinateAmplitudeSq
                (wholeStateVorticityNonlinearCoefficientAt
                  (complexSharpSupportProjection
                    (integerWaveFrequencyCube radius)
                    (receipt.wholePath time))
                  output)
          ∂(commonTimeMeasure requestedTime) := by
      rfl


private theorem receiptPairAggregateNegativeOneMass_sq_le_scaleCritical
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (time : Icc (0 : Real) requestedTime)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (receipt.wholePath time wave)) :
    (∑' output : IntegerWavevector,
      actualWholeContinuousPairAggregateNegativeOneDensity
        receipt time output) ^ 2 ≤
      (9 * 1557504 * biotSavartSerrinConstant ^ 2) *
        wholeVorticityEuclideanMass (receipt.wholePath time) ^ 3 *
        wholeStateVorticityGradientMass (receipt.wholePath time) := by
  let pairMass :=
    ∑' output : IntegerWavevector,
      actualWholeContinuousPairAggregateNegativeOneDensity
        receipt time output
  let nonlinearMass :=
    wholeStateVorticityNonlinearNegativeOneMass
      (receipt.wholePath time)
  have nonlinearSummable :=
    summable_wholeStateVorticityNonlinearNegativeOneDensity
      (receipt.wholePath time) (wholePath_transverse receipt time)
      gradientSummable
  have pairSummable :=
    summable_actualWholeContinuousPairAggregateNegativeOneDensity
      receipt time gradientSummable
  have pairNonneg : 0 ≤ pairMass := by
    unfold pairMass
    exact tsum_nonneg fun output =>
      actualWholeContinuousPairAggregateNegativeOneDensity_nonneg
        receipt time output
  have nonlinearNonneg : 0 ≤ nonlinearMass := by
    unfold nonlinearMass wholeStateVorticityNonlinearNegativeOneMass
    exact tsum_nonneg fun output =>
      wholeStateVorticityNonlinearNegativeOneDensity_nonneg
        (receipt.wholePath time) output
  have pairLe : pairMass ≤ 3 * nonlinearMass := by
    unfold pairMass nonlinearMass
      wholeStateVorticityNonlinearNegativeOneMass
    calc
      (∑' output : IntegerWavevector,
        actualWholeContinuousPairAggregateNegativeOneDensity
          receipt time output) ≤
          ∑' output : IntegerWavevector,
            3 * wholeStateVorticityNonlinearNegativeOneDensity
              (receipt.wholePath time) output :=
        Summable.tsum_le_tsum
          (actualWholeContinuousPairAggregateNegativeOneDensity_le
            receipt time)
          pairSummable
          (nonlinearSummable.mul_left 3)
      _ = 3 * ∑' output : IntegerWavevector,
          wholeStateVorticityNonlinearNegativeOneDensity
            (receipt.wholePath time) output := by
        rw [tsum_mul_left]
  have pairSq : pairMass ^ 2 ≤ 9 * nonlinearMass ^ 2 := by
    calc
      pairMass ^ 2 ≤ (3 * nonlinearMass) ^ 2 :=
        (sq_le_sq₀ pairNonneg
          (mul_nonneg (by norm_num) nonlinearNonneg)).2 pairLe
      _ = 9 * nonlinearMass ^ 2 := by ring
  have nonlinearSq :=
    wholeStateVorticityNonlinearNegativeOneMass_sq_le_scaleCritical
      (receipt.wholePath time)
      (wholePath_transverse receipt time)
      gradientSummable
  change pairMass ^ 2 ≤ _
  calc
    pairMass ^ 2 ≤ 9 * nonlinearMass ^ 2 := pairSq
    _ ≤ 9 *
        (1557504 * biotSavartSerrinConstant ^ 2 *
          wholeVorticityEuclideanMass (receipt.wholePath time) ^ 3 *
          wholeStateVorticityGradientMass (receipt.wholePath time)) :=
      mul_le_mul_of_nonneg_left nonlinearSq (by norm_num)
    _ = (9 * 1557504 * biotSavartSerrinConstant ^ 2) *
        wholeVorticityEuclideanMass (receipt.wholePath time) ^ 3 *
        wholeStateVorticityGradientMass (receipt.wholePath time) := by
      ring

/-- Scale-critical Young absorption on one actual time slice.  Half of the
same receipt's viscous density pays the whole nonlinear Euclidean row; the
only remainder is cubic in that receipt's vorticity mass. -/
theorem receiptPairAggregateNegativeOneMass_le_halfViscous_add_cubic
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (time : Icc (0 : Real) requestedTime)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (receipt.wholePath time wave)) :
    (∑' output : IntegerWavevector,
      actualWholeContinuousPairAggregateNegativeOneDensity
        receipt time output) ≤
      (nu.coeff ^ 2 * (2 * Real.pi) ^ 2 / 2) *
          wholeStateVorticityGradientMass (receipt.wholePath time) +
        ((9 * 1557504 * biotSavartSerrinConstant ^ 2) /
            (2 * (nu.coeff ^ 2 * (2 * Real.pi) ^ 2))) *
          wholeVorticityEuclideanMass (receipt.wholePath time) ^ 3 := by
  let pairMass :=
    ∑' output : IntegerWavevector,
      actualWholeContinuousPairAggregateNegativeOneDensity
        receipt time output
  let mass := wholeVorticityEuclideanMass (receipt.wholePath time)
  let gradient := wholeStateVorticityGradientMass (receipt.wholePath time)
  let scaleConstant := 9 * 1557504 * biotSavartSerrinConstant ^ 2
  let viscousConstant := nu.coeff ^ 2 * (2 * Real.pi) ^ 2
  let cubicConstant := scaleConstant / (2 * viscousConstant)
  have pairNonneg : 0 ≤ pairMass := by
    unfold pairMass
    exact tsum_nonneg fun output =>
      actualWholeContinuousPairAggregateNegativeOneDensity_nonneg
        receipt time output
  have massNonneg : 0 ≤ mass := by
    unfold mass wholeVorticityEuclideanMass
    exact tsum_nonneg fun wave => sq_nonneg _
  have gradientNonneg : 0 ≤ gradient := by
    unfold gradient wholeStateVorticityGradientMass
    exact tsum_nonneg fun wave =>
      mul_nonneg (integerWaveNormSq_nonneg wave)
        (complexCoordinateAmplitudeSq_nonneg _)
  have viscousConstantPos : 0 < viscousConstant := by
    unfold viscousConstant
    exact mul_pos
      (sq_pos_of_pos nu.coeff_pos)
      (sq_pos_of_pos (mul_pos zero_lt_two Real.pi_pos))
  have scaleConstantNonneg : 0 ≤ scaleConstant := by
    unfold scaleConstant
    positivity
  have cubicConstantNonneg : 0 ≤ cubicConstant := by
    unfold cubicConstant
    positivity
  have squareBound :
      pairMass ^ 2 ≤ scaleConstant * mass ^ 3 * gradient := by
    simpa [pairMass, mass, gradient, scaleConstant] using
      receiptPairAggregateNegativeOneMass_sq_le_scaleCritical
        receipt time gradientSummable
  have factor :
      2 * viscousConstant * cubicConstant = scaleConstant := by
    unfold cubicConstant
    field_simp [viscousConstantPos.ne']
  have rightNonneg :
      0 ≤ (viscousConstant / 2) * gradient +
        cubicConstant * mass ^ 3 :=
    add_nonneg
      (mul_nonneg
        (div_nonneg viscousConstantPos.le (by norm_num)) gradientNonneg)
      (mul_nonneg cubicConstantNonneg (by positivity))
  have scaleLe :
      scaleConstant * mass ^ 3 * gradient ≤
        ((viscousConstant / 2) * gradient +
          cubicConstant * mass ^ 3) ^ 2 := by
    rw [← factor]
    nlinarith [sq_nonneg
      ((viscousConstant / 2) * gradient - cubicConstant * mass ^ 3)]
  change pairMass ≤
    (viscousConstant / 2) * gradient + cubicConstant * mass ^ 3
  exact (sq_le_sq₀ pairNonneg rightNonneg).1
    (squareBound.trans scaleLe)

/-- Integrated scale-critical absorption on one actual receipt.  This is a
direct consumer of its exact PDE write and viscous ledger. -/
theorem receiptNonlinearNegativeOneEuclideanSquare_le_halfViscous_add_cubic
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime) :
    puncturedEuclideanSpaceTimeSquare
        (receiptNonlinearNegativeOneState receipt) ≤
      (1 / 2 : Real) *
          puncturedEuclideanSpaceTimeSquare
            (receiptViscousNegativeOneState receipt) +
        ((9 * 1557504 * biotSavartSerrinConstant ^ 2) /
            (2 * (nu.coeff ^ 2 * (2 * Real.pi) ^ 2))) *
          ∫ time,
            wholeVorticityEuclideanMass (receipt.wholePath time) ^ 3
            ∂(commonTimeMeasure requestedTime) := by
  let viscousConstant := nu.coeff ^ 2 * (2 * Real.pi) ^ 2
  let cubicConstant :=
    (9 * 1557504 * biotSavartSerrinConstant ^ 2) /
      (2 * viscousConstant)
  let pairMass := fun time =>
    ∑' output : IntegerWavevector,
      actualWholeContinuousPairAggregateNegativeOneDensity
        receipt time output
  let mass := fun time =>
    wholeVorticityEuclideanMass (receipt.wholePath time)
  let gradient := fun time =>
    wholeStateVorticityGradientMass (receipt.wholePath time)
  have pairIntegrable :
      Integrable pairMass (commonTimeMeasure requestedTime) := by
    simpa only [pairMass] using
      integrable_receiptPairAggregateNegativeOneMass receipt
  have massCubeContinuous : Continuous (fun time => mass time ^ 3) :=
    (wholeReceiptVorticityMass_continuous receipt).pow 3
  have massCubeIntegrable :
      Integrable (fun time => mass time ^ 3)
        (commonTimeMeasure requestedTime) := by
    simpa only [MeasureTheory.integrableOn_univ] using
      (ContinuousOn.integrableOn_compact isCompact_univ
        massCubeContinuous.continuousOn)
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
      Integrable (fun time => viscousConstant * gradient time)
        (commonTimeMeasure requestedTime) := by
    apply mappedViscousSquareIntegrable.congr
    filter_upwards [
      receiptViscousNegativeOneEuclideanMass_ae_eq_gradient receipt] with
        time pointEq
    simpa only [viscousConstant, gradient] using pointEq
  have halfGradientIntegrable :
      Integrable (fun time => (viscousConstant / 2) * gradient time)
        (commonTimeMeasure requestedTime) := by
    have scaled := weightedGradientIntegrable.const_mul (1 / 2 : Real)
    convert scaled using 1
    funext time
    ring
  have cubicIntegrable :
      Integrable (fun time => cubicConstant * mass time ^ 3)
        (commonTimeMeasure requestedTime) :=
    massCubeIntegrable.const_mul cubicConstant
  have pointwiseAE :
      ∀ᵐ time ∂(commonTimeMeasure requestedTime),
        pairMass time ≤
          (viscousConstant / 2) * gradient time +
            cubicConstant * mass time ^ 3 := by
    filter_upwards [
      receiptPointwiseGradient_ae_summable receipt,
      receiptStateLimit_eq_wholePath_ae receipt] with
        time gradientSummable stateEq
    have pathGradientSummable :
        Summable fun wave : IntegerWavevector =>
          integerWaveNormSq wave *
            complexCoordinateAmplitudeSq
              (receipt.wholePath time wave) := by
      simpa only [stateEq] using gradientSummable
    simpa only [pairMass, viscousConstant, gradient,
      cubicConstant, mass] using
        receiptPairAggregateNegativeOneMass_le_halfViscous_add_cubic
          receipt time pathGradientSummable
  have integralLe :
      (∫ time, pairMass time ∂(commonTimeMeasure requestedTime)) ≤
        ∫ time,
          (viscousConstant / 2) * gradient time +
            cubicConstant * mass time ^ 3
          ∂(commonTimeMeasure requestedTime) := by
    apply integral_mono_ae pairIntegrable
      (halfGradientIntegrable.add cubicIntegrable)
    filter_upwards [pointwiseAE] with time pointLe
    change pairMass time ≤
      (viscousConstant / 2) * gradient time +
        cubicConstant * mass time ^ 3
    change pairMass time ≤
      (viscousConstant / 2) * gradient time +
        cubicConstant * mass time ^ 3 at pointLe
    exact pointLe
  have nonlinearSquareEq :
      puncturedEuclideanSpaceTimeSquare
          (receiptNonlinearNegativeOneState receipt) =
        ∫ time, pairMass time
          ∂(commonTimeMeasure requestedTime) := by
    unfold puncturedEuclideanSpaceTimeSquare
    rw [puncturedEuclideanSpaceTimeState_norm_sq_eq_integral]
    apply integral_congr_ae
    filter_upwards [
      puncturedEuclideanSpaceTimeState_apply_ae
        (receiptNonlinearNegativeOneState receipt),
      receiptNonlinearNegativeOneEuclideanMass_ae_eq_pairAggregate
        receipt] with time mappedEq pairEq
    rw [mappedEq, pairEq]
  rw [nonlinearSquareEq]
  calc
    (∫ time, pairMass time ∂(commonTimeMeasure requestedTime)) ≤
        ∫ time,
          (viscousConstant / 2) * gradient time +
            cubicConstant * mass time ^ 3
          ∂(commonTimeMeasure requestedTime) :=
      integralLe
    _ = (viscousConstant / 2) *
          ∫ time, gradient time ∂(commonTimeMeasure requestedTime) +
        cubicConstant *
          ∫ time, mass time ^ 3
            ∂(commonTimeMeasure requestedTime) := by
      rw [integral_add halfGradientIntegrable cubicIntegrable,
        integral_const_mul, integral_const_mul]
    _ = (1 / 2 : Real) *
          puncturedEuclideanSpaceTimeSquare
            (receiptViscousNegativeOneState receipt) +
        cubicConstant *
          ∫ time, mass time ^ 3
            ∂(commonTimeMeasure requestedTime) := by
      rw [receiptViscousNegativeOneEuclideanSquare_eq_gradient receipt]
      ring
    _ = (1 / 2 : Real) *
          puncturedEuclideanSpaceTimeSquare
            (receiptViscousNegativeOneState receipt) +
        ((9 * 1557504 * biotSavartSerrinConstant ^ 2) /
            (2 * (nu.coeff ^ 2 * (2 * Real.pi) ^ 2))) *
          ∫ time,
            wholeVorticityEuclideanMass (receipt.wholePath time) ^ 3
            ∂(commonTimeMeasure requestedTime) := by
      rfl

private theorem euclideanBalance_commonTimeMeasure_univ_real
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

/-- The exact whole NS balance keeps the endpoint vorticity increment as a
signed boundary row while cubic absorption bounds the complete remaining
negative-one tangent/viscous action on the same receipt. -/
theorem receipt_tangentHalfViscousSquare_add_boundary_le_cubicTime
    {initialState : ComplexVorticityHilbertState}
    {requestedTime ceiling : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (massBound :
      ∀ᵐ time ∂(commonTimeMeasure requestedTime),
        wholeVorticityEuclideanMass (receipt.wholePath time) ≤ ceiling) :
    puncturedEuclideanSpaceTimeSquare receipt.wholeTangent +
        (1 / 2 : Real) *
          puncturedEuclideanSpaceTimeSquare
            (receiptViscousNegativeOneState receipt) +
        nu.coeff *
          (wholeVorticityEuclideanMass
              (receipt.wholePath
                ⟨requestedTime,
                  ⟨receipt.requestedTimePos.le, le_rfl⟩⟩) -
            wholeVorticityEuclideanMass initialState) ≤
      ((9 * 1557504 * biotSavartSerrinConstant ^ 2) /
          (2 * (nu.coeff ^ 2 * (2 * Real.pi) ^ 2))) *
        (ceiling ^ 3 * requestedTime) := by
  let cubicConstant : Real :=
    (9 * 1557504 * biotSavartSerrinConstant ^ 2) /
      (2 * (nu.coeff ^ 2 * (2 * Real.pi) ^ 2))
  let mass : Icc (0 : Real) requestedTime → Real := fun time =>
    wholeVorticityEuclideanMass (receipt.wholePath time)
  have balance := receiptNonlinearNegativeOneEuclideanBalance receipt
  have absorption :=
    receiptNonlinearNegativeOneEuclideanSquare_le_halfViscous_add_cubic
      receipt
  have signedSquareLe :
      puncturedEuclideanSpaceTimeSquare receipt.wholeTangent +
          (1 / 2 : Real) *
            puncturedEuclideanSpaceTimeSquare
              (receiptViscousNegativeOneState receipt) +
          nu.coeff *
            (wholeVorticityEuclideanMass
                (receipt.wholePath
                  ⟨requestedTime,
                    ⟨receipt.requestedTimePos.le, le_rfl⟩⟩) -
              wholeVorticityEuclideanMass initialState) ≤
        cubicConstant *
          ∫ time, mass time ^ 3
            ∂(commonTimeMeasure requestedTime) := by
    dsimp only [cubicConstant, mass]
    linarith
  have massCubeContinuous : Continuous (fun time => mass time ^ 3) :=
    (wholeReceiptVorticityMass_continuous receipt).pow 3
  have massCubeIntegrable :
      Integrable (fun time => mass time ^ 3)
        (commonTimeMeasure requestedTime) := by
    simpa only [MeasureTheory.integrableOn_univ] using
      (ContinuousOn.integrableOn_compact isCompact_univ
        massCubeContinuous.continuousOn)
  have constantIntegrable :
      Integrable (fun _ : Icc (0 : Real) requestedTime => ceiling ^ 3)
        (commonTimeMeasure requestedTime) := integrable_const _
  have massCubeLe : ∀ᵐ time ∂(commonTimeMeasure requestedTime),
      mass time ^ 3 ≤ ceiling ^ 3 := by
    filter_upwards [massBound] with time timeMassBound
    exact pow_le_pow_left₀
      (by
        unfold wholeVorticityEuclideanMass
        exact tsum_nonneg fun wave => sq_nonneg _)
      timeMassBound 3
  have massIntegralLe :
      (∫ time, mass time ^ 3
          ∂(commonTimeMeasure requestedTime)) ≤
        ceiling ^ 3 * requestedTime := by
    calc
      (∫ time, mass time ^ 3
          ∂(commonTimeMeasure requestedTime)) ≤
          ∫ _time : Icc (0 : Real) requestedTime,
            ceiling ^ 3
            ∂(commonTimeMeasure requestedTime) := by
        exact integral_mono_ae
          massCubeIntegrable constantIntegrable massCubeLe
      _ = ceiling ^ 3 * requestedTime := by
        rw [integral_const, euclideanBalance_commonTimeMeasure_univ_real
          requestedTime receipt.requestedTimePos.le]
        simp only [smul_eq_mul]
        ring
  exact signedSquareLe.trans <|
    mul_le_mul_of_nonneg_left massIntegralLe (by
      dsimp only [cubicConstant]
      positivity)

/-- The exact whole NS balance and cubic absorption bound the complete
negative-one tangent/viscous action on the same receipt whenever its endpoint
vorticity mass does not decrease and the path stays below one almost-everywhere
mass ceiling. -/
theorem receipt_tangentHalfViscousSquare_le_cubicTime
    {initialState : ComplexVorticityHilbertState}
    {requestedTime ceiling : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (massBound :
      ∀ᵐ time ∂(commonTimeMeasure requestedTime),
        wholeVorticityEuclideanMass (receipt.wholePath time) ≤ ceiling)
    (massNondecreasing :
      wholeVorticityEuclideanMass initialState ≤
        wholeVorticityEuclideanMass
          (receipt.wholePath
            ⟨requestedTime,
              ⟨receipt.requestedTimePos.le, le_rfl⟩⟩)) :
    puncturedEuclideanSpaceTimeSquare receipt.wholeTangent +
        (1 / 2 : Real) *
          puncturedEuclideanSpaceTimeSquare
            (receiptViscousNegativeOneState receipt) ≤
      ((9 * 1557504 * biotSavartSerrinConstant ^ 2) /
          (2 * (nu.coeff ^ 2 * (2 * Real.pi) ^ 2))) *
        (ceiling ^ 3 * requestedTime) := by
  have boundaryNonneg :
      0 ≤ nu.coeff *
        (wholeVorticityEuclideanMass
            (receipt.wholePath
              ⟨requestedTime,
                ⟨receipt.requestedTimePos.le, le_rfl⟩⟩) -
          wholeVorticityEuclideanMass initialState) :=
    mul_nonneg nu.coeff_pos.le (sub_nonneg.mpr massNondecreasing)
  have signed :=
    receipt_tangentHalfViscousSquare_add_boundary_le_cubicTime
      receipt massBound
  have target :
      puncturedEuclideanSpaceTimeSquare receipt.wholeTangent +
          (1 / 2 : Real) *
            puncturedEuclideanSpaceTimeSquare
              (receiptViscousNegativeOneState receipt) ≤
        ((9 * 1557504 * biotSavartSerrinConstant ^ 2) /
            (2 * (nu.coeff ^ 2 * (2 * Real.pi) ^ 2))) *
          (ceiling ^ 3 * requestedTime) := by
    linarith
  exact target

/-- A receipt whose endpoint vorticity mass does not decrease selects one
actual time slice where its tangent row and viscous gradient row obey the
same scale-critical cubic budget generated by the whole NS equation. -/
theorem receipt_exists_scaleCriticalTangentGradientState
    {initialState : ComplexVorticityHilbertState}
    {requestedTime ceiling : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (massBound :
      ∀ᵐ time ∂(commonTimeMeasure requestedTime),
        wholeVorticityEuclideanMass (receipt.wholePath time) ≤ ceiling)
    (massNondecreasing :
      wholeVorticityEuclideanMass initialState ≤
        wholeVorticityEuclideanMass
          (receipt.wholePath
            ⟨requestedTime,
              ⟨receipt.requestedTimePos.le, le_rfl⟩⟩)) :
    ∃ time : Icc (0 : Real) requestedTime,
      (Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (receipt.wholePath time wave)) ∧
      ‖puncturedEuclideanSpaceTimeState receipt.wholeTangent time‖ ^ 2 +
          ((nu.coeff ^ 2 * (2 * Real.pi) ^ 2) / 2) *
            wholeStateVorticityGradientMass (receipt.wholePath time) ≤
        ((9 * 1557504 * biotSavartSerrinConstant ^ 2) /
          (2 * (nu.coeff ^ 2 * (2 * Real.pi) ^ 2))) *
            ceiling ^ 3 := by
  let viscousConstant : Real := nu.coeff ^ 2 * (2 * Real.pi) ^ 2
  let scaleConstant : Real := 9 * 1557504 * biotSavartSerrinConstant ^ 2
  let cubicConstant : Real := scaleConstant / (2 * viscousConstant)
  let mass : Icc (0 : Real) requestedTime → Real := fun time =>
    wholeVorticityEuclideanMass (receipt.wholePath time)
  let gradient : Icc (0 : Real) requestedTime → Real := fun time =>
    wholeStateVorticityGradientMass (receipt.wholePath time)
  let tangentDensity : Icc (0 : Real) requestedTime → Real := fun time =>
    ‖puncturedEuclideanSpaceTimeState receipt.wholeTangent time‖ ^ 2
  let combinedDensity : Icc (0 : Real) requestedTime → Real := fun time =>
    tangentDensity time + (viscousConstant / 2) * gradient time
  have viscousConstantPos : 0 < viscousConstant := by
    dsimp only [viscousConstant]
    exact mul_pos
      (sq_pos_of_pos nu.coeff_pos)
      (sq_pos_of_pos (mul_pos zero_lt_two Real.pi_pos))
  have combinedSquareCeilingLe :
      puncturedEuclideanSpaceTimeSquare receipt.wholeTangent +
          (1 / 2 : Real) *
            puncturedEuclideanSpaceTimeSquare
              (receiptViscousNegativeOneState receipt) ≤
        cubicConstant * (ceiling ^ 3 * requestedTime) := by
    simpa only [cubicConstant, scaleConstant, viscousConstant] using
      (receipt_tangentHalfViscousSquare_le_cubicTime
        receipt massBound massNondecreasing)
  have tangentIntegrable :
      Integrable tangentDensity (commonTimeMeasure requestedTime) := by
    dsimp only [tangentDensity]
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (MeasureTheory.Lp.memLp
        (puncturedEuclideanSpaceTimeState
          receipt.wholeTangent)).integrable_norm_rpow
        (by norm_num) (by norm_num)
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
      Integrable (fun time => viscousConstant * gradient time)
        (commonTimeMeasure requestedTime) := by
    apply mappedViscousSquareIntegrable.congr
    filter_upwards [
      receiptViscousNegativeOneEuclideanMass_ae_eq_gradient receipt] with
        time pointEq
    simpa only [viscousConstant, gradient] using pointEq
  have halfGradientIntegrable :
      Integrable (fun time => (viscousConstant / 2) * gradient time)
        (commonTimeMeasure requestedTime) := by
    have scaled := weightedGradientIntegrable.const_mul (1 / 2 : Real)
    convert scaled using 1
    funext time
    ring
  have combinedIntegrable :
      Integrable combinedDensity (commonTimeMeasure requestedTime) :=
    tangentIntegrable.add halfGradientIntegrable
  have combinedIntegralEq :
      (∫ time, combinedDensity time
          ∂(commonTimeMeasure requestedTime)) =
        puncturedEuclideanSpaceTimeSquare receipt.wholeTangent +
          (1 / 2 : Real) *
            puncturedEuclideanSpaceTimeSquare
              (receiptViscousNegativeOneState receipt) := by
    rw [show combinedDensity = fun time =>
        tangentDensity time + (viscousConstant / 2) * gradient time by rfl,
      integral_add tangentIntegrable halfGradientIntegrable,
      integral_const_mul]
    have tangentEq :=
      puncturedEuclideanSpaceTimeState_norm_sq_eq_integral
        receipt.wholeTangent
    have viscousEq :=
      receiptViscousNegativeOneEuclideanSquare_eq_gradient receipt
    calc
      (∫ time, tangentDensity time
          ∂(commonTimeMeasure requestedTime)) +
            (viscousConstant / 2) *
              ∫ time, gradient time
                ∂(commonTimeMeasure requestedTime) =
          puncturedEuclideanSpaceTimeSquare receipt.wholeTangent +
            (viscousConstant / 2) *
              ∫ time, gradient time
                ∂(commonTimeMeasure requestedTime) := by
        dsimp only [tangentDensity]
        unfold puncturedEuclideanSpaceTimeSquare
        rw [tangentEq]
      _ = puncturedEuclideanSpaceTimeSquare receipt.wholeTangent +
          (1 / 2 : Real) *
            puncturedEuclideanSpaceTimeSquare
              (receiptViscousNegativeOneState receipt) := by
        dsimp only [viscousConstant, gradient]
        rw [viscousEq]
        ring
  have combinedIntegralLe :
      (∫ time, combinedDensity time
          ∂(commonTimeMeasure requestedTime)) ≤
        cubicConstant * (ceiling ^ 3 * requestedTime) := by
    rw [combinedIntegralEq]
    exact combinedSquareCeilingLe
  have measureNonzero : commonTimeMeasure requestedTime ≠ 0 := by
    intro measureZero
    have realZero := congrArg
      (fun measure : Measure (Icc (0 : Real) requestedTime) =>
        measure.real Set.univ) measureZero
    rw [euclideanBalance_commonTimeMeasure_univ_real
      requestedTime receipt.requestedTimePos.le] at realZero
    simp at realZero
    linarith [receipt.requestedTimePos]
  have pathGradientSummableAE :
      ∀ᵐ time ∂(commonTimeMeasure requestedTime),
        Summable fun wave : IntegerWavevector =>
          integerWaveNormSq wave *
            complexCoordinateAmplitudeSq (receipt.wholePath time wave) := by
    filter_upwards [
      receiptPointwiseGradient_ae_summable receipt,
      receiptStateLimit_eq_wholePath_ae receipt] with
        time gradientSummable stateEq
    simpa only [stateEq] using gradientSummable
  have exceptionalNull :
      (commonTimeMeasure requestedTime)
          {time : Icc (0 : Real) requestedTime |
            ¬ Summable fun wave : IntegerWavevector =>
              integerWaveNormSq wave *
                complexCoordinateAmplitudeSq
                  (receipt.wholePath time wave)} = 0 :=
    ae_iff.mp pathGradientSummableAE
  obtain ⟨time, timeNotExceptional, timeLeAverage⟩ :=
    exists_notMem_null_le_average measureNonzero combinedIntegrable
      exceptionalNull
  have timeGradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (receipt.wholePath time wave) := by
    simpa only [Set.mem_setOf_eq, Classical.not_not] using
      timeNotExceptional
  refine ⟨time, timeGradientSummable, ?_⟩
  change combinedDensity time ≤ cubicConstant * ceiling ^ 3
  calc
    combinedDensity time ≤
        ⨍ point, combinedDensity point
          ∂(commonTimeMeasure requestedTime) := timeLeAverage
    _ = requestedTime⁻¹ *
          ∫ point, combinedDensity point
            ∂(commonTimeMeasure requestedTime) := by
      rw [average_eq, euclideanBalance_commonTimeMeasure_univ_real
        requestedTime receipt.requestedTimePos.le]
      simp only [smul_eq_mul]
    _ ≤ requestedTime⁻¹ *
          (cubicConstant * (ceiling ^ 3 * requestedTime)) :=
      mul_le_mul_of_nonneg_left combinedIntegralLe
        (inv_nonneg.mpr receipt.requestedTimePos.le)
    _ = cubicConstant * ceiling ^ 3 := by
      field_simp [receipt.requestedTimePos.ne']
    _ = ((9 * 1557504 * biotSavartSerrinConstant ^ 2) /
          (2 * (nu.coeff ^ 2 * (2 * Real.pi) ^ 2))) *
            ceiling ^ 3 := by
      rfl

/-- The same-receipt PDE balance and scale-critical absorption give a
cubic source law for its actual whole-vorticity mass increment. -/
theorem receiptVorticityMass_increment_le_cubicPayment
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime) :
    nu.coeff *
        (wholeVorticityEuclideanMass
            (receipt.wholePath
              ⟨requestedTime,
                ⟨receipt.requestedTimePos.le, le_rfl⟩⟩) -
          wholeVorticityEuclideanMass initialState) ≤
      ((9 * 1557504 * biotSavartSerrinConstant ^ 2) /
          (2 * (nu.coeff ^ 2 * (2 * Real.pi) ^ 2))) *
        ∫ time,
          wholeVorticityEuclideanMass (receipt.wholePath time) ^ 3
          ∂(commonTimeMeasure requestedTime) := by
  have balance := receiptNonlinearNegativeOneEuclideanBalance receipt
  have absorption :=
    receiptNonlinearNegativeOneEuclideanSquare_le_halfViscous_add_cubic
      receipt
  have tangentNonneg :
      0 ≤ puncturedEuclideanSpaceTimeSquare receipt.wholeTangent := by
    unfold puncturedEuclideanSpaceTimeSquare
    positivity
  have viscousNonneg :
      0 ≤ puncturedEuclideanSpaceTimeSquare
        (receiptViscousNegativeOneState receipt) := by
    unfold puncturedEuclideanSpaceTimeSquare
    positivity
  linarith

/-! ## Shifted native prefix telescope -/

/-- Complete nonlinear Euclidean square accumulated over the actual shifted
native receipts. -/
def wholeRestartShiftedNonlinearNegativeOneEuclideanPrefix
    (initial : GeneratedWholeRestartCurrent nu)
    (length : Nat) : Real :=
  ∑ index ∈ Finset.range length,
    puncturedEuclideanSpaceTimeSquare
      (receiptNonlinearNegativeOneState
        (run initial index).nextContact.prefixReceipt)

/-- Complete tangent square over the identical shifted receipt prefix. -/
def wholeRestartShiftedTangentNegativeOneEuclideanPrefix
    (initial : GeneratedWholeRestartCurrent nu)
    (length : Nat) : Real :=
  ∑ index ∈ Finset.range length,
    puncturedEuclideanSpaceTimeSquare
      (run initial index).nextContact.prefixReceipt.wholeTangent

/-- Complete viscous negative-one square over the identical shifted receipt
prefix. -/
def wholeRestartShiftedViscousNegativeOneEuclideanPrefix
    (initial : GeneratedWholeRestartCurrent nu)
    (length : Nat) : Real :=
  ∑ index ∈ Finset.range length,
    puncturedEuclideanSpaceTimeSquare
      (receiptViscousNegativeOneState
        (run initial index).nextContact.prefixReceipt)

/-- Exact chronological telescope.  Every intermediate endpoint mass is
written by one actual receipt and consumed as the next receipt's initial
mass; no restart window is charged twice. -/
theorem wholeRestartShiftedNonlinearNegativeOneEuclideanPrefix_balance
    (initial : GeneratedWholeRestartCurrent nu) :
    ∀ length : Nat,
      wholeRestartShiftedNonlinearNegativeOneEuclideanPrefix
            initial length +
          nu.coeff *
            wholeVorticityEuclideanMass initial.contact.physicalState =
        wholeRestartShiftedTangentNegativeOneEuclideanPrefix
              initial length +
            wholeRestartShiftedViscousNegativeOneEuclideanPrefix
              initial length +
          nu.coeff *
            wholeVorticityEuclideanMass
              (run initial length).contact.physicalState
  | 0 => by
      simp [wholeRestartShiftedNonlinearNegativeOneEuclideanPrefix,
        wholeRestartShiftedTangentNegativeOneEuclideanPrefix,
        wholeRestartShiftedViscousNegativeOneEuclideanPrefix]
  | length + 1 => by
      have previous :=
        wholeRestartShiftedNonlinearNegativeOneEuclideanPrefix_balance
          initial length
      have edge :=
        receiptNonlinearNegativeOneEuclideanBalance
          (nu := nu)
          (run initial length).nextContact.prefixReceipt
      rw [(run initial length).nextContact_prefix_terminal] at edge
      change
        puncturedEuclideanSpaceTimeSquare
              (receiptNonlinearNegativeOneState
                (run initial length).nextContact.prefixReceipt) +
            nu.coeff *
              wholeVorticityEuclideanMass
                (run initial length).contact.physicalState =
          puncturedEuclideanSpaceTimeSquare
                (run initial length).nextContact.prefixReceipt.wholeTangent +
              puncturedEuclideanSpaceTimeSquare
                (receiptViscousNegativeOneState
                  (run initial length).nextContact.prefixReceipt) +
            nu.coeff *
              wholeVorticityEuclideanMass
                (run initial (length + 1)).contact.physicalState at edge
      unfold wholeRestartShiftedNonlinearNegativeOneEuclideanPrefix
        wholeRestartShiftedTangentNegativeOneEuclideanPrefix
        wholeRestartShiftedViscousNegativeOneEuclideanPrefix
      rw [Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ]
      change
        wholeRestartShiftedNonlinearNegativeOneEuclideanPrefix
              initial length +
            puncturedEuclideanSpaceTimeSquare
              (receiptNonlinearNegativeOneState
                (run initial length).nextContact.prefixReceipt) +
          nu.coeff *
            wholeVorticityEuclideanMass initial.contact.physicalState =
        wholeRestartShiftedTangentNegativeOneEuclideanPrefix
              initial length +
            puncturedEuclideanSpaceTimeSquare
              (run initial length).nextContact.prefixReceipt.wholeTangent +
          (wholeRestartShiftedViscousNegativeOneEuclideanPrefix
                initial length +
              puncturedEuclideanSpaceTimeSquare
                (receiptViscousNegativeOneState
                  (run initial length).nextContact.prefixReceipt)) +
          nu.coeff *
            wholeVorticityEuclideanMass
              (run initial (length + 1)).contact.physicalState
      nlinarith

/-! ## Exact chronological block balance -/

/-- Complete nonlinear Euclidean square on one literal half-open block of
the authoritative native run. -/
def wholeRestartIcoNonlinearNegativeOneEuclideanPayment
    (initial : GeneratedWholeRestartCurrent nu)
    (start finish : Nat) : Real :=
  ∑ index ∈ Finset.Ico start finish,
    puncturedEuclideanSpaceTimeSquare
      (receiptNonlinearNegativeOneState
        (run initial index).nextContact.prefixReceipt)

/-- Complete tangent Euclidean square on the identical actual receipts. -/
def wholeRestartIcoTangentNegativeOneEuclideanPayment
    (initial : GeneratedWholeRestartCurrent nu)
    (start finish : Nat) : Real :=
  ∑ index ∈ Finset.Ico start finish,
    puncturedEuclideanSpaceTimeSquare
      (run initial index).nextContact.prefixReceipt.wholeTangent

/-- Complete viscous negative-one Euclidean square on the identical actual
receipts. -/
def wholeRestartIcoViscousNegativeOneEuclideanPayment
    (initial : GeneratedWholeRestartCurrent nu)
    (start finish : Nat) : Real :=
  ∑ index ∈ Finset.Ico start finish,
    puncturedEuclideanSpaceTimeSquare
      (receiptViscousNegativeOneState
        (run initial index).nextContact.prefixReceipt)

/-- Exact `Ico` telescope of the same-receipt Euclidean PDE balance. The
start and finish contacts are observations of the same native run; every
intermediate mass is written and consumed exactly once. -/
theorem wholeRestartIcoNonlinearNegativeOneEuclideanPayment_balance
    (initial : GeneratedWholeRestartCurrent nu)
    (start finish : Nat)
    (start_le_finish : start ≤ finish) :
    wholeRestartIcoNonlinearNegativeOneEuclideanPayment
          initial start finish +
        nu.coeff * wholeVorticityEuclideanMass
          (run initial start).contact.physicalState =
      wholeRestartIcoTangentNegativeOneEuclideanPayment
            initial start finish +
          wholeRestartIcoViscousNegativeOneEuclideanPayment
            initial start finish +
        nu.coeff * wholeVorticityEuclideanMass
          (run initial finish).contact.physicalState := by
  have finishBalance :=
    wholeRestartShiftedNonlinearNegativeOneEuclideanPrefix_balance
      initial finish
  have startBalance :=
    wholeRestartShiftedNonlinearNegativeOneEuclideanPrefix_balance
      initial start
  unfold wholeRestartShiftedNonlinearNegativeOneEuclideanPrefix at finishBalance startBalance
  unfold wholeRestartShiftedTangentNegativeOneEuclideanPrefix at finishBalance startBalance
  unfold wholeRestartShiftedViscousNegativeOneEuclideanPrefix at finishBalance startBalance
  have nonlinearSplit :=
    Finset.sum_range_add_sum_Ico
      (fun index =>
        puncturedEuclideanSpaceTimeSquare
          (receiptNonlinearNegativeOneState
            (run initial index).nextContact.prefixReceipt))
      start_le_finish
  have tangentSplit :=
    Finset.sum_range_add_sum_Ico
      (fun index =>
        puncturedEuclideanSpaceTimeSquare
          (run initial index).nextContact.prefixReceipt.wholeTangent)
      start_le_finish
  have viscousSplit :=
    Finset.sum_range_add_sum_Ico
      (fun index =>
        puncturedEuclideanSpaceTimeSquare
          (receiptViscousNegativeOneState
            (run initial index).nextContact.prefixReceipt))
      start_le_finish
  unfold wholeRestartIcoNonlinearNegativeOneEuclideanPayment
    wholeRestartIcoTangentNegativeOneEuclideanPayment
    wholeRestartIcoViscousNegativeOneEuclideanPayment
  linarith

/-! ## Original-source cofinal action law -/

/-- Complete nonlinear `L²_t H⁻¹_x` action written by the original
chronological root prefix. -/
def nativeAccumulationNonlinearNegativeOneActionPrefix
    (initial : GeneratedWholeRestartCurrent nu)
    (index : Nat) : Real :=
  wholeRestartIcoNonlinearNegativeOneEuclideanPayment initial 0 index

/-- Every locally bounded elapsed-time fibre of the same actual source run
forces its chronological nonlinear action to diverge. -/
theorem
    nativeAccumulationNonlinearNegativeOneActionPrefix_tendsto_atTop_of_elapsedTime_bddAbove
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    Tendsto
      (nativeAccumulationNonlinearNegativeOneActionPrefix initial)
      atTop atTop := by
  let initialMass :=
    wholeVorticityEuclideanMass (run initial 0).contact.physicalState
  rw [tendsto_atTop]
  intro requested
  let requestedMass :=
    (max requested 0 + nu.coeff * initialMass + 1) / nu.coeff
  have viscosityRequestedMass :
      nu.coeff * requestedMass =
        max requested 0 + nu.coeff * initialMass + 1 := by
    dsimp only [requestedMass]
    field_simp [ne_of_gt nu.coeff_pos]
  have massEventually :
      ∀ᶠ index : Nat in atTop,
        requestedMass ≤ restartPhysicalVorticityMass initial index :=
    (tendsto_atTop.1
      (tendsto_restartPhysicalVorticityMass_atTop_of_elapsedTime_bddAbove
        initial elapsedBounded)) requestedMass
  filter_upwards [massEventually] with index massLarge
  have balance :=
    wholeRestartIcoNonlinearNegativeOneEuclideanPayment_balance
      initial 0 index (Nat.zero_le index)
  have tangentNonneg :
      0 ≤ wholeRestartIcoTangentNegativeOneEuclideanPayment
        initial 0 index := by
    unfold wholeRestartIcoTangentNegativeOneEuclideanPayment
    exact Finset.sum_nonneg fun _index _indexMem => sq_nonneg _
  have viscousNonneg :
      0 ≤ wholeRestartIcoViscousNegativeOneEuclideanPayment
        initial 0 index := by
    unfold wholeRestartIcoViscousNegativeOneEuclideanPayment
    exact Finset.sum_nonneg fun _index _indexMem => sq_nonneg _
  change requested ≤
    nativeAccumulationNonlinearNegativeOneActionPrefix initial index
  unfold nativeAccumulationNonlinearNegativeOneActionPrefix
  change
    requestedMass ≤
      wholeVorticityEuclideanMass
        (run initial index).contact.physicalState at massLarge
  dsimp only [initialMass] at viscosityRequestedMass balance
  nlinarith [nu.coeff_pos, le_max_left requested 0]

/-! ## Literal cross incidence on the original cofinal prefix -/

/-- Chronological prefix of the already paid pair diagonal. -/
def nativeAccumulationSymmetricVorticityPairDiagonalActionPrefix
    (initial : GeneratedWholeRestartCurrent nu)
    (length : Nat) : Real :=
  ∑ index ∈ Finset.range length,
    wholeRestartNextPrefixSymmetricVorticityPairDiagonalActionReal
      (run initial index)

/-- Chronological prefix of the signed literal cross incidences left after
the paid diagonal is removed from the same NS nonlinear action. -/
def nativeAccumulationSymmetricVorticityPairLiteralCrossActionPrefix
    (initial : GeneratedWholeRestartCurrent nu)
    (length : Nat) : Real :=
  ∑ index ∈ Finset.range length,
    wholeRestartNextPrefixSymmetricVorticityPairLiteralCrossAction
      (run initial index)

theorem
    nativeAccumulationNonlinearNegativeOneActionPrefix_eq_diagonal_add_literalCross
    (initial : GeneratedWholeRestartCurrent nu)
    (length : Nat) :
    nativeAccumulationNonlinearNegativeOneActionPrefix initial length =
      nativeAccumulationSymmetricVorticityPairDiagonalActionPrefix
          initial length +
        nativeAccumulationSymmetricVorticityPairLiteralCrossActionPrefix
          initial length := by
  unfold nativeAccumulationNonlinearNegativeOneActionPrefix
    wholeRestartIcoNonlinearNegativeOneEuclideanPayment
    nativeAccumulationSymmetricVorticityPairDiagonalActionPrefix
    nativeAccumulationSymmetricVorticityPairLiteralCrossActionPrefix
  rw [show Finset.Ico 0 length = Finset.range length by
    ext index
    simp]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro index _indexMem
  exact
    nextPrefix_receiptNonlinearNegativeOneEuclideanSquare_eq_diagonal_add_literalCross
      (run initial index)

/-- If elapsed time were bounded, the unbounded canonical nonlinear action
cannot be hidden in the source-paid diagonal.  It therefore remains on the
literal cross-incidence prefix of the identical actual run. -/
theorem
    nativeAccumulationSymmetricVorticityPairLiteralCrossActionPrefix_tendsto_atTop_of_elapsedTime_bddAbove
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    Tendsto
      (nativeAccumulationSymmetricVorticityPairLiteralCrossActionPrefix
        initial)
      atTop atTop := by
  have nonlinearTendsto :=
    nativeAccumulationNonlinearNegativeOneActionPrefix_tendsto_atTop_of_elapsedTime_bddAbove
      initial elapsedBounded
  have diagonalSummable :=
    summable_run_nextPrefixSymmetricVorticityPairDiagonalActionReal initial
  rw [tendsto_atTop]
  intro requested
  have nonlinearEventually :=
    (tendsto_atTop.1 nonlinearTendsto)
      (requested +
        ∑' index : Nat,
          wholeRestartNextPrefixSymmetricVorticityPairDiagonalActionReal
            (run initial index))
  filter_upwards [nonlinearEventually] with length nonlinearLarge
  have diagonalLe :
      nativeAccumulationSymmetricVorticityPairDiagonalActionPrefix
          initial length ≤
        ∑' index : Nat,
          wholeRestartNextPrefixSymmetricVorticityPairDiagonalActionReal
            (run initial index) := by
    unfold nativeAccumulationSymmetricVorticityPairDiagonalActionPrefix
    exact diagonalSummable.sum_le_tsum (Finset.range length)
      fun index _indexMem => ENNReal.toReal_nonneg
  have split :=
    nativeAccumulationNonlinearNegativeOneActionPrefix_eq_diagonal_add_literalCross
      initial length
  linarith

private theorem elapsedTime_bddAbove_generates_literalCrossAction_ne_zero
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (lower : Nat) :
    ∃ index : Nat,
      lower ≤ index ∧
        wholeRestartNextPrefixSymmetricVorticityPairLiteralCrossAction
          (run initial index) ≠ 0 := by
  have crossTendsto :=
    nativeAccumulationSymmetricVorticityPairLiteralCrossActionPrefix_tendsto_atTop_of_elapsedTime_bddAbove
      initial elapsedBounded
  let lowerPrefix :=
    nativeAccumulationSymmetricVorticityPairLiteralCrossActionPrefix
      initial lower
  have eventuallyLarger :=
    (tendsto_atTop.1 crossTendsto) (lowerPrefix + 1)
  obtain ⟨threshold, largerAfter⟩ :=
    Filter.eventually_atTop.1 eventuallyLarger
  let length := max threshold lower
  have thresholdLe : threshold ≤ length := Nat.le_max_left _ _
  have lowerLe : lower ≤ length := Nat.le_max_right _ _
  have prefixLarger :
      lowerPrefix <
        nativeAccumulationSymmetricVorticityPairLiteralCrossActionPrefix
          initial length :=
    lt_of_lt_of_le (lt_add_one lowerPrefix)
      (largerAfter length thresholdLe)
  have tailPositive :
      0 <
        ∑ index ∈ Finset.Ico lower length,
          wholeRestartNextPrefixSymmetricVorticityPairLiteralCrossAction
            (run initial index) := by
    rw [Finset.sum_Ico_eq_sub _ lowerLe]
    exact sub_pos.mpr prefixLarger
  obtain ⟨index, _indexMem, actionNonzero⟩ :=
    Finset.exists_ne_zero_of_sum_ne_zero (ne_of_gt tailPositive)
  exact ⟨index, (Finset.mem_Ico.mp _indexMem).1, actionNonzero⟩

private theorem literalCrossAction_ne_zero_generates_time
    (initial : GeneratedWholeRestartCurrent nu)
    (index : Nat)
    (actionNonzero :
      wholeRestartNextPrefixSymmetricVorticityPairLiteralCrossAction
        (run initial index) ≠ 0) :
    ∃ time : Icc (0 : Real) (run initial index).nextContact.time.1,
      actualWholeSymmetricVorticityPairNegativeOneLiteralCrossMass
        (run initial index).nextContact.prefixReceipt time ≠ 0 := by
  by_contra noTime
  push Not at noTime
  apply actionNonzero
  unfold wholeRestartNextPrefixSymmetricVorticityPairLiteralCrossAction
  simp only [noTime, integral_zero]

private theorem literalCrossMass_ne_zero_generates_orderedPairInterference
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (time : Icc (0 : Real) requestedTime)
    (massNonzero :
      actualWholeSymmetricVorticityPairNegativeOneLiteralCrossMass
        receipt time ≠ 0) :
    ∃ output left right : IntegerWavevector,
      right ≠ left ∧
        complexCoordinateRealInner
          (actualWholeSymmetricVorticityPairVector
            receipt output left time)
          (actualWholeSymmetricVorticityPairVector
            receipt output right time) ≠ 0 := by
  have existsOutput :
      ∃ output : IntegerWavevector,
        (integerWaveViscousMultiplier output)⁻¹ *
            pairVectorLiteralCrossInterference
              (fun first : IntegerWavevector =>
                actualWholeSymmetricVorticityPairVector
                  receipt output first time) ≠ 0 := by
    by_contra noOutput
    push Not at noOutput
    apply massNonzero
    unfold actualWholeSymmetricVorticityPairNegativeOneLiteralCrossMass
    simp_rw [noOutput]
    exact tsum_zero
  obtain ⟨output, outputNonzero⟩ := existsOutput
  have crossNonzero :
      pairVectorLiteralCrossInterference
        (fun first : IntegerWavevector =>
          actualWholeSymmetricVorticityPairVector
            receipt output first time) ≠ 0 :=
    (mul_ne_zero_iff.mp outputNonzero).2
  unfold pairVectorLiteralCrossInterference at crossNonzero
  have existsLeft :
      ∃ left : IntegerWavevector,
        (∑' right : IntegerWavevector,
          if right = left then 0
          else complexCoordinateRealInner
            (actualWholeSymmetricVorticityPairVector
              receipt output left time)
            (actualWholeSymmetricVorticityPairVector
              receipt output right time)) ≠ 0 := by
    by_contra noLeft
    push Not at noLeft
    apply crossNonzero
    simp_rw [noLeft]
    exact tsum_zero
  obtain ⟨left, leftNonzero⟩ := existsLeft
  have existsRight :
      ∃ right : IntegerWavevector,
        (if right = left then 0
          else complexCoordinateRealInner
            (actualWholeSymmetricVorticityPairVector
              receipt output left time)
            (actualWholeSymmetricVorticityPairVector
              receipt output right time)) ≠ 0 := by
    by_contra noRight
    push Not at noRight
    apply leftNonzero
    simp_rw [noRight]
    exact tsum_zero
  obtain ⟨right, rightNonzero⟩ := existsRight
  by_cases rightEq : right = left
  · simp [rightEq] at rightNonzero
  · exact ⟨output, left, right, rightEq, by
      simpa only [if_neg rightEq] using rightNonzero⟩

private theorem symmetricPairVector_ne_zero_generates_actualPairVector
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (time : Icc (0 : Real) requestedTime)
    (output first : IntegerWavevector)
    (symmetricNonzero :
      actualWholeSymmetricVorticityPairVector
        receipt output first time ≠ 0) :
    ∃ actualFirst : IntegerWavevector,
      (actualFirst = first ∨ actualFirst = output - first) ∧
        actualWholeContinuousPairVector
          receipt output actualFirst time ≠ 0 := by
  by_cases directNonzero :
      actualWholeContinuousPairVector receipt output first time ≠ 0
  · exact ⟨first, Or.inl rfl, directNonzero⟩
  · have directZero :
        actualWholeContinuousPairVector receipt output first time = 0 :=
      not_ne_iff.mp directNonzero
    have swappedNonzero :
        actualWholeContinuousPairVector
          receipt output (output - first) time ≠ 0 := by
      intro swappedZero
      apply symmetricNonzero
      unfold actualWholeSymmetricVorticityPairVector
      rw [directZero, swappedZero, zero_add, smul_zero]
    exact ⟨output - first, Or.inr rfl, swappedNonzero⟩

/-- Bounded elapsed time therefore generates a concrete literal
off-diagonal incidence on one original receipt and two nonzero actual pair
vectors underneath it.  Each vector is immediately consumed by the native
read/write split: it survives in the next physical pair table or writes a
nonzero forced trace on that same edge.  No branch, target state, or
settlement certificate is supplied by the caller. -/
theorem elapsedTime_bddAbove_generates_literalCross_actualPairIncidence
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    ∀ lower : Nat,
      ∃ index : Nat,
        lower ≤ index ∧
        ∃ time : Icc (0 : Real) (run initial index).nextContact.time.1,
        ∃ output left right leftActual rightActual : IntegerWavevector,
          right ≠ left ∧
          complexCoordinateRealInner
            (actualWholeSymmetricVorticityPairVector
              (run initial index).nextContact.prefixReceipt
              output left time)
            (actualWholeSymmetricVorticityPairVector
              (run initial index).nextContact.prefixReceipt
              output right time) ≠ 0 ∧
          (leftActual = left ∨ leftActual = output - left) ∧
          (rightActual = right ∨ rightActual = output - right) ∧
          actualWholeContinuousPairVector
              (run initial index).nextContact.prefixReceipt
              output leftActual time ≠ 0 ∧
          actualWholeContinuousPairVector
              (run initial index).nextContact.prefixReceipt
              output rightActual time ≠ 0 ∧
          (wholeRestartNextPairOccurrence
                initial index output leftActual ≠ 0 ∨
            wholeRestartPairOccurrenceTrace
              initial index output leftActual time ≠ 0) ∧
          (wholeRestartNextPairOccurrence
                initial index output rightActual ≠ 0 ∨
            wholeRestartPairOccurrenceTrace
              initial index output rightActual time ≠ 0) := by
  intro lower
  obtain ⟨index, lowerLe, actionNonzero⟩ :=
    elapsedTime_bddAbove_generates_literalCrossAction_ne_zero
      initial elapsedBounded lower
  obtain ⟨time, massNonzero⟩ :=
    literalCrossAction_ne_zero_generates_time
      initial index actionNonzero
  obtain ⟨output, left, right, rightNeLeft, interferenceNonzero⟩ :=
    literalCrossMass_ne_zero_generates_orderedPairInterference
      (run initial index).nextContact.prefixReceipt time massNonzero
  have leftSymmetricNonzero :
      actualWholeSymmetricVorticityPairVector
        (run initial index).nextContact.prefixReceipt
        output left time ≠ 0 := by
    intro leftZero
    apply interferenceNonzero
    rw [leftZero]
    simp [complexCoordinateRealInner]
  have rightSymmetricNonzero :
      actualWholeSymmetricVorticityPairVector
        (run initial index).nextContact.prefixReceipt
        output right time ≠ 0 := by
    intro rightZero
    apply interferenceNonzero
    rw [rightZero]
    simp [complexCoordinateRealInner]
  obtain ⟨leftActual, leftActualAt, leftActualNonzero⟩ :=
    symmetricPairVector_ne_zero_generates_actualPairVector
      (run initial index).nextContact.prefixReceipt time output left
      leftSymmetricNonzero
  obtain ⟨rightActual, rightActualAt, rightActualNonzero⟩ :=
    symmetricPairVector_ne_zero_generates_actualPairVector
      (run initial index).nextContact.prefixReceipt time output right
      rightSymmetricNonzero
  have leftWrite :=
    actualWholeContinuousPairVector_ne_zero_next_or_trace
      initial index output leftActual time leftActualNonzero
  have rightWrite :=
    actualWholeContinuousPairVector_ne_zero_next_or_trace
      initial index output rightActual time rightActualNonzero
  exact
    ⟨index, lowerLe, time, output, left, right, leftActual, rightActual,
      rightNeLeft, interferenceNonzero, leftActualAt, rightActualAt,
      leftActualNonzero, rightActualNonzero, leftWrite, rightWrite⟩

/-! ## Reciprocal-scale physical retention of the finite output action -/

private theorem reciprocalOutputFrequencyCube_waveNeg_mem
    (radius : Nat) {wave : IntegerWavevector}
    (waveMem : wave ∈ integerWaveFrequencyCube radius) :
    waveNeg wave ∈ integerWaveFrequencyCube radius := by
  rw [integerWaveFrequencyCube, Fintype.mem_piFinset] at waveMem ⊢
  intro coordinate
  have coordinateMem := Finset.mem_Icc.mp (waveMem coordinate)
  apply Finset.mem_Icc.mpr
  constructor
  · simpa [waveNeg] using neg_le_neg coordinateMem.2
  · simpa [waveNeg] using neg_le_neg coordinateMem.1

private theorem
    reciprocalOutputCoarseKeep_weightedNonlinear_reality
    (scale : CoarseScale)
    (state : ComplexVorticityHilbertState)
    (stateTransverse : WholeStateTransverse state)
    (reality : FiniteStateFourierReality state)
    (output : IntegerWavevector) :
    coarseCoefficientKeep scale
        (wholeStateVorticityNonlinearNegativeOneWeightedCoefficient state)
        (waveNeg output) =
      vectorConj
        (coarseCoefficientKeep scale
          (wholeStateVorticityNonlinearNegativeOneWeightedCoefficient state)
          output) := by
  rw [coarseCoefficientKeep_apply, coarseCoefficientKeep_apply,
    coarseCharacterMultiplier_waveNeg,
    wholeStateVorticityNonlinearNegativeOneWeightedCoefficient_waveNeg
      state stateTransverse reality output,
    vectorConj_smul]
  simp

private theorem
    physicalUnitCell_coarseFilteredWholeNonlinearNegativeOneOutputField_parseval
    (radius : Nat)
    (scale : CoarseScale)
    (state : ComplexVorticityHilbertState)
    (stateTransverse : WholeStateTransverse state)
    (reality : FiniteStateFourierReality state) :
    (∫ x in physicalUnitCell,
      velocityDot
        (coarseFilter scale
          (wholeStateVorticityNonlinearNegativeOneOutputField radius state))
        (coarseFilter scale
          (wholeStateVorticityNonlinearNegativeOneOutputField radius state)) x) =
      ∑ output ∈ integerWaveFrequencyCube radius,
        complexCoordinateVectorNormSq
          (coarseCoefficientKeep scale
            (wholeStateVorticityNonlinearNegativeOneWeightedCoefficient state)
            output) := by
  let modes := integerWaveFrequencyCube radius
  let coefficient :=
    wholeStateVorticityNonlinearNegativeOneWeightedCoefficient state
  let kept := coarseCoefficientKeep scale coefficient
  have observerExact :
      ∀ output ∈ modes,
        physicalUnitCellComplexFourierCoordinate output
            (finiteRealComplexFourierField modes kept) =
          kept output := by
    intro output outputMem
    rw [physicalUnitCellComplexFourierCoordinate_finiteRealComplexFourierField]
    funext coordinate
    rw [if_pos outputMem,
      if_pos (reciprocalOutputFrequencyCube_waveNeg_mem radius outputMem)]
    rw [show kept (waveNeg output) = vectorConj (kept output) by
      exact
        reciprocalOutputCoarseKeep_weightedNonlinear_reality
          scale state stateTransverse reality output]
    simp [vectorConj]
  have parseval :=
    physicalUnitCell_finiteRealComplexFourierField_parseval_of_observer
      modes kept observerExact
  rw [show
      coarseFilter scale
          (wholeStateVorticityNonlinearNegativeOneOutputField radius state) =
        finiteRealComplexFourierField modes kept by
      symm
      exact finiteRealComplexFourierField_coarseCoefficientKeep
        scale modes coefficient]
  simpa only [modes, kept, coefficient] using parseval

private theorem reciprocalOutputFrequencyCube_coordinate_abs_le
    (radius : Nat)
    {output : IntegerWavevector}
    (outputMem : output ∈ integerWaveFrequencyCube radius)
    (coordinate : Coordinate) :
    |(output coordinate : Real)| ≤ radius := by
  rw [integerWaveFrequencyCube, Fintype.mem_piFinset] at outputMem
  have coordinateMem := Finset.mem_Icc.mp (outputMem coordinate)
  rw [abs_le]
  constructor
  · exact_mod_cast coordinateMem.1
  · exact_mod_cast coordinateMem.2

/-- The actual normalized compact coarse kernel retains at least one quarter
of the complete physical negative-one action in a bounded output cube when
its radius is the reciprocal Fourier scale.  The multiplier lower bound is
generated by the kernel and the cube; it is not supplied as a premise. -/
theorem
    physicalUnitCell_wholeNonlinearNegativeOneOutputField_le_four_mul_coarseFilter
    (radius : Nat)
    (radiusPos : 0 < radius)
    (scale : CoarseScale)
    (scaleRadius :
      scale.radius = 1 / (6 * Real.pi * (radius : Real)))
    (state : ComplexVorticityHilbertState)
    (stateTransverse : WholeStateTransverse state)
    (reality : FiniteStateFourierReality state) :
    (∫ x in physicalUnitCell,
      velocityDot
        (wholeStateVorticityNonlinearNegativeOneOutputField radius state)
        (wholeStateVorticityNonlinearNegativeOneOutputField radius state) x) ≤
      4 * ∫ x in physicalUnitCell,
        velocityDot
          (coarseFilter scale
            (wholeStateVorticityNonlinearNegativeOneOutputField radius state))
          (coarseFilter scale
            (wholeStateVorticityNonlinearNegativeOneOutputField radius state)) x := by
  have radiusRealPos : 0 < (radius : Real) := by
    exact_mod_cast radiusPos
  have scaleSmall :
      6 * Real.pi * (radius : Real) * scale.radius ≤ 1 := by
    rw [scaleRadius]
    have denominatorPos :
        0 < 6 * Real.pi * (radius : Real) := by
      positivity
    rw [one_div]
    field_simp [denominatorPos.ne']
    norm_num
  have multiplierHalf :
      ∀ output ∈ integerWaveFrequencyCube radius,
        (1 / 2 : Real) ≤ coarseCharacterMultiplier scale output := by
    intro output outputMem
    exact coarseCharacterMultiplier_ge_half_of_coordinate_bound
      scale output radius (by positivity)
      (reciprocalOutputFrequencyCube_coordinate_abs_le
        radius outputMem) scaleSmall
  have coefficientLe :
      ∀ output ∈ integerWaveFrequencyCube radius,
        (integerWaveViscousMultiplier output)⁻¹ *
            complexCoordinateAmplitudeSq
              (wholeStateVorticityNonlinearCoefficientAt state output) ≤
          4 * complexCoordinateVectorNormSq
            (coarseCoefficientKeep scale
              (wholeStateVorticityNonlinearNegativeOneWeightedCoefficient state)
              output) := by
    intro output outputMem
    rw [←
      wholeStateVorticityNonlinearNegativeOneWeightedCoefficient_amplitudeSq
        state output,
      complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
    let multiplier := coarseCharacterMultiplier scale output
    let normSq := complexCoordinateVectorNormSq
      (wholeStateVorticityNonlinearNegativeOneWeightedCoefficient state output)
    have halfLe : (1 / 2 : Real) ≤ multiplier :=
      multiplierHalf output outputMem
    have normSqNonneg : 0 ≤ normSq := by
      unfold normSq
      exact complexCoordinateVectorNormSq_nonneg _
    have oneLe : (1 : Real) ≤ 4 * multiplier ^ 2 := by
      nlinarith
    have scaledRaw :=
      mul_le_mul_of_nonneg_right oneLe normSqNonneg
    have scaled : normSq ≤ (4 * multiplier ^ 2) * normSq := by
      simpa only [one_mul] using scaledRaw
    rw [coarseCoefficientKeep_apply,
      complexCoordinateVectorNormSq_smul, Complex.normSq_ofReal]
    change normSq ≤ 4 * (multiplier * multiplier * normSq)
    nlinarith [scaled]
  rw [
    physicalUnitCell_wholeStateVorticityNonlinearNegativeOneOutputField_parseval
      radius state stateTransverse reality,
    physicalUnitCell_coarseFilteredWholeNonlinearNegativeOneOutputField_parseval
      radius scale state stateTransverse reality,
    Finset.mul_sum]
  exact Finset.sum_le_sum fun output outputMem =>
    coefficientLe output outputMem

/-- On almost every slice of one actual receipt, its finite low-output pair
action is retained by the same reciprocal-scale physical coarse observation.
Fourier reality is consumed only through the receipt's existing a.e. law. -/
theorem
    receiptLowOutputPairDensity_le_four_mul_reciprocalCoarsePhysicalDensity_ae
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (radius : Nat)
    (radiusPos : 0 < radius)
    (scale : CoarseScale)
    (scaleRadius :
      scale.radius = 1 / (12 * Real.pi * (radius : Real))) :
    ∀ᵐ time ∂(commonTimeMeasure requestedTime),
      (∑ output ∈ integerWaveFrequencyCube (2 * radius),
        actualWholeContinuousPairAggregateNegativeOneDensity
          receipt time output) ≤
        4 * ∫ x in physicalUnitCell,
          velocityDot
            (coarseFilter scale
              (wholeStateVorticityNonlinearNegativeOneOutputField
                (2 * radius) (receipt.wholePath time)))
            (coarseFilter scale
              (wholeStateVorticityNonlinearNegativeOneOutputField
                (2 * radius) (receipt.wholePath time))) x := by
  have radiusRealPos : 0 < (radius : Real) := by
    exact_mod_cast radiusPos
  have outputRadiusPos : 0 < 2 * radius := by
    omega
  have outputScaleRadius :
      scale.radius =
        1 / (6 * Real.pi * ((2 * radius : Nat) : Real)) := by
    rw [scaleRadius]
    field_simp [Real.pi_ne_zero, radiusRealPos.ne']
    push_cast
    ring
  filter_upwards [wholePath_fourierReality_ae receipt] with time reality
  have pairEq :
      (∑ output ∈ integerWaveFrequencyCube (2 * radius),
        actualWholeContinuousPairAggregateNegativeOneDensity
          receipt time output) =
        ∫ x in physicalUnitCell,
          velocityDot
            (wholeStateVorticityNonlinearNegativeOneOutputField
              (2 * radius) (receipt.wholePath time))
            (wholeStateVorticityNonlinearNegativeOneOutputField
              (2 * radius) (receipt.wholePath time)) x := by
    rw [
      physicalUnitCell_wholeStateVorticityNonlinearNegativeOneOutputField_parseval
        (2 * radius) (receipt.wholePath time)
        (wholePath_transverse receipt time) reality]
    apply Finset.sum_congr rfl
    intro output outputMem
    unfold actualWholeContinuousPairAggregateNegativeOneDensity
    rw [tsum_actualWholeContinuousPairVector_eq_nonlinearOutput]
  rw [pairEq]
  exact
    physicalUnitCell_wholeNonlinearNegativeOneOutputField_le_four_mul_coarseFilter
      (2 * radius) outputRadiusPos scale outputScaleRadius
      (receipt.wholePath time) (wholePath_transverse receipt time) reality

/-- One actual receipt selects both its absorbing output radius and the
matching physical coarse scale.  Its exact PDE mass increment is then paid
by the time-integrated coarse observation of the identical nonlinear rows. -/
theorem
    receiptVorticityMass_increment_le_sourceSelectedReciprocalCoarsePhysicalPayment
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (ceiling : Real)
    (ceilingNonneg : 0 ≤ ceiling)
    (massBound :
      ∀ time : Icc (0 : Real) requestedTime,
        wholeVorticityEuclideanMass (receipt.wholePath time) ≤ ceiling) :
    ∃ radius : Nat,
      ∃ scale : CoarseScale,
        0 < radius ∧
        4368 * biotSavartSerrinConstant * ceiling ≤
          (radius : Real) * (nu.coeff ^ 2 * (2 * Real.pi) ^ 2) ∧
        (radius : Real) ≤
          (4368 * biotSavartSerrinConstant * ceiling) /
              (nu.coeff ^ 2 * (2 * Real.pi) ^ 2) + 2 ∧
        scale.radius = 1 / (12 * Real.pi * (radius : Real)) ∧
        nu.coeff *
            (wholeVorticityEuclideanMass
                (receipt.wholePath
                  ⟨requestedTime,
                    ⟨receipt.requestedTimePos.le, le_rfl⟩⟩) -
              wholeVorticityEuclideanMass initialState) ≤
          4 * ∫ time,
            (∫ x in physicalUnitCell,
              velocityDot
                (coarseFilter scale
                  (wholeStateVorticityNonlinearNegativeOneOutputField
                    (2 * radius) (receipt.wholePath time)))
                (coarseFilter scale
                  (wholeStateVorticityNonlinearNegativeOneOutputField
                    (2 * radius) (receipt.wholePath time))) x)
            ∂(commonTimeMeasure requestedTime) := by
  obtain ⟨radius, radiusPos, radiusAbsorbs, radiusUpper, lowPayment⟩ :=
    receiptVorticityMass_increment_le_sourceSelectedLowOutputPayment
      receipt ceiling ceilingNonneg massBound
  have radiusRealPos : 0 < (radius : Real) := by
    exact_mod_cast radiusPos
  let scale : CoarseScale :=
    { radius := 1 / (12 * Real.pi * (radius : Real))
      radius_pos := by positivity }
  let lowMass := fun time : Icc (0 : Real) requestedTime =>
    ∑ output ∈ integerWaveFrequencyCube (2 * radius),
      actualWholeContinuousPairAggregateNegativeOneDensity
        receipt time output
  let physicalMass := fun time : Icc (0 : Real) requestedTime =>
    ∫ x in physicalUnitCell,
      velocityDot
        (coarseFilter scale
          (wholeStateVorticityNonlinearNegativeOneOutputField
            (2 * radius) (receipt.wholePath time)))
        (coarseFilter scale
          (wholeStateVorticityNonlinearNegativeOneOutputField
            (2 * radius) (receipt.wholePath time))) x
  let keptMass := fun time : Icc (0 : Real) requestedTime =>
    ∑ output ∈ integerWaveFrequencyCube (2 * radius),
      complexCoordinateAmplitudeSq
        (coarseCoefficientKeep scale
          (wholeStateVorticityNonlinearNegativeOneWeightedCoefficient
            (receipt.wholePath time)) output)
  have pairDensityContinuous :
      ∀ output : IntegerWavevector,
        Continuous (fun time : Icc (0 : Real) requestedTime =>
          actualWholeContinuousPairAggregateNegativeOneDensity
            receipt time output) := by
    intro output
    have rowContinuous :
        Continuous (fun time : Icc (0 : Real) requestedTime =>
          actualWholeContinuousNonlinearRow receipt output time.1) :=
      (actualWholeContinuousNonlinearRow_continuous receipt output).comp
        continuous_subtype_val
    have sourceContinuous :
        Continuous (fun time : Icc (0 : Real) requestedTime =>
          (integerWaveViscousMultiplier output)⁻¹ *
            complexCoordinateAmplitudeSq
              (actualWholeContinuousNonlinearRow
                receipt output time.1)) :=
      continuous_const.mul
        (complexCoordinateAmplitudeSq_continuous.comp rowContinuous)
    apply sourceContinuous.congr
    intro time
    unfold actualWholeContinuousPairAggregateNegativeOneDensity
    rw [tsum_actualWholeContinuousPairVector_eq_continuousNonlinearRow]
  have lowMassContinuous : Continuous lowMass := by
    unfold lowMass
    exact continuous_finsetSum
      (integerWaveFrequencyCube (2 * radius))
      (fun output _ => pairDensityContinuous output)
  have lowMassIntegrable :
      Integrable lowMass (commonTimeMeasure requestedTime) := by
    simpa only [MeasureTheory.integrableOn_univ] using
      (ContinuousOn.integrableOn_compact isCompact_univ
        lowMassContinuous.continuousOn)
  let transversePath := fun time : Icc (0 : Real) requestedTime =>
    (⟨receipt.wholePath time, wholePath_transverse receipt time⟩ :
      WholeTransverseVorticityState)
  have transversePathContinuous : Continuous transversePath := by
    exact receipt.wholePath.continuous.subtype_mk
      (fun time => wholePath_transverse receipt time)
  have keptCoefficientContinuous :
      ∀ output : IntegerWavevector,
        Continuous (fun time : Icc (0 : Real) requestedTime =>
          coarseCoefficientKeep scale
            (wholeStateVorticityNonlinearNegativeOneWeightedCoefficient
              (receipt.wholePath time)) output) := by
    intro output
    rw [show (fun time : Icc (0 : Real) requestedTime =>
        coarseCoefficientKeep scale
          (wholeStateVorticityNonlinearNegativeOneWeightedCoefficient
            (receipt.wholePath time)) output) =
      (fun time =>
        (coarseCharacterMultiplier scale output : Complex) •
          wholeStateVorticityNonlinearNegativeOneWeightedCoefficient
            (transversePath time).1 output) by
      funext time
      rfl]
    exact
      ((wholeStateVorticityNonlinearNegativeOneWeightedCoefficient_continuous
        output).comp transversePathContinuous).const_smul
          (coarseCharacterMultiplier scale output : Complex)
  have keptMassContinuous : Continuous keptMass := by
    unfold keptMass
    exact continuous_finsetSum
      (integerWaveFrequencyCube (2 * radius))
      (fun output _ =>
        complexCoordinateAmplitudeSq_continuous.comp
          (keptCoefficientContinuous output))
  have keptMassIntegrable :
      Integrable keptMass (commonTimeMeasure requestedTime) := by
    simpa only [MeasureTheory.integrableOn_univ] using
      (ContinuousOn.integrableOn_compact isCompact_univ
        keptMassContinuous.continuousOn)
  have physicalMassEq :
      physicalMass =ᵐ[commonTimeMeasure requestedTime] keptMass := by
    filter_upwards [wholePath_fourierReality_ae receipt] with time reality
    simpa only [keptMass,
      complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq] using
      physicalUnitCell_coarseFilteredWholeNonlinearNegativeOneOutputField_parseval
        (2 * radius) scale (receipt.wholePath time)
        (wholePath_transverse receipt time) reality
  have physicalMassIntegrable :
      Integrable physicalMass (commonTimeMeasure requestedTime) :=
    keptMassIntegrable.congr physicalMassEq.symm
  have pointwise :
      lowMass ≤ᵐ[commonTimeMeasure requestedTime]
        fun time => 4 * physicalMass time := by
    unfold lowMass physicalMass
    exact
      receiptLowOutputPairDensity_le_four_mul_reciprocalCoarsePhysicalDensity_ae
        receipt radius radiusPos scale rfl
  have integrated :
      (∫ time, lowMass time ∂(commonTimeMeasure requestedTime)) ≤
        4 * ∫ time, physicalMass time
          ∂(commonTimeMeasure requestedTime) := by
    have comparison := integral_mono_ae
      lowMassIntegrable (physicalMassIntegrable.const_mul 4) pointwise
    rw [integral_const_mul] at comparison
    exact comparison
  refine ⟨radius, scale, radiusPos, radiusAbsorbs, radiusUpper, rfl, ?_⟩
  exact lowPayment.trans (by
    simpa only [lowMass, physicalMass] using integrated)

/-! ## Parabolic whole-carrier commuting -/

private theorem finiteStateVorticityNonlinearCoefficientAt_real_smul
    (modes : Finset IntegerWavevector)
    (scale : Real)
    (state : ComplexVorticityHilbertState)
    (output : IntegerWavevector) :
    finiteStateVorticityNonlinearCoefficientAt modes
        (scale • state) output =
      ((scale : Complex) ^ 2) •
        finiteStateVorticityNonlinearCoefficientAt modes state output := by
  unfold finiteStateVorticityNonlinearCoefficientAt
  simp_rw [finiteStateVorticityNonlinearPairContribution_real_smul]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro first _
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro second _
  by_cases sumEq : first + second = output <;> simp [sumEq]

private theorem finiteStateVorticityGenerator_apply_parabolicScale
    (modes : Finset IntegerWavevector)
    (viscosity scale : Real)
    (state : ComplexVorticityHilbertState)
    (output : IntegerWavevector) :
    (scale ^ 2 : Real) • ((scale ^ 2 : Real) •
        finiteStateVorticityGenerator modes viscosity state output) =
      if output ∈ modes then
        finiteStateVorticityNonlinearCoefficientAt modes
            ((scale ^ 2 : Real) • state) output -
          (viscosity *
              (scale ^ 2 * integerWaveViscousMultiplier output)) •
            ((scale ^ 2 : Complex) • state output)
      else 0 := by
  rw [finiteStateVorticityGenerator_apply]
  by_cases outputMem : output ∈ modes
  · rw [if_pos outputMem, if_pos outputMem,
      finiteStateVorticityNonlinearCoefficientAt_real_smul]
    simp only [RCLike.real_smul_eq_coe_smul (K := Complex)]
    push_cast
    module
  · simp [outputMem]

/-- Parabolic time and vorticity scaling preserve every actual finite
Galerkin row equation with real frequency `scale * output`. -/
theorem finiteGalerkinTrajectoryWave_hasDerivAt_parabolicScale
    (modes : Finset IntegerWavevector)
    (viscosity scale anchor time : Real)
    (trajectory : Real → ComplexVorticityHilbertState)
    (output : IntegerWavevector)
    (evolves :
      HasDerivAt trajectory
        (finiteStateVorticityGenerator modes viscosity
          (trajectory (anchor + scale ^ 2 * time)))
        (anchor + scale ^ 2 * time)) :
    HasDerivAt
      ((scale ^ 2 : Real) •
        ((fun originalTime => trajectory originalTime output) ∘
          fun scaledTime => anchor + scale ^ 2 * scaledTime))
      (if output ∈ modes then
        finiteStateVorticityNonlinearCoefficientAt modes
            ((scale ^ 2 : Real) •
              trajectory (anchor + scale ^ 2 * time)) output -
          (viscosity *
              (scale ^ 2 * integerWaveViscousMultiplier output)) •
            ((scale ^ 2 : Complex) •
              trajectory (anchor + scale ^ 2 * time) output)
       else 0)
      time := by
  have row :=
    complexVorticityTrajectoryWave_hasDerivAt
      trajectory (anchor + scale ^ 2 * time)
      (finiteStateVorticityGenerator modes viscosity
        (trajectory (anchor + scale ^ 2 * time)))
      output evolves
  have clock :
      HasDerivAt
        (fun scaledTime : Real => anchor + scale ^ 2 * scaledTime)
        (scale ^ 2) time := by
    simpa only [id_eq, mul_one] using
      ((hasDerivAt_id time).const_mul (scale ^ 2)).const_add anchor
  have scaled := (row.scomp time clock).const_smul (scale ^ 2 : Real)
  rw [finiteStateVorticityGenerator_apply_parabolicScale] at scaled
  exact scaled

/-- A unit-periodic finite Fourier state becomes periodic on the expanded
lattice `scale⁻¹ * ℤ³` under the exact parabolic spatial rescaling. -/
theorem finiteRealComplexFourierField_parabolicScale_expandedPeriodic
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState)
    (scale : Real)
    (scalePos : 0 < scale)
    (center : PhysicalSpace)
    (shift : IntegerShift)
    (x : PhysicalSpace) :
    (scale ^ 2 : Real) •
        finiteRealComplexFourierField modes state
          (center + scale • (x + scale⁻¹ • latticeShift shift)) =
      (scale ^ 2 : Real) •
        finiteRealComplexFourierField modes state
          (center + scale • x) := by
  have argumentEq :
      center + scale • (x + scale⁻¹ • latticeShift shift) =
        (center + scale • x) + latticeShift shift := by
    rw [smul_add, smul_smul, mul_inv_cancel₀ scalePos.ne', one_smul]
    abel
  rw [argumentEq,
    finiteRealComplexFourierField_latticePeriodic modes state shift]

private theorem wholeStateVorticityGradientMass_real_smul
    (scale : Real)
    (state : ComplexVorticityHilbertState) :
    wholeStateVorticityGradientMass (scale • state) =
      scale ^ 2 * wholeStateVorticityGradientMass state := by
  have rowScale : ∀ wave : IntegerWavevector,
      integerWaveNormSq wave *
          complexCoordinateAmplitudeSq ((scale • state) wave) =
        scale ^ 2 * (integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (state wave)) := by
    intro wave
    change integerWaveNormSq wave *
      complexCoordinateAmplitudeSq ((scale : Complex) • state wave) = _
    simp only [complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq,
      complexCoordinateVectorNormSq_smul, Complex.normSq_ofReal]
    ring
  unfold wholeStateVorticityGradientMass
  simp_rw [rowScale]
  rw [tsum_mul_left]

/-- Expanded-cell vorticity mass and the time-integrated gradient density
carry the three-dimensional Navier--Stokes parabolic factors `scale` and
`scale³`. -/
theorem wholeVorticityMass_gradient_parabolicScale
    (scale : Real)
    (scalePos : 0 < scale)
    (state : ComplexVorticityHilbertState) :
    (scale ^ 3)⁻¹ *
        wholeVorticityEuclideanMass ((scale ^ 2 : Real) • state) =
        scale * wholeVorticityEuclideanMass state ∧
      (scale ^ 3)⁻¹ * scale ^ 2 *
          wholeStateVorticityGradientMass
            ((scale ^ 2 : Real) • state) =
        scale ^ 3 * wholeStateVorticityGradientMass state := by
  constructor
  · rw [wholeVorticityEuclideanMass_real_smul]
    field_simp [scalePos.ne']
  · rw [wholeStateVorticityGradientMass_real_smul]
    field_simp [scalePos.ne']

private theorem physicalUnitCell_finiteRealComplexFourierField_mass_parseval
    (modes : Finset IntegerWavevector)
    (negClosed : ∀ {wave}, wave ∈ modes → waveNeg wave ∈ modes)
    (state : ComplexVorticityHilbertState)
    (reality : FiniteStateFourierReality state) :
    (∫ x in physicalUnitCell,
      ‖finiteRealComplexFourierField modes state x‖ ^ 2) =
      finiteStateVorticityCoefficientEnstrophy modes state := by
  have parseval :=
    physicalUnitCell_finiteRealComplexFourierField_parseval_of_observer
      modes state (fun wave waveMem => by
        rw [physicalUnitCellComplexFourierCoordinate_finiteRealComplexFourierField]
        funext coordinate
        rw [if_pos waveMem, if_pos (negClosed waveMem), reality wave]
        simp [vectorConj])
  rw [show (∫ x in physicalUnitCell,
      ‖finiteRealComplexFourierField modes state x‖ ^ 2) =
      ∫ x in physicalUnitCell,
        velocityDot
          (finiteRealComplexFourierField modes state)
          (finiteRealComplexFourierField modes state) x by
    apply integral_congr_ae
    filter_upwards with x
    unfold velocityDot
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [pow_two]]
  rw [parseval]
  unfold finiteStateVorticityCoefficientEnstrophy
  apply Finset.sum_congr rfl
  intro wave _
  exact
    (complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq
      (state wave)).symm

/-- Exact physical `L²` mass on the expanded fundamental cell under the
three-dimensional Navier--Stokes parabolic scaling.  This is the physical
Jacobian bridge used to turn a source-generated coefficient tail into a
local physical-space tail; it accepts no tightness or compactness premise. -/
theorem physicalUnitCell_finiteRealComplexFourierField_parabolicScale_mass
    (modes : Finset IntegerWavevector)
    (negClosed : ∀ {wave}, wave ∈ modes → waveNeg wave ∈ modes)
    (state : ComplexVorticityHilbertState)
    (reality : FiniteStateFourierReality state)
    (scale : Real) (scalePos : 0 < scale) :
    (∫ x in scale⁻¹ • physicalUnitCell,
      ‖(scale ^ 2 : Real) •
          finiteRealComplexFourierField modes state (scale • x)‖ ^ 2) =
      scale * finiteStateVorticityCoefficientEnstrophy modes state := by
  let density : PhysicalSpace → Real := fun x =>
    ‖finiteRealComplexFourierField modes state x‖ ^ 2
  have scaledSet :
      scale • (scale⁻¹ • physicalUnitCell) = physicalUnitCell := by
    rw [← mul_smul, mul_inv_cancel₀ scalePos.ne', one_smul]
  have changeVariables := Measure.setIntegral_comp_smul_of_pos
    (volume : Measure PhysicalSpace) density
      (scale⁻¹ • physicalUnitCell) scalePos
  rw [scaledSet] at changeVariables
  have dimension : Module.finrank Real PhysicalSpace = 3 := by
    simp [PhysicalSpace, Coordinate]
  have rawIntegral :
      (∫ x in scale⁻¹ • physicalUnitCell, density (scale • x)) =
        (scale ^ 3)⁻¹ *
          ∫ x in physicalUnitCell, density x := by
    simpa [dimension, smul_eq_mul] using changeVariables
  have scaleSqNonneg : 0 ≤ scale ^ 2 := sq_nonneg scale
  calc
    (∫ x in scale⁻¹ • physicalUnitCell,
      ‖(scale ^ 2 : Real) •
          finiteRealComplexFourierField modes state (scale • x)‖ ^ 2) =
        scale ^ 4 *
          ∫ x in scale⁻¹ • physicalUnitCell,
            density (scale • x) := by
      rw [← MeasureTheory.integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      dsimp only [density]
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg scaleSqNonneg]
      ring
    _ = scale ^ 4 * ((scale ^ 3)⁻¹ *
          ∫ x in physicalUnitCell, density x) := by rw [rawIntegral]
    _ = scale * ∫ x in physicalUnitCell, density x := by
      field_simp [scalePos.ne']
    _ = scale * finiteStateVorticityCoefficientEnstrophy modes state := by
      rw [physicalUnitCell_finiteRealComplexFourierField_mass_parseval
        modes negClosed state reality]

/-- Exact scaled `L²` mass on the expanded fundamental cell naturally
recentered at an arbitrary physical point.  The affine preimage is the cell
on which `x ↦ center + scale • x` lands in `physicalUnitCell`; translation
invariance of Haar volume keeps the identity independent of `center`. -/
theorem physicalUnitCell_finiteRealComplexFourierField_centeredParabolicScale_mass
    (modes : Finset IntegerWavevector)
    (negClosed : ∀ {wave}, wave ∈ modes → waveNeg wave ∈ modes)
    (state : ComplexVorticityHilbertState)
    (reality : FiniteStateFourierReality state)
    (scale : Real) (scalePos : 0 < scale)
    (center : PhysicalSpace) :
    (∫ x in
        (fun x : PhysicalSpace => x + scale⁻¹ • center) ⁻¹'
          (scale⁻¹ • physicalUnitCell),
      ‖(scale ^ 2 : Real) •
          finiteRealComplexFourierField modes state
            (center + scale • x)‖ ^ 2) =
      scale * finiteStateVorticityCoefficientEnstrophy modes state := by
  let shift : PhysicalSpace := scale⁻¹ • center
  let baseDensity : PhysicalSpace → Real := fun x =>
    ‖(scale ^ 2 : Real) •
      finiteRealComplexFourierField modes state (scale • x)‖ ^ 2
  let translate : PhysicalSpace ≃ᵐ PhysicalSpace :=
    MeasurableEquiv.addRight shift
  have translatePreserving :
      MeasurePreserving
        (translate : PhysicalSpace → PhysicalSpace) volume volume := by
    simpa [translate] using measurePreserving_add_right volume shift
  have translatedIntegral :=
    translatePreserving.setIntegral_preimage_emb
      translate.measurableEmbedding baseDensity
      (scale⁻¹ • physicalUnitCell)
  have argumentEq : ∀ x : PhysicalSpace,
      scale • (x + shift) = center + scale • x := by
    intro x
    dsimp only [shift]
    rw [smul_add, smul_smul, mul_inv_cancel₀ scalePos.ne', one_smul]
    abel
  change
    (∫ x in
        (fun x : PhysicalSpace => x + shift) ⁻¹'
          (scale⁻¹ • physicalUnitCell),
      ‖(scale ^ 2 : Real) •
          finiteRealComplexFourierField modes state
            (center + scale • x)‖ ^ 2) = _
  calc
    _ = ∫ x in
          (fun x : PhysicalSpace => x + shift) ⁻¹'
            (scale⁻¹ • physicalUnitCell),
        baseDensity (x + shift) := by
      apply setIntegral_congr_fun
      · exact (MeasurableSet.const_smul_of_ne_zero
          physicalUnitCell_isCompact.measurableSet
          (inv_ne_zero scalePos.ne')).preimage
            (measurable_id.add measurable_const)
      · intro x _
        simp only [baseDensity, argumentEq]
    _ = ∫ x in scale⁻¹ • physicalUnitCell, baseDensity x := by
      simpa [translate] using translatedIntegral
    _ = scale * finiteStateVorticityCoefficientEnstrophy modes state := by
      simpa [baseDensity] using
        physicalUnitCell_finiteRealComplexFourierField_parabolicScale_mass
          modes negClosed state reality scale scalePos

/-- Finite-input/output nonlinear `H⁻¹` action on the expanded physical cell
is exactly `scale` times the original actual action. -/
theorem finiteInputOutputNonlinearAction_parabolicScale
    (inputModes outputModes : Finset IntegerWavevector)
    (path : Real → ComplexVorticityHilbertState)
    (anchor terminal scale : Real)
    (scalePos : 0 < scale) :
    (∫ scaledTime in 0..(terminal - anchor) / scale ^ 2,
      ∑ output ∈ outputModes,
        (scale ^ 3)⁻¹ *
          (scale ^ 2 * integerWaveViscousMultiplier output)⁻¹ *
            complexCoordinateAmplitudeSq
              (finiteStateVorticityNonlinearCoefficientAt inputModes
                ((scale ^ 2 : Real) •
                  path (anchor + scale ^ 2 * scaledTime))
                output)) =
      scale *
        ∫ originalTime in anchor..terminal,
          ∑ output ∈ outputModes,
            (integerWaveViscousMultiplier output)⁻¹ *
              complexCoordinateAmplitudeSq
                (finiteStateVorticityNonlinearCoefficientAt inputModes
                  (path originalTime) output) := by
  let density : Real → Real := fun originalTime =>
    ∑ output ∈ outputModes,
      (integerWaveViscousMultiplier output)⁻¹ *
        complexCoordinateAmplitudeSq
          (finiteStateVorticityNonlinearCoefficientAt inputModes
            (path originalTime) output)
  have densityEq :
      (fun scaledTime =>
        ∑ output ∈ outputModes,
          (scale ^ 3)⁻¹ *
            (scale ^ 2 * integerWaveViscousMultiplier output)⁻¹ *
              complexCoordinateAmplitudeSq
                (finiteStateVorticityNonlinearCoefficientAt inputModes
                  ((scale ^ 2 : Real) •
                    path (anchor + scale ^ 2 * scaledTime))
                  output)) =
        fun scaledTime =>
          scale ^ 3 * density (anchor + scale ^ 2 * scaledTime) := by
    funext scaledTime
    dsimp only [density]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro output _
    rw [finiteStateVorticityNonlinearCoefficientAt_real_smul]
    simp only [complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq,
      complexCoordinateVectorNormSq_smul]
    push_cast
    simp only [map_pow, Complex.normSq_ofReal]
    field_simp [scalePos.ne']
  rw [densityEq]
  have changeVariables :=
    intervalIntegral.smul_integral_comp_add_mul
      (f := density) (a := 0)
      (b := (terminal - anchor) / scale ^ 2)
      (c := scale ^ 2) anchor
  have terminalEq :
      anchor + scale ^ 2 * ((terminal - anchor) / scale ^ 2) =
        terminal := by
    field_simp [scalePos.ne']
    ring
  have changeVariables' :
      scale ^ 2 *
          ∫ scaledTime in 0..(terminal - anchor) / scale ^ 2,
            density (anchor + scale ^ 2 * scaledTime) =
        ∫ originalTime in anchor..terminal, density originalTime := by
    simpa only [smul_eq_mul, mul_zero, add_zero, terminalEq] using
      changeVariables
  calc
    (∫ scaledTime in 0..(terminal - anchor) / scale ^ 2,
      scale ^ 3 * density (anchor + scale ^ 2 * scaledTime)) =
        scale ^ 3 *
          ∫ scaledTime in 0..(terminal - anchor) / scale ^ 2,
            density (anchor + scale ^ 2 * scaledTime) := by
      rw [intervalIntegral.integral_const_mul]
    _ = scale * (scale ^ 2 *
          ∫ scaledTime in 0..(terminal - anchor) / scale ^ 2,
            density (anchor + scale ^ 2 * scaledTime)) := by ring
    _ = scale *
        ∫ originalTime in anchor..terminal, density originalTime := by
      rw [changeVariables']
    _ = scale *
        ∫ originalTime in anchor..terminal,
          ∑ output ∈ outputModes,
            (integerWaveViscousMultiplier output)⁻¹ *
              complexCoordinateAmplitudeSq
                (finiteStateVorticityNonlinearCoefficientAt inputModes
                  (path originalTime) output) := by rfl

/-! ## Whole-receipt physical-band time modulus -/

/-- One nonzero row of an actual whole mild receipt has the same sharp
time-increment bound as its source Galerkin approximants.  The proof uses
the receipt's own absolutely-continuous row extension and whole-tangent
write, so no finite projection is treated as an autonomous trajectory. -/
theorem receiptWave_timeIncrement_sq_le_wholeTangentRow
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (wave : IntegerWavevector)
    (waveNe : wave ≠ 0)
    (a b : Icc (0 : Real) requestedTime)
    (hab : a.1 ≤ b.1) :
    ‖receipt.wholePath b wave - receipt.wholePath a wave‖ ^ 2 ≤
      (b.1 - a.1) * integerWaveViscousMultiplier wave *
        ‖fixedWaveSpaceTimeRestriction
            requestedTime wave receipt.wholeTangent‖ ^ 2 := by
  let rowExtension : Real → ComplexCoordinateVector :=
    commonTimeZeroExtension requestedTime
      (receipt.rowTangent wave waveNe)
  let wholeTangentRow :=
    fixedWaveSpaceTimeRestriction
      requestedTime wave receipt.wholeTangent
  have wholeTangentRowIntegrable :
      Integrable
        (fun time : Icc (0 : Real) requestedTime =>
          wholeTangentRow time)
        (commonTimeMeasure requestedTime) := by
    have onUniv :=
      integrableOn_Lp_of_measure_ne_top
        wholeTangentRow fact_one_le_two_ennreal.elim
        (measure_ne_top (commonTimeMeasure requestedTime) Set.univ)
    simpa only [integrableOn_univ] using onUniv
  have rowTangentIntegrable :
      Integrable
        (receipt.rowTangent wave waveNe)
        (commonTimeMeasure requestedTime) := by
    have scaledIntegrable :=
      Integrable.smul
        (Real.sqrt (integerWaveViscousMultiplier wave) : Complex)
        wholeTangentRowIntegrable
    apply scaledIntegrable.congr
    filter_upwards [
      fixedWaveSpaceTimeRestriction_coeFn
        requestedTime wave receipt.wholeTangent,
      receipt.rowTangent_eq_wholeTangent_ae wave waveNe] with
        time wholeRowEq tangentEq
    change
      (Real.sqrt (integerWaveViscousMultiplier wave) : Complex) •
          wholeTangentRow time =
        receipt.rowTangent wave waveNe time
    rw [wholeRowEq]
    exact tangentEq
  have rowTangentNormSqIntegrable :
      Integrable
        (fun time : Icc (0 : Real) requestedTime =>
          ‖receipt.rowTangent wave waveNe time‖ ^ 2)
        (commonTimeMeasure requestedTime) := by
    let scaledRow :
        MeasureTheory.Lp ComplexCoordinateVector 2
          (commonTimeMeasure requestedTime) :=
      (Real.sqrt (integerWaveViscousMultiplier wave) : Complex) •
        wholeTangentRow
    have scaledNormSqIntegrable :
        Integrable
          (fun time : Icc (0 : Real) requestedTime =>
            ‖scaledRow time‖ ^ 2)
          (commonTimeMeasure requestedTime) :=
      (MeasureTheory.Lp.memLp scaledRow).integrable_norm_pow (by norm_num)
    apply scaledNormSqIntegrable.congr
    filter_upwards [
      fixedWaveSpaceTimeRestriction_coeFn
        requestedTime wave receipt.wholeTangent,
      receipt.rowTangent_eq_wholeTangent_ae wave waveNe,
      MeasureTheory.Lp.coeFn_smul
        (Real.sqrt (integerWaveViscousMultiplier wave) : Complex)
        wholeTangentRow] with time wholeRowEq tangentEq scaledEq
    rw [scaledEq]
    change
      ‖(Real.sqrt (integerWaveViscousMultiplier wave) : Complex) •
          wholeTangentRow time‖ ^ 2 =
        ‖receipt.rowTangent wave waveNe time‖ ^ 2
    rw [wholeRowEq]
    exact congrArg (fun row : ComplexCoordinateVector => ‖row‖ ^ 2) tangentEq
  have rowExtensionIntegrable :
      IntervalIntegrable rowExtension volume 0 requestedTime :=
    commonTimeZeroExtension_intervalIntegrable_of_integrable
      requestedTime receipt.requestedTimePos.le
      (receipt.rowTangent wave waveNe) rowTangentIntegrable
  have rowExtensionNormSqIntegrable :
      IntervalIntegrable
        (fun time => ‖rowExtension time‖ ^ 2)
        volume 0 requestedTime := by
    have generated :=
      commonTimeZeroExtension_intervalIntegrable_of_integrable
        requestedTime receipt.requestedTimePos.le
        (fun time : Icc (0 : Real) requestedTime =>
          ‖receipt.rowTangent wave waveNe time‖ ^ 2)
        rowTangentNormSqIntegrable
    apply generated.congr
    intro time _timeMem
    by_cases timeMem : time ∈ Icc (0 : Real) requestedTime <;>
      simp [rowExtension, commonTimeZeroExtension, timeMem]
  have aMemU : a.1 ∈ uIcc (0 : Real) requestedTime := by
    simpa [uIcc_of_le receipt.requestedTimePos.le] using a.2
  have bMemU : b.1 ∈ uIcc (0 : Real) requestedTime := by
    simpa [uIcc_of_le receipt.requestedTimePos.le] using b.2
  have abSubset : uIcc a.1 b.1 ⊆ uIcc (0 : Real) requestedTime :=
    uIcc_subset_uIcc aMemU bMemU
  have rowExtensionIntegrableAB :
      IntervalIntegrable rowExtension volume a.1 b.1 :=
    rowExtensionIntegrable.mono_set abSubset
  have rowExtensionNormSqIntegrableAB :
      IntervalIntegrable
        (fun time => ‖rowExtension time‖ ^ 2)
        volume a.1 b.1 :=
    rowExtensionNormSqIntegrable.mono_set abSubset
  have derivativeAB :
      ∀ᵐ time : Real,
        time ∈ uIcc a.1 b.1 →
          HasDerivAt (receipt.rowExtension wave waveNe)
            (rowExtension time) time := by
    filter_upwards [receipt.rowExtension_ae_hasDerivAt wave waveNe] with
      time derivative
    intro timeMem
    exact derivative (abSubset timeMem)
  have update :=
    path_sub_eq_intervalIntegral
      ((receipt.rowExtension_absolutelyContinuous wave waveNe).mono abSubset)
      rowExtensionIntegrableAB derivativeAB b.1 right_mem_uIcc
  rw [receipt.rowExtension_on_interval wave waveNe b,
    receipt.rowExtension_on_interval wave waveNe a] at update
  let μ : Measure Real := volume.restrict (Ioc a.1 b.1)
  have rowIntegrableOn : Integrable rowExtension μ := by
    change IntegrableOn rowExtension (Ioc a.1 b.1) volume
    simpa only [uIoc_of_le hab] using rowExtensionIntegrableAB.def'
  have rowNormSqIntegrableOn :
      Integrable (fun time => ‖rowExtension time‖ ^ 2) μ := by
    change IntegrableOn
      (fun time => ‖rowExtension time‖ ^ 2) (Ioc a.1 b.1) volume
    simpa only [uIoc_of_le hab] using
      rowExtensionNormSqIntegrableAB.def'
  have normMemLp :
      MemLp (fun time => ‖rowExtension time‖) 2 μ :=
    (MeasureTheory.memLp_two_iff_integrable_sq
      rowIntegrableOn.norm.aestronglyMeasurable).mpr
        rowNormSqIntegrableOn
  have rowMemLp : MemLp rowExtension 2 μ :=
    (MeasureTheory.memLp_norm_iff
      rowIntegrableOn.aestronglyMeasurable).mp normMemLp
  have cauchy :=
    norm_integral_sq_le_measureReal_mul_integral_norm_sq
      rowExtension rowMemLp
  have measureReal : μ.real Set.univ = b.1 - a.1 := by
    dsimp [μ]
    rw [measureReal_def, Measure.restrict_apply_univ, Real.volume_Ioc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]
  have subIntegralLeFull :
      (∫ time in a.1..b.1, ‖rowExtension time‖ ^ 2) ≤
        ∫ time in (0 : Real)..requestedTime,
          ‖rowExtension time‖ ^ 2 := by
    apply intervalIntegral.integral_mono_interval
    · exact a.2.1
    · exact hab
    · exact b.2.2
    · exact Filter.Eventually.of_forall fun time => sq_nonneg _
    · exact rowExtensionNormSqIntegrable
  have fullIntegralEq :
      (∫ time in (0 : Real)..requestedTime,
          ‖rowExtension time‖ ^ 2) =
        integerWaveViscousMultiplier wave *
          ‖wholeTangentRow‖ ^ 2 := by
    rw [← commonTime_integral_eq_intervalIntegral
      requestedTime receipt.requestedTimePos.le]
    rw [fixedWaveSpaceTimeState_norm_sq_eq_integral, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [
      fixedWaveSpaceTimeRestriction_coeFn
        requestedTime wave receipt.wholeTangent,
      receipt.rowTangent_eq_wholeTangent_ae wave waveNe] with
        time wholeRowEq tangentEq
    have extensionEq :
        rowExtension time.1 = receipt.rowTangent wave waveNe time := by
      unfold rowExtension
      exact commonTimeZeroExtension_of_mem
        requestedTime (receipt.rowTangent wave waveNe) time.1 time.2
    rw [extensionEq, ← tangentEq, norm_smul, mul_pow]
    rw [wholeRowEq]
    have multiplierNonneg : 0 ≤ integerWaveViscousMultiplier wave := by
      unfold integerWaveViscousMultiplier
      exact mul_nonneg (sq_nonneg _) (integerWaveNormSq_nonneg wave)
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt multiplierNonneg]
  rw [update, intervalIntegral.integral_of_le hab]
  change ‖∫ time, rowExtension time ∂μ‖ ^ 2 ≤ _
  calc
    ‖∫ time, rowExtension time ∂μ‖ ^ 2 ≤
        μ.real Set.univ *
          ∫ time, ‖rowExtension time‖ ^ 2 ∂μ := cauchy
    _ = (b.1 - a.1) *
          ∫ time in a.1..b.1, ‖rowExtension time‖ ^ 2 := by
      rw [measureReal, intervalIntegral.integral_of_le hab]
    _ ≤ (b.1 - a.1) *
          (integerWaveViscousMultiplier wave *
            ‖wholeTangentRow‖ ^ 2) := by
      gcongr
      exact subIntegralLeFull.trans_eq fullIntegralEq
    _ = (b.1 - a.1) * integerWaveViscousMultiplier wave *
        ‖wholeTangentRow‖ ^ 2 := by ring

theorem receiptWholeTangentSquare_le_euclideanSquare
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime) :
    ‖receipt.wholeTangent‖ ^ 2 ≤
      puncturedEuclideanSpaceTimeSquare receipt.wholeTangent := by
  have mappedAE :=
    puncturedEuclideanSpaceTimeState_apply_ae receipt.wholeTangent
  have pointwiseNormLe :
      ∀ᵐ time ∂(commonTimeMeasure requestedTime),
        ‖receipt.wholeTangent time‖ ≤
          ‖puncturedEuclideanSpaceTimeState
            receipt.wholeTangent time‖ := by
    filter_upwards [mappedAE,
      receiptWholeTangent_zero_row_ae receipt] with
        time mappedEq zeroRow
    rw [mappedEq]
    have squareLe :=
      state_norm_sq_le_puncturedEuclideanize_of_zero_row
        (receipt.wholeTangent time) zeroRow
    nlinarith [norm_nonneg (receipt.wholeTangent time),
      norm_nonneg (puncturedEuclideanize (receipt.wholeTangent time))]
  have normLe := MeasureTheory.Lp.norm_le_norm_of_ae_le pointwiseNormLe
  unfold puncturedEuclideanSpaceTimeSquare
  nlinarith [norm_nonneg receipt.wholeTangent,
    norm_nonneg
      (puncturedEuclideanSpaceTimeState receipt.wholeTangent)]

/-- A finite physical frequency band of one actual whole mild receipt has a
time modulus controlled by the largest multiplier in the band, not by the
sum of its multipliers.  The estimate is taken directly on the whole receipt
rows, and its right side is the same complete Euclidean tangent write used by
the source ledger. -/
theorem receiptFiniteInventory_timeIncrement_euclideanSq_le_multiplierCeiling
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (observed : Finset IntegerWavevector)
    (observedZeroFree : ∀ wave ∈ observed, wave ≠ 0)
    (multiplierCeiling : Real)
    (multiplierCeilingNonneg : 0 ≤ multiplierCeiling)
    (multiplierLe :
      ∀ wave ∈ observed,
        integerWaveViscousMultiplier wave ≤ multiplierCeiling)
    (a b : Icc (0 : Real) requestedTime)
    (hab : a.1 ≤ b.1) :
    (∑ wave ∈ observed,
        complexCoordinateAmplitudeSq
          (receipt.wholePath b wave - receipt.wholePath a wave)) ≤
      3 * (b.1 - a.1) * multiplierCeiling *
        puncturedEuclideanSpaceTimeSquare receipt.wholeTangent := by
  have timeNonneg : 0 ≤ b.1 - a.1 := sub_nonneg.mpr hab
  have restrictionSummable :
      Summable fun wave : IntegerWavevector =>
        ‖fixedWaveSpaceTimeRestriction
          requestedTime wave receipt.wholeTangent‖ ^ 2 :=
    summable_fixedWaveSpaceTimeRestriction_norm_sq
      requestedTime receipt.wholeTangent
  have finiteRestrictionLe :
      (∑ wave ∈ observed,
          ‖fixedWaveSpaceTimeRestriction
            requestedTime wave receipt.wholeTangent‖ ^ 2) ≤
        ‖receipt.wholeTangent‖ ^ 2 := by
    calc
      (∑ wave ∈ observed,
          ‖fixedWaveSpaceTimeRestriction
            requestedTime wave receipt.wholeTangent‖ ^ 2) ≤
          ∑' wave : IntegerWavevector,
            ‖fixedWaveSpaceTimeRestriction
              requestedTime wave receipt.wholeTangent‖ ^ 2 :=
        restrictionSummable.sum_le_tsum observed
          (fun wave waveMem => sq_nonneg _)
      _ = ‖receipt.wholeTangent‖ ^ 2 := by
        rw [tsum_fixedWaveSpaceTimeRestriction_norm_sq]
  have pointwise (wave : IntegerWavevector) (waveMem : wave ∈ observed) :
      complexCoordinateAmplitudeSq
          (receipt.wholePath b wave - receipt.wholePath a wave) ≤
        3 * ((b.1 - a.1) * multiplierCeiling *
          ‖fixedWaveSpaceTimeRestriction
            requestedTime wave receipt.wholeTangent‖ ^ 2) := by
    have amplitudeLe :=
      complexCoordinateAmplitudeSq_le_three_mul_norm_sq
        (receipt.wholePath b wave - receipt.wholePath a wave)
    have rowLe :=
      receiptWave_timeIncrement_sq_le_wholeTangentRow
        receipt wave (observedZeroFree wave waveMem) a b hab
    have multiplierNonneg :
        0 ≤ integerWaveViscousMultiplier wave := by
      unfold integerWaveViscousMultiplier
      exact mul_nonneg (sq_nonneg _) (integerWaveNormSq_nonneg wave)
    calc
      complexCoordinateAmplitudeSq
          (receipt.wholePath b wave - receipt.wholePath a wave) ≤
          3 * ‖receipt.wholePath b wave -
            receipt.wholePath a wave‖ ^ 2 := amplitudeLe
      _ ≤ 3 * ((b.1 - a.1) *
          integerWaveViscousMultiplier wave *
            ‖fixedWaveSpaceTimeRestriction
              requestedTime wave receipt.wholeTangent‖ ^ 2) := by
        gcongr
      _ ≤ 3 * ((b.1 - a.1) * multiplierCeiling *
          ‖fixedWaveSpaceTimeRestriction
            requestedTime wave receipt.wholeTangent‖ ^ 2) := by
        gcongr
        exact multiplierLe wave waveMem
  calc
    (∑ wave ∈ observed,
        complexCoordinateAmplitudeSq
          (receipt.wholePath b wave - receipt.wholePath a wave)) ≤
        ∑ wave ∈ observed,
          3 * ((b.1 - a.1) * multiplierCeiling *
            ‖fixedWaveSpaceTimeRestriction
              requestedTime wave receipt.wholeTangent‖ ^ 2) := by
      exact Finset.sum_le_sum fun wave waveMem => pointwise wave waveMem
    _ = 3 * (b.1 - a.1) * multiplierCeiling *
        (∑ wave ∈ observed,
          ‖fixedWaveSpaceTimeRestriction
            requestedTime wave receipt.wholeTangent‖ ^ 2) := by
      rw [Finset.mul_sum]
      ring_nf
    _ ≤ 3 * (b.1 - a.1) * multiplierCeiling *
        ‖receipt.wholeTangent‖ ^ 2 := by
      gcongr
    _ ≤ 3 * (b.1 - a.1) * multiplierCeiling *
        puncturedEuclideanSpaceTimeSquare receipt.wholeTangent := by
      gcongr
      exact receiptWholeTangentSquare_le_euclideanSquare receipt

end FullFrameBoundaryVorticityCofinalNonlinearNegativeOneEuclideanBalance
end GeneratedInfiniteWholeRestartEndpointMacroLineage

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
end NavierStokes
end SaturationMonoid
