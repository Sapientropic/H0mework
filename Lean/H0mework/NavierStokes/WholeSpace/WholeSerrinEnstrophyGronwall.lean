import H0mework.NavierStokes.Fourier.WholeNonlinearDifferenceNegativeOne
import H0mework.NavierStokes.Restart.HalfCriticalComponentGluing
import H0mework.NavierStokes.Restart.PositiveOutputWorkDualBudget
import H0mework.NavierStokes.ShellSources.WholeReceiptEnergyWriteBack

/-!
# Whole-carrier Serrin control of vorticity enstrophy

The nonlinear-difference estimate already lives on the complete weighted
`H⁻¹` carrier.  Specializing its second state to zero gives the exact
cutoff-free estimate needed by the whole unforced receipt:

```text
‖N(ω)‖_H⁻¹² ≤ 8 * U(ω)² * ‖ω‖₂².
```

The velocity majorant, vorticity mass, and nonlinear row all belong to the
same whole Fourier state.  No shell cutoff, critical margin, coefficient
ceiling, continuation witness, or target endpoint enters the theorem mouth.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientWholeSerrinEnstrophyGronwall

open scoped BigOperators ENNReal Topology Interval

open Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinAmbientNorm
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientInfiniteNonlinearNegativeSobolev
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeCriticalSerrin
open
  ThreeDimensionalVorticityCoefficientWholeSpaceTimeGradientLowerSemicontinuity
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeNonlinearNegativeOne
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeViscousNegativeOne
open ThreeDimensionalVorticityCoefficientWholeNonlinearDifferenceNegativeOne
open ThreeDimensionalVorticityCoefficientTransverseSpaceTimeNonlinearRow
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEnstrophyWork
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPreQuotientNonlinearWork
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPositiveOutputWorkDualBudget
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellWholeReceiptEnergyWriteBack
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartHalfCriticalComponentGluing

noncomputable section

private theorem zero_whole_gradient_summable :
    Summable fun wave : IntegerWavevector =>
      integerWaveNormSq wave *
        complexCoordinateAmplitudeSq
          ((0 : ComplexVorticityHilbertState) wave) := by
  simp [complexCoordinateAmplitudeSq]

/-- The actual whole nonlinear tangent is controlled by the identical
state's velocity Serrin density and vorticity mass.  This is the zero-state
specialization of the already completed nonlinear-difference carrier, not a
new finite-mode estimate. -/
theorem wholeStateVorticityNonlinearNegativeOneMass_le_velocitySerrin
    (state : ComplexVorticityHilbertState)
    (stateTransverse : WholeStateTransverse state)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (state wave)) :
    wholeStateVorticityNonlinearNegativeOneMass state ≤
      8 * wholeStateVelocityMajorant state ^ 2 *
        wholeVorticityEuclideanMass state := by
  have differenceGradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq ((state - 0) wave) :=
    summable_wholeStateVorticityGradientDensity_sub
      state 0 gradientSummable zero_whole_gradient_summable
  have differenceBound :=
    wholeStateVorticityNonlinearDifferenceNegativeOneMass_le
      state 0 stateTransverse wholeStateTransverse_zero
      gradientSummable zero_whole_gradient_summable
      differenceGradientSummable
  have zeroMass :
      wholeVorticityEuclideanMass
        (0 : ComplexVorticityHilbertState) = 0 := by
    simp [wholeVorticityEuclideanMass, vorticityRowAmplitude,
      complexCoordinateAmplitudeSq]
  convert differenceBound using 1
  · unfold wholeStateVorticityNonlinearDifferenceNegativeOneMass
      wholeStateVorticityNonlinearNegativeOneMass
    apply tsum_congr
    intro output
    simp [wholeStateVorticityNonlinearDifferenceNegativeOneDensity,
      wholeStateVorticityNonlinearNegativeOneDensity,
      wholeStateVorticityNonlinearCoefficientAt,
      finiteStateVorticityNonlinearPairContribution]
  · simp [wholeStateVelocityMajorant, zeroMass]
    ring

/-- On one actual unforced whole receipt, the cutoff-free nonlinear
`H⁻¹` estimate is read on the identical common-time representative.  In
particular, its velocity factor is literally the receipt's intrinsic Serrin
density; no independently selected path representative occurs. -/
theorem wholeReceiptNonlinearNegativeOneMass_ae_le_velocitySerrin
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime) :
    ∀ᵐ time ∂(commonTimeMeasure requestedTime),
      wholeStateVorticityNonlinearNegativeOneMass
          (receipt.transverseLimit time).1 ≤
        8 * receipt.serrinDensity time *
          wholeVorticityEuclideanMass
            (receipt.wholePath time) := by
  have pathToLpAE :=
    BoundedContinuousFunction.coeFn_toLp
      (p := (2 : ℝ≥0∞))
      (μ := commonTimeMeasure requestedTime) ℂ receipt.wholePath
  filter_upwards [
    receiptPointwiseGradient_ae_summable receipt,
    receiptStateLimit_eq_wholePath_ae receipt,
    receipt.wholePath_eq_transverse_ae,
    pathToLpAE] with
      time gradientSummable stateEq transverseEq pathToLpEq
  have transverseGradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq
            ((receipt.transverseLimit time).1 wave) := by
    simpa only [stateEq, transverseEq] using gradientSummable
  have nonlinearBound :=
    wholeStateVorticityNonlinearNegativeOneMass_le_velocitySerrin
      (receipt.transverseLimit time).1
      (receipt.transverseLimit time).2
      transverseGradientSummable
  simpa only [WholeContinuousMildSerrinReceipt.serrinDensity,
    pathToLpEq, transverseEq] using nonlinearBound

/-- The intrinsic mass of a continuous whole path is continuous on its
actual compact common-time carrier. -/
theorem wholeReceiptVorticityMass_continuous
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime) :
    Continuous fun time =>
      wholeVorticityEuclideanMass (receipt.wholePath time) := by
  have pathIdentity :
      (fun time =>
        wholeVorticityEuclideanMass (receipt.wholePath time)) =
      (fun time =>
        ∑ coordinate : Coordinate,
          ‖wholeStateCoordinateSliceCLM coordinate
            (receipt.wholePath time)‖ ^ 2) := by
    funext time
    exact wholeVorticityEuclideanMass_eq_coordinateSlices _
  rw [pathIdentity]
  fun_prop

/-- The continuous actual path itself generates a finite vorticity-mass
ceiling.  It is used only to install the already generated nonlinearity in
the time-`L² H⁻¹` carrier. -/
def wholeReceiptVorticityMassCeiling
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime) : ℝ :=
  3 * ‖receipt.wholePath‖ ^ 2

theorem wholeReceiptVorticityMassCeiling_nonneg
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime) :
    0 ≤ wholeReceiptVorticityMassCeiling receipt := by
  unfold wholeReceiptVorticityMassCeiling
  positivity

theorem wholeReceiptVorticityMass_le_ceiling
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime)
    (time : Set.Icc (0 : ℝ) requestedTime) :
    wholeVorticityEuclideanMass (receipt.wholePath time) ≤
      wholeReceiptVorticityMassCeiling receipt := by
  have pathNormLe : ‖receipt.wholePath time‖ ≤ ‖receipt.wholePath‖ :=
    receipt.wholePath.norm_coe_le_norm time
  have pathNormSqLe :
      ‖receipt.wholePath time‖ ^ 2 ≤ ‖receipt.wholePath‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 pathNormLe
  exact
    (wholeVorticityEuclideanMass_le_three_mul_norm_sq
      (receipt.wholePath time)).trans <|
      mul_le_mul_of_nonneg_left pathNormSqLe
        (by norm_num : (0 : ℝ) ≤ 3)

theorem wholeReceiptSerrinDensity_mul_vorticityMass_integrable
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime) :
    Integrable
      (fun time => receipt.serrinDensity time *
        wholeVorticityEuclideanMass (receipt.wholePath time))
      (commonTimeMeasure requestedTime) := by
  have massMeasurable :
      AEStronglyMeasurable
        (fun time =>
          wholeVorticityEuclideanMass (receipt.wholePath time))
        (commonTimeMeasure requestedTime) :=
    (wholeReceiptVorticityMass_continuous receipt).aestronglyMeasurable
  apply receipt.serrinDensity_integrable.mul_bdd
    (c := wholeReceiptVorticityMassCeiling receipt) massMeasurable
  filter_upwards with time
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · exact wholeReceiptVorticityMass_le_ceiling receipt time
  · unfold wholeVorticityEuclideanMass
    exact tsum_nonneg fun wave => sq_nonneg _

theorem wholeReceiptTransverseVorticityMass_ae_le_ceiling
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime) :
    ∀ᵐ time ∂(commonTimeMeasure requestedTime),
      wholeVorticityEuclideanMass
          (receipt.transverseLimit time).1 ≤
        wholeReceiptVorticityMassCeiling receipt := by
  filter_upwards [receipt.wholePath_eq_transverse_ae] with
      time pathEq
  rw [← pathEq]
  exact wholeReceiptVorticityMass_le_ceiling receipt time

/-- The nonlinear state recovered from the receipt's unforced update is
exactly the canonical whole `L²_t H⁻¹_x` nonlinearity.  The temporary mass
ceiling is generated by the receipt's own continuous path and does not occur
in the conclusion. -/
theorem receiptNonlinearNegativeOneState_eq_canonicalWholeNonlinearity
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime) :
    receiptNonlinearNegativeOneState receipt =
      wholeSpaceTimeNonlinearNegativeOneState
        receipt.transverseLimit
        (by
          simpa only [receipt.stateLimit_eq_transverse] using
            receipt.gradient_summable)
        (wholeReceiptVorticityMassCeiling_nonneg receipt)
        (wholeReceiptTransverseVorticityMass_ae_le_ceiling receipt) := by
  apply MeasureTheory.Lp.ext
  have sumAE :=
    MeasureTheory.Lp.coeFn_add
      receipt.wholeTangent
      (receiptViscousNegativeOneState receipt)
  have viscousAE :=
    wholeSpaceTimeViscousNegativeOneState_coeFn
      ν.coeff receipt.stateLimit receipt.gradient_summable
      (receiptPointwiseGradient_ae_summable receipt)
  have nonlinearAE :=
    wholeSpaceTimeNonlinearNegativeOneState_coeFn
      receipt.transverseLimit
      (by
        simpa only [receipt.stateLimit_eq_transverse] using
          receipt.gradient_summable)
      (wholeReceiptVorticityMassCeiling_nonneg receipt)
      (wholeReceiptTransverseVorticityMass_ae_le_ceiling receipt)
  filter_upwards [sumAE, receipt.wholeTangent_eq_unforced_ae,
      viscousAE, nonlinearAE] with
      time sumEq tangentEq viscousEq nonlinearEq
  rw [receiptNonlinearNegativeOneState, sumEq]
  change
    receipt.wholeTangent time +
        wholeSpaceTimeViscousNegativeOneState
          ν.coeff receipt.stateLimit receipt.gradient_summable
            (receiptPointwiseGradient_ae_summable receipt) time = _
  rw [tangentEq, viscousEq, nonlinearEq]
  abel

/-- The complete nonlinear space-time forcing is paid by the actual
Serrin-density–vorticity-mass product of the identical whole receipt. -/
theorem receiptNonlinearNegativeOneState_norm_sq_le_serrinEnergy
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime) :
    ‖receiptNonlinearNegativeOneState receipt‖ ^ 2 ≤
      8 *
        (∫ time,
          receipt.serrinDensity time *
            wholeVorticityEuclideanMass (receipt.wholePath time)
          ∂(commonTimeMeasure requestedTime)) := by
  let gradientSummable :
      Summable fun wave : IntegerWavevector =>
        wholeSpaceTimeVorticityGradientDensity requestedTime
          (transverseSpaceTimeInclusion
            requestedTime receipt.transverseLimit) wave := by
    simpa only [receipt.stateLimit_eq_transverse] using
      receipt.gradient_summable
  let coefficientNonneg :=
    wholeReceiptVorticityMassCeiling_nonneg receipt
  let coefficientMassLe :=
    wholeReceiptTransverseVorticityMass_ae_le_ceiling receipt
  rw [receiptNonlinearNegativeOneState_eq_canonicalWholeNonlinearity]
  rw [spaceTime_norm_sq_eq_integral]
  have functionIntegrable :=
    wholeSpaceTimeNonlinearNegativeOneFunction_integrable_norm_sq
      receipt.transverseLimit gradientSummable
      coefficientNonneg coefficientMassLe
  have serrinEnergyIntegrable :=
    (wholeReceiptSerrinDensity_mul_vorticityMass_integrable receipt).const_mul 8
  calc
    (∫ time,
        ‖wholeSpaceTimeNonlinearNegativeOneState
          receipt.transverseLimit gradientSummable
            coefficientNonneg coefficientMassLe time‖ ^ 2
        ∂(commonTimeMeasure requestedTime)) =
        ∫ time,
          ‖wholeSpaceTimeNonlinearNegativeOneFunction
            receipt.transverseLimit time‖ ^ 2
          ∂(commonTimeMeasure requestedTime) := by
      apply integral_congr_ae
      filter_upwards [
        wholeSpaceTimeNonlinearNegativeOneState_coeFn
          receipt.transverseLimit gradientSummable
            coefficientNonneg coefficientMassLe] with
          time forcingEq
      rw [forcingEq]
    _ ≤
        ∫ time,
          8 *
            (receipt.serrinDensity time *
              wholeVorticityEuclideanMass (receipt.wholePath time))
          ∂(commonTimeMeasure requestedTime) := by
      apply integral_mono_ae functionIntegrable serrinEnergyIntegrable
      filter_upwards [
        transversePointwiseGradient_ae_summable
          receipt.transverseLimit gradientSummable,
        wholeReceiptNonlinearNegativeOneMass_ae_le_velocitySerrin
          receipt] with
          time timeGradientSummable nonlinearBound
      rw [wholeSpaceTimeNonlinearNegativeOneFunction_norm_sq
        receipt.transverseLimit time timeGradientSummable]
      simpa only [mul_assoc] using nonlinearBound
    _ =
        8 *
          (∫ time,
            receipt.serrinDensity time *
              wholeVorticityEuclideanMass (receipt.wholePath time)
            ∂(commonTimeMeasure requestedTime)) := by
      rw [integral_const_mul]

/-! ## Same-receipt finite inventories -/

/-- Every finite inventory of actual nonlinear enstrophy work is paid by
the complete `H¹--H⁻¹` action of the identical receipt.  The finite set is
only a readout inventory; the right-hand side remains the whole carrier. -/
theorem actualWholeFiniteNonlinearWork_le_wholeDualPayment
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime)
    (modes : Finset IntegerWavevector) :
    actualWholeFiniteNonlinearWork receipt modes ≤
      (6 / ν.coeff) *
        (‖receiptViscousNegativeOneState receipt‖ *
          ‖receiptNonlinearNegativeOneState receipt‖) := by
  rw [actualWholeFiniteNonlinearWork_eq_bilinearWork]
  unfold actualWholeFiniteBilinearWork
  calc
    (∑ wave ∈ modes,
        actualWholeRowBilinearWork receipt wave) ≤
        ∑ wave ∈ modes,
          max (actualWholeRowBilinearWork receipt wave) 0 := by
      exact Finset.sum_le_sum fun wave _waveMem =>
        le_max_left _ _
    _ ≤
        (6 / ν.coeff) *
          (‖receiptViscousNegativeOneState receipt‖ *
            ‖receiptNonlinearNegativeOneState receipt‖) :=
      finite_sum_positiveOutputWork_le_dualBudget receipt modes

/-- Finite endpoint enstrophy, its actual viscous payment, and the initial
inventory obey one same-event whole-action inequality. -/
theorem actualWholeFiniteEndpoint_add_viscous_le_initial_add_wholeDualPayment
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime)
    (modes : Finset IntegerWavevector) :
    finiteStateVorticityCoefficientEnstrophy modes
          (receipt.wholePath
            ⟨requestedTime,
              ⟨receipt.requestedTimePos.le, le_rfl⟩⟩) +
        actualWholeFiniteViscousPayment receipt modes ≤
      finiteStateVorticityCoefficientEnstrophy modes initialState +
        (6 / ν.coeff) *
          (‖receiptViscousNegativeOneState receipt‖ *
            ‖receiptNonlinearNegativeOneState receipt‖) := by
  have nonlinearBound :=
    actualWholeFiniteNonlinearWork_le_wholeDualPayment receipt modes
  rw [← actualWholeFiniteNetWork_add_viscousPayment] at nonlinearBound
  rw [actualWholeFiniteNetWork_eq_terminal_sub_initial]
    at nonlinearBound
  linarith

private theorem spaceTime_row_norm_sq_integrable
    {requestedTime : ℝ}
    (state : SpaceTimeState requestedTime)
    (wave : IntegerWavevector) :
    Integrable (fun time => ‖state time wave‖ ^ 2)
      (commonTimeMeasure requestedTime) := by
  have wholeIntegrable :
      Integrable (fun time => ‖state time‖ ^ 2)
        (commonTimeMeasure requestedTime) :=
    (MeasureTheory.Lp.memLp state).integrable_norm_pow (by norm_num)
  apply wholeIntegrable.mono'
  · exact
      ((lp.evalCLM ℂ
        (fun _ : IntegerWavevector => ComplexCoordinateVector)
        2 wave).continuous.comp_aestronglyMeasurable
          (MeasureTheory.Lp.aestronglyMeasurable state)).norm.pow 2
  · filter_upwards with time
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have rowLe : ‖state time wave‖ ≤ ‖state time‖ :=
      lp.norm_apply_le_norm
        (p := (2 : ℝ≥0∞)) (by norm_num) (state time) wave
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 rowLe

/-- Positive viscous power of one actual receipt row on its common-time
carrier.  This is the integrand already present in
`actualWholeRowViscousPayment`, written after the self-pairing is evaluated. -/
def receiptRowViscousPower
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime)
    (wave : IntegerWavevector)
    (time : Set.Icc (0 : ℝ) requestedTime) : ℝ :=
  2 * ν.coeff * integerWaveViscousMultiplier wave *
    complexCoordinateAmplitudeSq (receipt.wholePath time wave)

theorem receiptRowViscousPower_nonneg
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime)
    (wave : IntegerWavevector)
    (time : Set.Icc (0 : ℝ) requestedTime) :
    0 ≤ receiptRowViscousPower receipt wave time := by
  unfold receiptRowViscousPower
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (by norm_num) ν.coeff_pos.le)
      (by
        unfold integerWaveViscousMultiplier
        exact mul_nonneg (sq_nonneg _)
          (integerWaveNormSq_nonneg wave)))
    (complexCoordinateAmplitudeSq_nonneg _)

theorem receiptRowViscousPower_integrable
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime)
    (wave : IntegerWavevector) :
    Integrable (receiptRowViscousPower receipt wave)
      (commonTimeMeasure requestedTime) := by
  have densityContinuous :
      Continuous (receiptRowViscousPower receipt wave) := by
    unfold receiptRowViscousPower
    exact continuous_const.mul <|
      complexCoordinateAmplitudeSq_continuous.comp <|
        (lp.evalCLM ℂ
          (fun _ : IntegerWavevector => ComplexCoordinateVector)
          2 wave).continuous.comp receipt.wholePath.continuous
  simpa only [MeasureTheory.integrableOn_univ] using
    densityContinuous.continuousOn.integrableOn_compact
      (isCompact_univ : IsCompact
        (Set.univ : Set (Set.Icc (0 : ℝ) requestedTime)))

/-- The interval definition of actual viscous payment is exactly the
common-time positive density of the same receipt. -/
theorem actualWholeRowViscousPayment_eq_commonTimeIntegral
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime)
    (wave : IntegerWavevector) :
    actualWholeRowViscousPayment receipt wave =
      ∫ time, receiptRowViscousPower receipt wave time
        ∂(commonTimeMeasure requestedTime) := by
  by_cases waveZero : wave = 0
  · subst wave
    simp [actualWholeRowViscousPayment,
      receiptRowViscousPower, integerWaveViscousMultiplier,
      integerWaveNormSq]
  · unfold actualWholeRowViscousPayment
    rw [dif_neg waveZero]
    rw [← commonTime_integral_eq_intervalIntegral
      requestedTime receipt.requestedTimePos.le]
    apply integral_congr_ae
    filter_upwards with time
    rw [receipt.rowExtension_on_interval wave waveZero time,
      complexCoordinateRealInner_real_smul_right,
      complexCoordinateRealInner_self,
      ← complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
    unfold receiptRowViscousPower
    ring

/-- The same-event dual density splits into one absorbable viscous square
and one nonlinear `H⁻¹` square.  Positivity of the already fixed physical
viscosity generates the split; no Young parameter is supplied by a caller. -/
theorem receiptRowDualDensity_le_viscousSquare_add_nonlinearSquare
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime)
    (wave : IntegerWavevector)
    (time : Set.Icc (0 : ℝ) requestedTime) :
    receiptRowDualDensity receipt wave time ≤
      ν.coeff⁻¹ *
          ‖(receiptViscousNegativeOneState receipt time) wave‖ ^ 2 +
        (9 * ν.coeff⁻¹) *
          ‖(receiptNonlinearNegativeOneState receipt time) wave‖ ^ 2 := by
  let viscousNorm :=
    ‖(receiptViscousNegativeOneState receipt time) wave‖
  let nonlinearNorm :=
    ‖(receiptNonlinearNegativeOneState receipt time) wave‖
  have square :=
    sq_nonneg (viscousNorm - 3 * nonlinearNorm)
  have base :
      6 * viscousNorm * nonlinearNorm ≤
        viscousNorm ^ 2 + 9 * nonlinearNorm ^ 2 := by
    nlinarith
  have inverseNonneg : 0 ≤ ν.coeff⁻¹ :=
    inv_nonneg.2 ν.coeff_pos.le
  unfold receiptRowDualDensity
  dsimp only [viscousNorm, nonlinearNorm] at base ⊢
  calc
    (6 / ν.coeff) *
          (‖(receiptViscousNegativeOneState receipt time) wave‖ *
            ‖(receiptNonlinearNegativeOneState receipt time) wave‖) =
        ν.coeff⁻¹ *
          (6 * ‖(receiptViscousNegativeOneState receipt time) wave‖ *
            ‖(receiptNonlinearNegativeOneState receipt time) wave‖) := by
      ring
    _ ≤
        ν.coeff⁻¹ *
          (‖(receiptViscousNegativeOneState receipt time) wave‖ ^ 2 +
            9 *
              ‖(receiptNonlinearNegativeOneState receipt time) wave‖ ^ 2) :=
      mul_le_mul_of_nonneg_left base inverseNonneg
    _ =
        ν.coeff⁻¹ *
            ‖(receiptViscousNegativeOneState receipt time) wave‖ ^ 2 +
          (9 * ν.coeff⁻¹) *
            ‖(receiptNonlinearNegativeOneState receipt time) wave‖ ^ 2 := by
      ring

/-- The viscous square of each weighted row is paid by one half of the
literal physical viscous power on the same common-time event. -/
theorem receiptViscousNegativeOneRowSquare_ae_le_halfPower
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime)
    (wave : IntegerWavevector) :
    ∀ᵐ time ∂(commonTimeMeasure requestedTime),
      ν.coeff⁻¹ *
          ‖(receiptViscousNegativeOneState receipt time) wave‖ ^ 2 ≤
        (1 / 2 : ℝ) * receiptRowViscousPower receipt wave time := by
  filter_upwards [
    receiptViscousNegativeOneState_row_ae receipt wave] with
      time viscousEq
  have multiplierNonneg :
      0 ≤ integerWaveViscousMultiplier wave := by
    unfold integerWaveViscousMultiplier
    exact mul_nonneg (sq_nonneg _)
      (integerWaveNormSq_nonneg wave)
  have scalarNonneg :
      0 ≤ ν.coeff * Real.sqrt (integerWaveViscousMultiplier wave) :=
    mul_nonneg ν.coeff_pos.le (Real.sqrt_nonneg _)
  have rowSquareLe :
      ‖receipt.wholePath time wave‖ ^ 2 ≤
        complexCoordinateAmplitudeSq
          (receipt.wholePath time wave) :=
    complexCoordinateVector_norm_sq_le_amplitudeSq _
  rw [viscousEq, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg scalarNonneg]
  unfold receiptRowViscousPower
  have viscosityNe : ν.coeff ≠ 0 := ne_of_gt ν.coeff_pos
  calc
    ν.coeff⁻¹ *
          ((ν.coeff * Real.sqrt
              (integerWaveViscousMultiplier wave)) *
            ‖receipt.wholePath time wave‖) ^ 2 =
        ν.coeff * integerWaveViscousMultiplier wave *
          ‖receipt.wholePath time wave‖ ^ 2 := by
      rw [mul_pow, show
        (ν.coeff * Real.sqrt
            (integerWaveViscousMultiplier wave)) ^ 2 =
          ν.coeff ^ 2 *
            Real.sqrt (integerWaveViscousMultiplier wave) ^ 2 by ring,
        Real.sq_sqrt multiplierNonneg]
      field_simp [viscosityNe]
    _ ≤
        ν.coeff * integerWaveViscousMultiplier wave *
          complexCoordinateAmplitudeSq
            (receipt.wholePath time wave) :=
      mul_le_mul_of_nonneg_left rowSquareLe
        (mul_nonneg ν.coeff_pos.le multiplierNonneg)
    _ =
        (1 / 2 : ℝ) *
          (2 * ν.coeff * integerWaveViscousMultiplier wave *
            complexCoordinateAmplitudeSq
              (receipt.wholePath time wave)) := by
      ring

/-- One actual nonlinear row is bounded by half of its own viscous payment
plus the nonlinear weighted square of that same row. -/
theorem actualWholeRowBilinearWork_le_halfViscous_add_nonlinearSquare
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime)
    (wave : IntegerWavevector) :
    actualWholeRowBilinearWork receipt wave ≤
      (1 / 2 : ℝ) * actualWholeRowViscousPayment receipt wave +
        (9 * ν.coeff⁻¹) *
          (∫ time,
            ‖(receiptNonlinearNegativeOneState receipt time) wave‖ ^ 2
              ∂(commonTimeMeasure requestedTime)) := by
  let viscousSquare := fun time : Set.Icc (0 : ℝ) requestedTime =>
    ν.coeff⁻¹ *
      ‖(receiptViscousNegativeOneState receipt time) wave‖ ^ 2
  let nonlinearSquare := fun time : Set.Icc (0 : ℝ) requestedTime =>
    (9 * ν.coeff⁻¹) *
      ‖(receiptNonlinearNegativeOneState receipt time) wave‖ ^ 2
  have viscousSquareIntegrable :
      Integrable viscousSquare (commonTimeMeasure requestedTime) :=
    (spaceTime_row_norm_sq_integrable
      (receiptViscousNegativeOneState receipt) wave).const_mul ν.coeff⁻¹
  have nonlinearSquareIntegrable :
      Integrable nonlinearSquare (commonTimeMeasure requestedTime) :=
    (spaceTime_row_norm_sq_integrable
      (receiptNonlinearNegativeOneState receipt) wave).const_mul
        (9 * ν.coeff⁻¹)
  have splitIntegralLe :
      (∫ time, receiptRowDualDensity receipt wave time
          ∂(commonTimeMeasure requestedTime)) ≤
        ∫ time, viscousSquare time + nonlinearSquare time
          ∂(commonTimeMeasure requestedTime) := by
    exact integral_mono_ae
      (receiptRowDualDensity_integrable receipt wave)
      (viscousSquareIntegrable.add nonlinearSquareIntegrable)
      (Filter.Eventually.of_forall fun time =>
        receiptRowDualDensity_le_viscousSquare_add_nonlinearSquare
          receipt wave time)
  have viscousIntegralLe :
      (∫ time, viscousSquare time
          ∂(commonTimeMeasure requestedTime)) ≤
        ∫ time,
          (1 / 2 : ℝ) * receiptRowViscousPower receipt wave time
            ∂(commonTimeMeasure requestedTime) := by
    exact integral_mono_ae
      viscousSquareIntegrable
      ((receiptRowViscousPower_integrable receipt wave).const_mul
        (1 / 2 : ℝ))
      (receiptViscousNegativeOneRowSquare_ae_le_halfPower
        receipt wave)
  calc
    actualWholeRowBilinearWork receipt wave ≤
        max (actualWholeRowBilinearWork receipt wave) 0 :=
      le_max_left _ _
    _ ≤
        ∫ time, receiptRowDualDensity receipt wave time
          ∂(commonTimeMeasure requestedTime) :=
      max_actualWholeRowBilinearWork_le_integral_dualDensity
        receipt wave
    _ ≤
        ∫ time, viscousSquare time + nonlinearSquare time
          ∂(commonTimeMeasure requestedTime) := splitIntegralLe
    _ =
        (∫ time, viscousSquare time
            ∂(commonTimeMeasure requestedTime)) +
          ∫ time, nonlinearSquare time
            ∂(commonTimeMeasure requestedTime) := by
      rw [integral_add viscousSquareIntegrable nonlinearSquareIntegrable]
    _ ≤
        (∫ time,
            (1 / 2 : ℝ) * receiptRowViscousPower receipt wave time
              ∂(commonTimeMeasure requestedTime)) +
          ∫ time, nonlinearSquare time
            ∂(commonTimeMeasure requestedTime) :=
      add_le_add viscousIntegralLe le_rfl
    _ =
        (1 / 2 : ℝ) * actualWholeRowViscousPayment receipt wave +
          (9 * ν.coeff⁻¹) *
            (∫ time,
              ‖(receiptNonlinearNegativeOneState receipt time) wave‖ ^ 2
                ∂(commonTimeMeasure requestedTime)) := by
      rw [integral_const_mul, integral_const_mul,
        ← actualWholeRowViscousPayment_eq_commonTimeIntegral]

/-- A finite output inventory of nonlinear weighted squares is bounded by
the norm of the complete space-time `H⁻¹` state. -/
theorem finite_nonlinearRowSquareIntegral_le_wholeNormSq
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime)
    (modes : Finset IntegerWavevector) :
    (∑ wave ∈ modes,
        ∫ time,
          ‖(receiptNonlinearNegativeOneState receipt time) wave‖ ^ 2
            ∂(commonTimeMeasure requestedTime)) ≤
      ‖receiptNonlinearNegativeOneState receipt‖ ^ 2 := by
  let nonlinear := receiptNonlinearNegativeOneState receipt
  have eachIntegrable :
      ∀ wave ∈ modes,
        Integrable (fun time => ‖(nonlinear time) wave‖ ^ 2)
          (commonTimeMeasure requestedTime) :=
    fun wave _waveMem => spaceTime_row_norm_sq_integrable nonlinear wave
  have sumIntegrable :
      Integrable
        (fun time => ∑ wave ∈ modes, ‖(nonlinear time) wave‖ ^ 2)
        (commonTimeMeasure requestedTime) := by
    exact integrable_finsetSum modes eachIntegrable
  have wholeIntegrable :
      Integrable (fun time => ‖nonlinear time‖ ^ 2)
        (commonTimeMeasure requestedTime) :=
    (MeasureTheory.Lp.memLp nonlinear).integrable_norm_pow (by norm_num)
  change
    (∑ wave ∈ modes,
        ∫ time, ‖(nonlinear time) wave‖ ^ 2
          ∂(commonTimeMeasure requestedTime)) ≤
      ‖nonlinear‖ ^ 2
  rw [spaceTime_norm_sq_eq_integral]
  rw [← integral_finsetSum modes eachIntegrable]
  apply integral_mono_ae sumIntegrable wholeIntegrable
  filter_upwards with time
  have nonlinearHasSum :
      HasSum
        (fun wave : IntegerWavevector => ‖nonlinear time wave‖ ^ 2)
        (‖nonlinear time‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (lp.hasSum_norm
        (p := (2 : ℝ≥0∞)) (by norm_num) (nonlinear time))
  rw [← nonlinearHasSum.tsum_eq]
  exact nonlinearHasSum.summable.sum_le_tsum modes
    (fun wave _waveMem => sq_nonneg _)

/-- Viscosity is absorbed on the same finite inventory before the output
quotient.  The only surviving term is the complete nonlinear `H⁻¹` square. -/
theorem actualWholeFiniteNonlinearWork_le_halfViscous_add_nonlinearNormSq
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime)
    (modes : Finset IntegerWavevector) :
    actualWholeFiniteNonlinearWork receipt modes ≤
      (1 / 2 : ℝ) * actualWholeFiniteViscousPayment receipt modes +
        (9 * ν.coeff⁻¹) *
          ‖receiptNonlinearNegativeOneState receipt‖ ^ 2 := by
  rw [actualWholeFiniteNonlinearWork_eq_bilinearWork]
  unfold actualWholeFiniteBilinearWork
  calc
    (∑ wave ∈ modes, actualWholeRowBilinearWork receipt wave) ≤
        ∑ wave ∈ modes,
          ((1 / 2 : ℝ) *
              actualWholeRowViscousPayment receipt wave +
            (9 * ν.coeff⁻¹) *
              (∫ time,
                ‖(receiptNonlinearNegativeOneState receipt time) wave‖ ^ 2
                  ∂(commonTimeMeasure requestedTime))) := by
      exact Finset.sum_le_sum fun wave _waveMem =>
        actualWholeRowBilinearWork_le_halfViscous_add_nonlinearSquare
          receipt wave
    _ =
        (1 / 2 : ℝ) * actualWholeFiniteViscousPayment receipt modes +
          (9 * ν.coeff⁻¹) *
            (∑ wave ∈ modes,
              ∫ time,
                ‖(receiptNonlinearNegativeOneState receipt time) wave‖ ^ 2
                  ∂(commonTimeMeasure requestedTime)) := by
      unfold actualWholeFiniteViscousPayment
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤
        (1 / 2 : ℝ) * actualWholeFiniteViscousPayment receipt modes +
          (9 * ν.coeff⁻¹) *
            ‖receiptNonlinearNegativeOneState receipt‖ ^ 2 := by
      have coefficientNonneg : 0 ≤ 9 * ν.coeff⁻¹ :=
        mul_nonneg (by norm_num) (inv_nonneg.2 ν.coeff_pos.le)
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_left
          (finite_nonlinearRowSquareIntegral_le_wholeNormSq
            receipt modes)
          coefficientNonneg)

/-- The whole nonlinear carrier controls every finite endpoint inventory
after its own viscous leg has been absorbed. -/
theorem actualWholeFiniteEndpoint_le_initial_add_nonlinearNormSq
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime)
    (modes : Finset IntegerWavevector) :
    finiteStateVorticityCoefficientEnstrophy modes
        (receipt.wholePath
          ⟨requestedTime,
            ⟨receipt.requestedTimePos.le, le_rfl⟩⟩) ≤
      finiteStateVorticityCoefficientEnstrophy modes initialState +
        (9 * ν.coeff⁻¹) *
          ‖receiptNonlinearNegativeOneState receipt‖ ^ 2 := by
  have nonlinearBound :=
    actualWholeFiniteNonlinearWork_le_halfViscous_add_nonlinearNormSq
      receipt modes
  rw [← actualWholeFiniteNetWork_add_viscousPayment,
    actualWholeFiniteNetWork_eq_terminal_sub_initial] at nonlinearBound
  have viscousNonneg :=
    actualWholeFiniteViscousPayment_nonneg receipt modes
  linarith

/-- Cutoff exhaustion removes the finite readout entirely: one actual whole
receipt's endpoint vorticity mass is controlled by its initial mass and the
same receipt's complete nonlinear `H⁻¹` square. -/
theorem WholeContinuousMildSerrinReceipt.terminal_vorticityMass_le_initial_add_nonlinearNormSq
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime) :
    wholeVorticityEuclideanMass
        (receipt.wholePath
          ⟨requestedTime,
            ⟨receipt.requestedTimePos.le, le_rfl⟩⟩) ≤
      wholeVorticityEuclideanMass initialState +
        (9 * ν.coeff⁻¹) *
          ‖receiptNonlinearNegativeOneState receipt‖ ^ 2 := by
  apply wholeVorticityEuclideanMass_le_of_finiteRestartInventory_le
  · exact receipt.wholePath_zero_row
      ⟨requestedTime,
        ⟨receipt.requestedTimePos.le, le_rfl⟩⟩
  · intro radius
    exact
      (actualWholeFiniteEndpoint_le_initial_add_nonlinearNormSq
        receipt (wholeRestartModes radius)).trans <| by
          exact add_le_add
            (ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEnstrophyWork.finiteStateVorticityCoefficientEnstrophy_le_wholeMass
              (wholeRestartModes radius) initialState) le_rfl

/-- One actual whole unforced receipt obeys the cutoff-free integral
enstrophy inequality generated by its own velocity Serrin density.  The
nonlinear `H⁻¹` carrier and the endpoint are those of the same receipt; no
external cutoff, margin, or continuation witness is supplied. -/
theorem WholeContinuousMildSerrinReceipt.terminal_vorticityMass_le_initial_add_serrinEnergy
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime) :
    wholeVorticityEuclideanMass
        (receipt.wholePath
          ⟨requestedTime,
            ⟨receipt.requestedTimePos.le, le_rfl⟩⟩) ≤
      wholeVorticityEuclideanMass initialState +
        (72 * ν.coeff⁻¹) *
          (∫ time,
            receipt.serrinDensity time *
              wholeVorticityEuclideanMass (receipt.wholePath time)
            ∂(commonTimeMeasure requestedTime)) := by
  have endpointBound :=
    WholeContinuousMildSerrinReceipt.terminal_vorticityMass_le_initial_add_nonlinearNormSq
      receipt
  have nonlinearBound :=
    receiptNonlinearNegativeOneState_norm_sq_le_serrinEnergy receipt
  have coefficientNonneg : 0 ≤ 9 * ν.coeff⁻¹ :=
    mul_nonneg (by norm_num) (inv_nonneg.2 ν.coeff_pos.le)
  calc
    wholeVorticityEuclideanMass
        (receipt.wholePath
          ⟨requestedTime,
            ⟨receipt.requestedTimePos.le, le_rfl⟩⟩) ≤
        wholeVorticityEuclideanMass initialState +
          (9 * ν.coeff⁻¹) *
            ‖receiptNonlinearNegativeOneState receipt‖ ^ 2 := endpointBound
    _ ≤ wholeVorticityEuclideanMass initialState +
          (9 * ν.coeff⁻¹) *
            (8 *
              (∫ time,
                receipt.serrinDensity time *
                  wholeVorticityEuclideanMass (receipt.wholePath time)
                ∂(commonTimeMeasure requestedTime))) := by
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_left nonlinearBound coefficientNonneg)
    _ = wholeVorticityEuclideanMass initialState +
          (72 * ν.coeff⁻¹) *
            (∫ time,
              receipt.serrinDensity time *
                wholeVorticityEuclideanMass (receipt.wholePath time)
              ∂(commonTimeMeasure requestedTime)) := by
      ring

end

end ThreeDimensionalVorticityCoefficientWholeSerrinEnstrophyGronwall
end NavierStokes
end SaturationMonoid
