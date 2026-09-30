import H0mework.NavierStokes.GeneratedPaths.InfiniteNonlinearNegativeOneTimeBudget
import H0mework.NavierStokes.WholeSpace.WholeSpaceTimeGradientLowerSemicontinuity

/-!
# Whole space-time critical Serrin transport

This module closes the Tonelli bridge between the whole Fourier-gradient
carrier and the pointwise critical velocity geometry.

For a general whole space-time state with summable gradient density it proves:

* almost-everywhere summability of the actual pointwise Euclidean gradient;
* summability of the whole Fourier velocity majorant at those same times;
* integrability of the squared whole velocity majorant; and
* the cutoff-free estimate

`∫ M_whole(t)^2 dt ≤ 3 K_crit G_whole`.

The factor three is the exact finite-coordinate comparison between the
ambient row sup norm used by the Hilbert carrier and the Euclidean amplitude
used by Biot--Savart.  Pointwise summability is generated from the
space-time `tsum`; the default value of a nonsummable `tsum` is never used as
an analytic premise.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientWholeSpaceTimeCriticalSerrin

open scoped BigOperators

open Set
open MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellSource
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalIntegerLatticeCriticalKernel
open ThreeDimensionalVorticityCoefficientFiniteSupportCriticalSobolev
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier
open ThreeDimensionalVorticityCoefficientGeneratedPathCriticalAbsorption
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeSubsequence
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedPathCommonTimeCompactnessBudget
open ThreeDimensionalVorticityCoefficientInfiniteNonlinearNegativeSobolev
open ThreeDimensionalVorticityCoefficientGeneratedPathInfiniteNonlinearNegativeOneTimeBudget
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeGradientLowerSemicontinuity

noncomputable section

/-- The full Fourier velocity majorant on the whole lattice. -/
def wholeStateVelocityMajorant
    (state : ComplexVorticityHilbertState) : ℝ :=
  ∑' wave : IntegerWavevector,
    Real.sqrt
      (complexCoordinateAmplitudeSq
        (finiteStateVelocityCoefficient state wave))

theorem complexCoordinateAmplitudeSq_continuous :
    Continuous complexCoordinateAmplitudeSq := by
  unfold complexCoordinateAmplitudeSq
  fun_prop

theorem wholeVelocityAmplitudeTerm_continuous
    (wave : IntegerWavevector) :
    Continuous
      (fun state : ComplexVorticityHilbertState =>
        Real.sqrt
          (complexCoordinateAmplitudeSq
            (finiteStateVelocityCoefficient state wave))) := by
  exact Real.continuous_sqrt.comp <|
    complexCoordinateAmplitudeSq_continuous.comp <|
      (finiteStateVelocityCoefficient_contDiff wave).continuous

theorem wholeStateVelocityMajorant_nonneg
    (state : ComplexVorticityHilbertState) :
    0 ≤ wholeStateVelocityMajorant state := by
  unfold wholeStateVelocityMajorant
  exact tsum_nonneg fun wave => Real.sqrt_nonneg _

theorem wholeStateVelocityMajorant_eq_finite_of_supported
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState)
    (supported :
      ∀ wave : IntegerWavevector,
        wave ∉ modes → state wave = 0) :
    wholeStateVelocityMajorant state =
      finiteStateVelocityMajorant modes state := by
  unfold wholeStateVelocityMajorant
    finiteStateVelocityMajorant finiteVelocityFourierMajorant
  rw [tsum_eq_sum (s := modes)]
  intro wave waveNotMem
  simp [finiteStateVelocityCoefficient,
    supported wave waveNotMem, complexCoordinateAmplitudeSq]

theorem summable_wholeStateVelocityAmplitude
    (state : ComplexVorticityHilbertState)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (state wave)) :
    Summable fun wave : IntegerWavevector =>
      Real.sqrt
        (complexCoordinateAmplitudeSq
          (finiteStateVelocityCoefficient state wave)) := by
  let criticalConstant :=
    biotSavartSerrinConstant *
      (∑' wave : IntegerWavevector, integerWaveCriticalKernel wave)
  let gradientMass := wholeStateVorticityGradientMass state
  have criticalConstantNonneg : 0 ≤ criticalConstant := by
    exact mul_nonneg biotSavartSerrinConstant_nonneg
      integerWaveCriticalKernel_tsum_nonneg
  have gradientMassNonneg : 0 ≤ gradientMass := by
    unfold gradientMass wholeStateVorticityGradientMass
    exact tsum_nonneg fun wave =>
      mul_nonneg (integerWaveNormSq_nonneg wave)
        (complexCoordinateAmplitudeSq_nonneg _)
  apply summable_of_sum_le
    (fun wave => Real.sqrt_nonneg _)
    (c := Real.sqrt (criticalConstant * gradientMass))
  intro modes
  have finiteGradientLe :
      finiteStateVorticityEnstrophyMass modes state ≤
        gradientMass := by
    exact finiteStateVorticityEnstrophyMass_le_wholeGradientMass
      modes state gradientSummable
  have finiteSq :
      finiteStateVelocityMajorant modes state ^ 2 ≤
        criticalConstant * gradientMass := by
    simpa [criticalConstant] using
      (finiteStateVelocityMajorant_sq_le_criticalGlobal
        modes state).trans
        (mul_le_mul_of_nonneg_left finiteGradientLe
          criticalConstantNonneg)
  simpa [finiteStateVelocityMajorant,
    finiteVelocityFourierMajorant] using
      (Real.le_sqrt_of_sq_le finiteSq)

theorem wholeStateVelocityMajorant_sq_le_criticalGlobal
    (state : ComplexVorticityHilbertState)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (state wave)) :
    wholeStateVelocityMajorant state ^ 2 ≤
      biotSavartSerrinConstant *
        (∑' wave : IntegerWavevector, integerWaveCriticalKernel wave) *
        wholeStateVorticityGradientMass state := by
  let criticalConstant :=
    biotSavartSerrinConstant *
      (∑' wave : IntegerWavevector, integerWaveCriticalKernel wave)
  let gradientMass := wholeStateVorticityGradientMass state
  have criticalConstantNonneg : 0 ≤ criticalConstant := by
    exact mul_nonneg biotSavartSerrinConstant_nonneg
      integerWaveCriticalKernel_tsum_nonneg
  have gradientMassNonneg : 0 ≤ gradientMass := by
    unfold gradientMass wholeStateVorticityGradientMass
    exact tsum_nonneg fun wave =>
      mul_nonneg (integerWaveNormSq_nonneg wave)
        (complexCoordinateAmplitudeSq_nonneg _)
  have majorantSummable :=
    summable_wholeStateVelocityAmplitude state gradientSummable
  have majorantLe :
      wholeStateVelocityMajorant state ≤
        Real.sqrt (criticalConstant * gradientMass) := by
    unfold wholeStateVelocityMajorant
    apply majorantSummable.tsum_le_of_sum_le
    intro modes
    have finiteGradientLe :
        finiteStateVorticityEnstrophyMass modes state ≤
          gradientMass := by
      exact finiteStateVorticityEnstrophyMass_le_wholeGradientMass
        modes state gradientSummable
    have finiteSq :
        finiteStateVelocityMajorant modes state ^ 2 ≤
          criticalConstant * gradientMass := by
      simpa [criticalConstant] using
        (finiteStateVelocityMajorant_sq_le_criticalGlobal
          modes state).trans
          (mul_le_mul_of_nonneg_left finiteGradientLe
            criticalConstantNonneg)
    simpa [finiteStateVelocityMajorant,
      finiteVelocityFourierMajorant] using
        (Real.le_sqrt_of_sq_le finiteSq)
  have majorantNonneg := wholeStateVelocityMajorant_nonneg state
  have rootSq :
      Real.sqrt (criticalConstant * gradientMass) ^ 2 =
        criticalConstant * gradientMass :=
    Real.sq_sqrt (mul_nonneg criticalConstantNonneg gradientMassNonneg)
  change wholeStateVelocityMajorant state ^ 2 ≤
    criticalConstant * gradientMass
  nlinarith

theorem
    GeneratedPathCommonTimeCompactnessBudget.wholeGradientIntegral_eq_finite
    {seed current : RawVorticityFourierSource}
    {arrival : GeneratedIntegerShellReachable seed current}
    {ν : Viscosity}
    {θ requestedTime : ℝ}
    (budget :
      GeneratedPathCommonTimeCompactnessBudget
        arrival ν θ requestedTime)
    (requestedTimeNonneg : 0 ≤ requestedTime) :
    (∫ t in (0 : ℝ)..requestedTime,
        wholeStateVorticityGradientMass (budget.trajectory t)) =
      ∫ t in (0 : ℝ)..requestedTime,
        finiteStateVorticityEnstrophyMass
          (generatedSupport current) (budget.trajectory t) := by
  apply intervalIntegral.integral_congr
  intro t tMem
  have tInInterval : t ∈ Icc (0 : ℝ) requestedTime := by
    rwa [uIcc_of_le requestedTimeNonneg] at tMem
  exact wholeStateVorticityGradientMass_eq_finite_of_supported
    (generatedSupport current) (budget.trajectory t)
    (budget.physicalProperties t tInInterval).2.1

theorem
    GeneratedPathCommonTimeCompactnessBudget.wholeVelocityIntegral_eq_finite
    {seed current : RawVorticityFourierSource}
    {arrival : GeneratedIntegerShellReachable seed current}
    {ν : Viscosity}
    {θ requestedTime : ℝ}
    (budget :
      GeneratedPathCommonTimeCompactnessBudget
        arrival ν θ requestedTime)
    (requestedTimeNonneg : 0 ≤ requestedTime) :
    (∫ t in (0 : ℝ)..requestedTime,
        wholeStateVelocityMajorant (budget.trajectory t) ^ 2) =
      ∫ t in (0 : ℝ)..requestedTime,
        finiteStateVelocityMajorant
          (generatedSupport current) (budget.trajectory t) ^ 2 := by
  apply intervalIntegral.integral_congr
  intro t tMem
  have tInInterval : t ∈ Icc (0 : ℝ) requestedTime := by
    rwa [uIcc_of_le requestedTimeNonneg] at tMem
  change
    wholeStateVelocityMajorant (budget.trajectory t) ^ 2 =
      finiteStateVelocityMajorant
        (generatedSupport current) (budget.trajectory t) ^ 2
  rw [wholeStateVelocityMajorant_eq_finite_of_supported
    (generatedSupport current) (budget.trajectory t)
    (budget.physicalProperties t tInInterval).2.1]

theorem
    GeneratedPathCommonTimeCompactnessBudget.wholeCriticalSerrinBudget
    {seed current : RawVorticityFourierSource}
    {arrival : GeneratedIntegerShellReachable seed current}
    {ν : Viscosity}
    {θ requestedTime : ℝ}
    (budget :
      GeneratedPathCommonTimeCompactnessBudget
        arrival ν θ requestedTime)
    (requestedTimeNonneg : 0 ≤ requestedTime) :
    criticalEnstrophyAbsorptionCoefficient θ ν *
          (∫ t in (0 : ℝ)..requestedTime,
            wholeStateVorticityGradientMass
              (budget.trajectory t)) ≤
        finiteStateVorticityHalfEnstrophy
            (generatedSupport current) (budget.trajectory 0) -
          finiteStateVorticityHalfEnstrophy
            (generatedSupport current)
            (budget.trajectory requestedTime) ∧
      (∫ t in (0 : ℝ)..requestedTime,
        wholeStateVelocityMajorant (budget.trajectory t) ^ 2) ≤
        criticalEnstrophyLatticeConstant *
            finiteStateVorticityHalfEnstrophy
              (generatedSupport current) (budget.trajectory 0) /
          criticalEnstrophyAbsorptionCoefficient θ ν := by
  constructor
  · rw [
      ThreeDimensionalVorticityCoefficientWholeSpaceTimeCriticalSerrin.GeneratedPathCommonTimeCompactnessBudget.wholeGradientIntegral_eq_finite
        budget requestedTimeNonneg]
    exact budget.enstrophyAbsorption
  · rw [
      ThreeDimensionalVorticityCoefficientWholeSpaceTimeCriticalSerrin.GeneratedPathCommonTimeCompactnessBudget.wholeVelocityIntegral_eq_finite
        budget requestedTimeNonneg]
    exact budget.serrinBound

/-! ## Tonelli transport from space-time gradient mass to pointwise Serrin -/

/-- One pointwise carrier-norm gradient density.  This uses the same fixed-wave
`L²_t` restriction as the space-time lower-semicontinuity theorem. -/
def wholePointwiseCarrierGradientDensity
    (requestedTime : ℝ)
    (state : SpaceTimeState requestedTime)
    (time : Icc (0 : ℝ) requestedTime)
    (wave : IntegerWavevector) : ℝ :=
  integerWaveNormSq wave *
    ‖fixedWaveSpaceTimeRestriction
      requestedTime wave state time‖ ^ 2

theorem wholePointwiseCarrierGradientDensity_nonneg
    (requestedTime : ℝ)
    (state : SpaceTimeState requestedTime)
    (time : Icc (0 : ℝ) requestedTime)
    (wave : IntegerWavevector) :
    0 ≤
      wholePointwiseCarrierGradientDensity
        requestedTime state time wave := by
  exact mul_nonneg (integerWaveNormSq_nonneg wave) (sq_nonneg _)

theorem wholePointwiseCarrierGradientDensity_integrable
    (requestedTime : ℝ)
    (state : SpaceTimeState requestedTime)
    (wave : IntegerWavevector) :
    Integrable
      (fun time =>
        wholePointwiseCarrierGradientDensity
          requestedTime state time wave)
      (commonTimeMeasure requestedTime) := by
  let row :=
    fixedWaveSpaceTimeRestriction requestedTime wave state
  have rowSqIntegrable :
      Integrable
        (fun time =>
          ‖row time‖ ^ 2)
        (commonTimeMeasure requestedTime) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (MeasureTheory.Lp.memLp row).integrable_norm_rpow
        (by norm_num) (by norm_num)
  simpa only [wholePointwiseCarrierGradientDensity, row] using
    rowSqIntegrable.const_mul (integerWaveNormSq wave)

theorem wholePointwiseCarrierGradientDensity_integral
    (requestedTime : ℝ)
    (state : SpaceTimeState requestedTime)
    (wave : IntegerWavevector) :
    (∫ time,
        wholePointwiseCarrierGradientDensity
          requestedTime state time wave
        ∂(commonTimeMeasure requestedTime)) =
      wholeSpaceTimeVorticityGradientDensity
        requestedTime state wave := by
  unfold wholePointwiseCarrierGradientDensity
    wholeSpaceTimeVorticityGradientDensity
  rw [integral_const_mul]
  rw [← fixedWaveSpaceTimeState_norm_sq_eq_integral]

theorem wholePointwiseCarrierGradientDensity_integral_norm
    (requestedTime : ℝ)
    (state : SpaceTimeState requestedTime)
    (wave : IntegerWavevector) :
    (∫ time,
        ‖wholePointwiseCarrierGradientDensity
          requestedTime state time wave‖
        ∂(commonTimeMeasure requestedTime)) =
      wholeSpaceTimeVorticityGradientDensity
        requestedTime state wave := by
  calc
    (∫ time,
        ‖wholePointwiseCarrierGradientDensity
          requestedTime state time wave‖
        ∂(commonTimeMeasure requestedTime)) =
        ∫ time,
          wholePointwiseCarrierGradientDensity
            requestedTime state time wave
          ∂(commonTimeMeasure requestedTime) := by
      apply integral_congr_ae
      filter_upwards with time
      rw [Real.norm_of_nonneg
        (wholePointwiseCarrierGradientDensity_nonneg
          requestedTime state time wave)]
    _ = _ :=
      wholePointwiseCarrierGradientDensity_integral
        requestedTime state wave

theorem
    wholePointwiseCarrierGradientDensity_ae_summable
    (requestedTime : ℝ)
    (state : SpaceTimeState requestedTime)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        wholeSpaceTimeVorticityGradientDensity
          requestedTime state wave) :
    ∀ᵐ time ∂(commonTimeMeasure requestedTime),
      Summable fun wave : IntegerWavevector =>
        wholePointwiseCarrierGradientDensity
          requestedTime state time wave := by
  let density : IntegerWavevector →
      Icc (0 : ℝ) requestedTime → ℝ :=
    fun wave time =>
      wholePointwiseCarrierGradientDensity
        requestedTime state time wave
  have densityIntegrable :
      ∀ wave : IntegerWavevector,
        Integrable (density wave)
          (commonTimeMeasure requestedTime) := by
    intro wave
    exact
      wholePointwiseCarrierGradientDensity_integrable
        requestedTime state wave
  have integralNormSummable :
      Summable fun wave : IntegerWavevector =>
        ∫ time, ‖density wave time‖
          ∂(commonTimeMeasure requestedTime) := by
    apply gradientSummable.congr
    intro wave
    exact (
      wholePointwiseCarrierGradientDensity_integral_norm
        requestedTime state wave).symm
  have densityEnormAEMeasurable :
      ∀ wave : IntegerWavevector,
        AEMeasurable (fun time => ‖density wave time‖ₑ)
          (commonTimeMeasure requestedTime) :=
    fun wave => (densityIntegrable wave).aestronglyMeasurable.enorm
  have lintegralTsumNeTop :
      lintegral (commonTimeMeasure requestedTime)
          (fun time =>
            tsum fun wave : IntegerWavevector =>
              ‖density wave time‖ₑ) ≠ ⊤ := by
    rw [lintegral_tsum densityEnormAEMeasurable]
    have lintegralEq :
        ∀ wave : IntegerWavevector,
          lintegral (commonTimeMeasure requestedTime)
              (fun time => ‖density wave time‖ₑ) =
            ‖∫ time, ‖density wave time‖
                ∂(commonTimeMeasure requestedTime)‖ₑ := by
      intro wave
      rw [Real.enorm_of_nonneg
        (integral_nonneg fun time => norm_nonneg _)]
      exact
        (ofReal_integral_norm_eq_lintegral_enorm
          (densityIntegrable wave)).symm
    rw [funext lintegralEq]
    exact ENNReal.tsum_coe_ne_top_iff_summable.2 <|
      NNReal.summable_coe.1 integralNormSummable.abs
  have pointwiseNormSummable :
      ∀ᵐ time ∂(commonTimeMeasure requestedTime),
        Summable fun wave : IntegerWavevector =>
          ‖density wave time‖ := by
    have aeFinite :
        ∀ᵐ time ∂(commonTimeMeasure requestedTime),
          (∑' wave : IntegerWavevector,
            ‖density wave time‖ₑ) < ⊤ :=
      ae_lt_top'
        (AEMeasurable.tsum densityEnormAEMeasurable)
        lintegralTsumNeTop
    filter_upwards [aeFinite] with time timeFinite
    exact tsum_enorm_ne_top_iff_summable_norm.1 timeFinite.ne
  filter_upwards [pointwiseNormSummable] with time timeSummable
  simpa only [density] using timeSummable.of_norm

theorem wholePointwiseGradientDensity_ae_summable
    (requestedTime : ℝ)
    (state : SpaceTimeState requestedTime)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        wholeSpaceTimeVorticityGradientDensity
          requestedTime state wave) :
    ∀ᵐ time ∂(commonTimeMeasure requestedTime),
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (state time wave) := by
  have carrierSummable :=
    wholePointwiseCarrierGradientDensity_ae_summable
      requestedTime state gradientSummable
  have rowsAgree :
      ∀ᵐ time ∂(commonTimeMeasure requestedTime),
        ∀ wave : IntegerWavevector,
          fixedWaveSpaceTimeRestriction
              requestedTime wave state time =
            state time wave :=
    eventually_countable_forall.2 fun wave =>
      fixedWaveSpaceTimeRestriction_coeFn
        requestedTime wave state
  filter_upwards [carrierSummable, rowsAgree] with
    time timeCarrierSummable timeRowsAgree
  have dominatingSummable :
      Summable fun wave : IntegerWavevector =>
        3 *
          wholePointwiseCarrierGradientDensity
            requestedTime state time wave :=
    timeCarrierSummable.mul_left 3
  apply Summable.of_nonneg_of_le
    (fun wave =>
      mul_nonneg (integerWaveNormSq_nonneg wave)
        (complexCoordinateAmplitudeSq_nonneg _))
    (fun wave => ?_)
    dominatingSummable
  have amplitudeLe :=
    complexCoordinateAmplitudeSq_le_three_mul_norm_sq
      (fixedWaveSpaceTimeRestriction
        requestedTime wave state time)
  rw [← timeRowsAgree wave]
  unfold wholePointwiseCarrierGradientDensity
  calc
    integerWaveNormSq wave *
        complexCoordinateAmplitudeSq
          (fixedWaveSpaceTimeRestriction
            requestedTime wave state time) ≤
        integerWaveNormSq wave *
          (3 *
            ‖fixedWaveSpaceTimeRestriction
              requestedTime wave state time‖ ^ 2) :=
      mul_le_mul_of_nonneg_left amplitudeLe
        (integerWaveNormSq_nonneg wave)
    _ = 3 *
        (integerWaveNormSq wave *
          ‖fixedWaveSpaceTimeRestriction
            requestedTime wave state time‖ ^ 2) := by ring

theorem wholeStateGradientMass_le_three_mul_pointwiseCarrierMass
    (requestedTime : ℝ)
    (state : SpaceTimeState requestedTime)
    (time : Icc (0 : ℝ) requestedTime)
    (rowsAgree :
      ∀ wave : IntegerWavevector,
        fixedWaveSpaceTimeRestriction
            requestedTime wave state time =
          state time wave)
    (carrierSummable :
      Summable fun wave : IntegerWavevector =>
        wholePointwiseCarrierGradientDensity
          requestedTime state time wave)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (state time wave)) :
    wholeStateVorticityGradientMass (state time) ≤
      3 *
        ∑' wave : IntegerWavevector,
          wholePointwiseCarrierGradientDensity
            requestedTime state time wave := by
  unfold wholeStateVorticityGradientMass
  have dominatingSummable :
      Summable fun wave : IntegerWavevector =>
        3 *
          wholePointwiseCarrierGradientDensity
            requestedTime state time wave :=
    carrierSummable.mul_left 3
  have amplitudeLe :
      ∀ wave : IntegerWavevector,
        integerWaveNormSq wave *
            complexCoordinateAmplitudeSq (state time wave) ≤
          3 *
            wholePointwiseCarrierGradientDensity
              requestedTime state time wave := by
    intro wave
    have rowAmplitudeLe :=
      complexCoordinateAmplitudeSq_le_three_mul_norm_sq
        (fixedWaveSpaceTimeRestriction
          requestedTime wave state time)
    rw [← rowsAgree wave]
    unfold wholePointwiseCarrierGradientDensity
    calc
      integerWaveNormSq wave *
          complexCoordinateAmplitudeSq
            (fixedWaveSpaceTimeRestriction
              requestedTime wave state time) ≤
          integerWaveNormSq wave *
            (3 *
              ‖fixedWaveSpaceTimeRestriction
                requestedTime wave state time‖ ^ 2) :=
        mul_le_mul_of_nonneg_left rowAmplitudeLe
          (integerWaveNormSq_nonneg wave)
      _ = 3 *
          (integerWaveNormSq wave *
            ‖fixedWaveSpaceTimeRestriction
              requestedTime wave state time‖ ^ 2) := by ring
  have transported :=
    gradientSummable.tsum_le_tsum
      amplitudeLe dominatingSummable
  simpa only [carrierSummable.tsum_mul_left 3] using transported

theorem wholePointwiseCarrierGradientMass_integrable
    (requestedTime : ℝ)
    (state : SpaceTimeState requestedTime)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        wholeSpaceTimeVorticityGradientDensity
          requestedTime state wave) :
    Integrable
      (fun time =>
        ∑' wave : IntegerWavevector,
          wholePointwiseCarrierGradientDensity
            requestedTime state time wave)
      (commonTimeMeasure requestedTime) := by
  let density : IntegerWavevector →
      Icc (0 : ℝ) requestedTime → ℝ :=
    fun wave time =>
      wholePointwiseCarrierGradientDensity
        requestedTime state time wave
  have densityIntegrable :
      ∀ wave : IntegerWavevector,
        Integrable (density wave)
          (commonTimeMeasure requestedTime) := by
    intro wave
    exact wholePointwiseCarrierGradientDensity_integrable
      requestedTime state wave
  have integralNormSummable :
      Summable fun wave : IntegerWavevector =>
        ∫ time, ‖density wave time‖
          ∂(commonTimeMeasure requestedTime) := by
    apply gradientSummable.congr
    intro wave
    exact (wholePointwiseCarrierGradientDensity_integral_norm
      requestedTime state wave).symm
  have sumAEMeasurable :
      AEStronglyMeasurable
        (fun time => ∑' wave : IntegerWavevector, density wave time)
        (commonTimeMeasure requestedTime) :=
    AEStronglyMeasurable.tsum fun wave =>
      (densityIntegrable wave).aestronglyMeasurable
  have pointwiseSummable :
      ∀ᵐ time ∂(commonTimeMeasure requestedTime),
        Summable fun wave : IntegerWavevector => density wave time :=
    wholePointwiseCarrierGradientDensity_ae_summable
      requestedTime state gradientSummable
  have sumNonneg :
      ∀ᵐ time ∂(commonTimeMeasure requestedTime),
        0 ≤ ∑' wave : IntegerWavevector, density wave time := by
    filter_upwards with time
    exact tsum_nonneg fun wave =>
      wholePointwiseCarrierGradientDensity_nonneg
        requestedTime state time wave
  have integralTsum :
      (∑' wave : IntegerWavevector,
          ∫ time, density wave time
            ∂(commonTimeMeasure requestedTime)) =
        ∫ time,
          ∑' wave : IntegerWavevector, density wave time
            ∂(commonTimeMeasure requestedTime) :=
    integral_tsum_of_summable_integral_norm
      densityIntegrable integralNormSummable
  have sumIntegralFinite :
      HasFiniteIntegral
        (fun time =>
          ∑' wave : IntegerWavevector, density wave time)
        (commonTimeMeasure requestedTime) := by
    rw [hasFiniteIntegral_iff_ofReal sumNonneg]
    have densityEnormAEMeasurable :
        ∀ wave : IntegerWavevector,
          AEMeasurable (fun time => ‖density wave time‖ₑ)
            (commonTimeMeasure requestedTime) :=
      fun wave => (densityIntegrable wave).aestronglyMeasurable.enorm
    have lintegralTsumNeTop :
        lintegral (commonTimeMeasure requestedTime)
            (fun time =>
              tsum fun wave : IntegerWavevector =>
                ‖density wave time‖ₑ) ≠ ⊤ := by
      rw [lintegral_tsum densityEnormAEMeasurable]
      have lintegralEq :
          ∀ wave : IntegerWavevector,
            lintegral (commonTimeMeasure requestedTime)
                (fun time => ‖density wave time‖ₑ) =
              ‖∫ time, ‖density wave time‖
                  ∂(commonTimeMeasure requestedTime)‖ₑ := by
        intro wave
        rw [Real.enorm_of_nonneg
          (integral_nonneg fun time => norm_nonneg _)]
        exact
          (ofReal_integral_norm_eq_lintegral_enorm
            (densityIntegrable wave)).symm
      rw [funext lintegralEq]
      exact ENNReal.tsum_coe_ne_top_iff_summable.2 <|
        NNReal.summable_coe.1 integralNormSummable.abs
    have densityNonneg :
        ∀ time wave, 0 ≤ density wave time := by
      intro time wave
      exact wholePointwiseCarrierGradientDensity_nonneg
        requestedTime state time wave
    have enormTsum :
        (fun time =>
          ENNReal.ofReal
            (∑' wave : IntegerWavevector, density wave time)) =ᵐ[
              commonTimeMeasure requestedTime]
          fun time =>
            ∑' wave : IntegerWavevector,
              ‖density wave time‖ₑ := by
      filter_upwards [pointwiseSummable] with time timeSummable
      rw [ENNReal.ofReal_tsum_of_nonneg
        (densityNonneg time) timeSummable]
      apply tsum_congr
      intro wave
      exact (Real.enorm_of_nonneg
        (densityNonneg time wave)).symm
    rw [lintegral_congr_ae enormTsum]
    exact lt_top_iff_ne_top.2 lintegralTsumNeTop
  refine ⟨?_, ?_⟩
  · simpa only [density] using sumAEMeasurable
  · simpa only [density] using sumIntegralFinite

theorem wholePointwiseCarrierGradientMass_integral
    (requestedTime : ℝ)
    (state : SpaceTimeState requestedTime)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        wholeSpaceTimeVorticityGradientDensity
          requestedTime state wave) :
    (∫ time,
        ∑' wave : IntegerWavevector,
          wholePointwiseCarrierGradientDensity
            requestedTime state time wave
        ∂(commonTimeMeasure requestedTime)) =
      wholeSpaceTimeVorticityGradientMass
        requestedTime state := by
  let density : IntegerWavevector →
      Icc (0 : ℝ) requestedTime → ℝ :=
    fun wave time =>
      wholePointwiseCarrierGradientDensity
        requestedTime state time wave
  have densityIntegrable :
      ∀ wave : IntegerWavevector,
        Integrable (density wave)
          (commonTimeMeasure requestedTime) := by
    intro wave
    exact wholePointwiseCarrierGradientDensity_integrable
      requestedTime state wave
  have integralNormSummable :
      Summable fun wave : IntegerWavevector =>
        ∫ time, ‖density wave time‖
          ∂(commonTimeMeasure requestedTime) := by
    apply gradientSummable.congr
    intro wave
    exact (wholePointwiseCarrierGradientDensity_integral_norm
      requestedTime state wave).symm
  rw [← integral_tsum_of_summable_integral_norm
    densityIntegrable integralNormSummable]
  unfold wholeSpaceTimeVorticityGradientMass
  apply tsum_congr
  intro wave
  exact wholePointwiseCarrierGradientDensity_integral
    requestedTime state wave

theorem wholeVelocityMajorantSq_integrable
    (requestedTime : ℝ)
    (state : SpaceTimeState requestedTime)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        wholeSpaceTimeVorticityGradientDensity
          requestedTime state wave) :
    Integrable
      (fun time => wholeStateVelocityMajorant (state time) ^ 2)
      (commonTimeMeasure requestedTime) := by
  have pointwiseGradientSummable :=
    wholePointwiseGradientDensity_ae_summable
      requestedTime state gradientSummable
  have carrierSummable :=
    wholePointwiseCarrierGradientDensity_ae_summable
      requestedTime state gradientSummable
  have rowsAgree :
      ∀ᵐ time ∂(commonTimeMeasure requestedTime),
        ∀ wave : IntegerWavevector,
          fixedWaveSpaceTimeRestriction
              requestedTime wave state time =
            state time wave :=
    eventually_countable_forall.2 fun wave =>
      fixedWaveSpaceTimeRestriction_coeFn
        requestedTime wave state
  have pointwiseBound :
      ∀ᵐ time ∂(commonTimeMeasure requestedTime),
        wholeStateVelocityMajorant (state time) ^ 2 ≤
          3 *
            (biotSavartSerrinConstant *
              (∑' wave : IntegerWavevector,
                integerWaveCriticalKernel wave)) *
            (∑' wave : IntegerWavevector,
              wholePointwiseCarrierGradientDensity
                requestedTime state time wave) := by
    filter_upwards [pointwiseGradientSummable,
      carrierSummable, rowsAgree] with
      time timeGradientSummable timeCarrierSummable timeRowsAgree
    have staticBound :=
      wholeStateVelocityMajorant_sq_le_criticalGlobal
        (state time) timeGradientSummable
    have gradientMassLe :
        wholeStateVorticityGradientMass (state time) ≤
          3 *
            ∑' wave : IntegerWavevector,
              wholePointwiseCarrierGradientDensity
                requestedTime state time wave :=
      wholeStateGradientMass_le_three_mul_pointwiseCarrierMass
        requestedTime state time timeRowsAgree
        timeCarrierSummable timeGradientSummable
    have criticalConstantNonneg :
        0 ≤
          biotSavartSerrinConstant *
            (∑' wave : IntegerWavevector,
              integerWaveCriticalKernel wave) :=
      mul_nonneg biotSavartSerrinConstant_nonneg
        integerWaveCriticalKernel_tsum_nonneg
    exact staticBound.trans <| by
      nlinarith
  have majorantAEMeasurable :
      AEStronglyMeasurable
        (fun time => wholeStateVelocityMajorant (state time) ^ 2)
        (commonTimeMeasure requestedTime) := by
    have stateMeasurable :
        AEStronglyMeasurable
          (fun time => state time)
          (commonTimeMeasure requestedTime) :=
      MeasureTheory.Lp.aestronglyMeasurable state
    have termMeasurable :
        ∀ wave : IntegerWavevector,
          AEStronglyMeasurable
            (fun time =>
              Real.sqrt
                (complexCoordinateAmplitudeSq
                  (finiteStateVelocityCoefficient
                    (state time) wave)))
            (commonTimeMeasure requestedTime) := by
      intro wave
      exact
        (wholeVelocityAmplitudeTerm_continuous wave)
          |>.comp_aestronglyMeasurable stateMeasurable
    exact
      ((AEStronglyMeasurable.tsum termMeasurable).pow 2)
  have carrierMassIntegrable :=
    wholePointwiseCarrierGradientMass_integrable
      requestedTime state gradientSummable
  apply
    (carrierMassIntegrable.const_mul
      (3 *
        (biotSavartSerrinConstant *
          (∑' wave : IntegerWavevector,
            integerWaveCriticalKernel wave)))).mono_nonneg
      majorantAEMeasurable
  · filter_upwards with time
    exact sq_nonneg _
  · exact pointwiseBound

theorem wholeVelocityMajorantSq_integral_le
    (requestedTime : ℝ)
    (state : SpaceTimeState requestedTime)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        wholeSpaceTimeVorticityGradientDensity
          requestedTime state wave) :
    (∫ time,
        wholeStateVelocityMajorant (state time) ^ 2
        ∂(commonTimeMeasure requestedTime)) ≤
      3 *
        (biotSavartSerrinConstant *
          (∑' wave : IntegerWavevector,
            integerWaveCriticalKernel wave)) *
        wholeSpaceTimeVorticityGradientMass
          requestedTime state := by
  have pointwiseGradientSummable :=
    wholePointwiseGradientDensity_ae_summable
      requestedTime state gradientSummable
  have carrierSummable :=
    wholePointwiseCarrierGradientDensity_ae_summable
      requestedTime state gradientSummable
  have rowsAgree :
      ∀ᵐ time ∂(commonTimeMeasure requestedTime),
        ∀ wave : IntegerWavevector,
          fixedWaveSpaceTimeRestriction
              requestedTime wave state time =
            state time wave :=
    eventually_countable_forall.2 fun wave =>
      fixedWaveSpaceTimeRestriction_coeFn
        requestedTime wave state
  have pointwiseBound :
      ∀ᵐ time ∂(commonTimeMeasure requestedTime),
        wholeStateVelocityMajorant (state time) ^ 2 ≤
          3 *
            (biotSavartSerrinConstant *
              (∑' wave : IntegerWavevector,
                integerWaveCriticalKernel wave)) *
            (∑' wave : IntegerWavevector,
              wholePointwiseCarrierGradientDensity
                requestedTime state time wave) := by
    filter_upwards [pointwiseGradientSummable,
      carrierSummable, rowsAgree] with
      time timeGradientSummable timeCarrierSummable timeRowsAgree
    have staticBound :=
      wholeStateVelocityMajorant_sq_le_criticalGlobal
        (state time) timeGradientSummable
    have gradientMassLe :
        wholeStateVorticityGradientMass (state time) ≤
          3 *
            ∑' wave : IntegerWavevector,
              wholePointwiseCarrierGradientDensity
                requestedTime state time wave :=
      wholeStateGradientMass_le_three_mul_pointwiseCarrierMass
        requestedTime state time timeRowsAgree
        timeCarrierSummable timeGradientSummable
    have criticalConstantNonneg :
        0 ≤
          biotSavartSerrinConstant *
            (∑' wave : IntegerWavevector,
              integerWaveCriticalKernel wave) :=
      mul_nonneg biotSavartSerrinConstant_nonneg
        integerWaveCriticalKernel_tsum_nonneg
    exact staticBound.trans <| by
      nlinarith
  calc
    (∫ time,
        wholeStateVelocityMajorant (state time) ^ 2
        ∂(commonTimeMeasure requestedTime)) ≤
        ∫ time,
          3 *
            (biotSavartSerrinConstant *
              (∑' wave : IntegerWavevector,
                integerWaveCriticalKernel wave)) *
            (∑' wave : IntegerWavevector,
              wholePointwiseCarrierGradientDensity
                requestedTime state time wave)
          ∂(commonTimeMeasure requestedTime) := by
      exact integral_mono_ae
        (wholeVelocityMajorantSq_integrable
          requestedTime state gradientSummable)
        ((wholePointwiseCarrierGradientMass_integrable
          requestedTime state gradientSummable).const_mul
            (3 *
              (biotSavartSerrinConstant *
                (∑' wave : IntegerWavevector,
                  integerWaveCriticalKernel wave))))
        pointwiseBound
    _ =
        3 *
          (biotSavartSerrinConstant *
            (∑' wave : IntegerWavevector,
              integerWaveCriticalKernel wave)) *
          wholeSpaceTimeVorticityGradientMass
            requestedTime state := by
      rw [integral_const_mul]
      rw [wholePointwiseCarrierGradientMass_integral
        requestedTime state gradientSummable]

end

end ThreeDimensionalVorticityCoefficientWholeSpaceTimeCriticalSerrin
end NavierStokes
end SaturationMonoid
