import H0mework.NavierStokes.ShellSources.FixedWaveNonlinearL2

/-!
# Whole space-time viscous negative-one carrier

The Fourier multiplier of the viscous vorticity term is unbounded on the
plain coefficient Hilbert space.  On the actual whole-gradient domain,
however, its inverse-Laplacian weighted row is square summable:

`sqrt((-Δ)_k)⁻¹ ν (-Δ)_k ω_k = ν sqrt((-Δ)_k) ω_k`.

This module installs that row in the same time-`L²`, coefficient-`ℓ²`
negative-one carrier used by the nonlinear forcing.  The construction uses
canonical finite frequency projections, so measurability and carrier
membership are generated from the whole-gradient budget.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientWholeSpaceTimeViscousNegativeOne

open scoped BigOperators ENNReal Topology

open Filter
open MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientFiniteGalerkinAmbientNorm
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeSubsequence
open ThreeDimensionalVorticityCoefficientGeneratedPathInfiniteNonlinearRowLimit
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeGradientLowerSemicontinuity
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeCriticalSerrin
open ThreeDimensionalVorticityCoefficientInfiniteFixedWaveWeakCarrier
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageReceiptSquare
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageReceiptSquare.GeneratedIntegerShellInfiniteLineage
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellCriticalSerrinWeakLimit
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellNonlinearNegativeOneForcing
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellFixedWaveNonlinearL2
open ThreeDimensionalVorticityCoefficientTransverseSpaceTimeNonlinearRow

noncomputable section

/-! ## Pointwise whole-carrier construction -/

/-- The inverse-Laplacian weighted viscous Fourier row. -/
def wholeStateVorticityViscousNegativeOneWeightedCoefficient
    (ν : ℝ)
    (state : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) : ComplexCoordinateVector :=
  (ν * Real.sqrt (integerWaveViscousMultiplier wave)) • state wave

theorem
    wholeStateVorticityViscousNegativeOneWeightedCoefficient_norm_sq_le
    (ν : ℝ)
    (state : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) :
    ‖wholeStateVorticityViscousNegativeOneWeightedCoefficient
        ν state wave‖ ^ 2 ≤
      ν ^ 2 * integerWaveViscousMultiplier wave *
        complexCoordinateAmplitudeSq (state wave) := by
  have multiplierNonneg :
      0 ≤ integerWaveViscousMultiplier wave := by
    unfold integerWaveViscousMultiplier
    exact mul_nonneg (sq_nonneg _) (integerWaveNormSq_nonneg wave)
  rw [wholeStateVorticityViscousNegativeOneWeightedCoefficient,
    norm_smul, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [mul_pow, mul_pow, Real.sq_sqrt multiplierNonneg]
  have rowLe :=
    complexCoordinateVector_norm_sq_le_amplitudeSq (state wave)
  have scalarNonneg :
      0 ≤ |ν| ^ 2 * integerWaveViscousMultiplier wave :=
    mul_nonneg (sq_nonneg _) multiplierNonneg
  calc
    |ν| ^ 2 * integerWaveViscousMultiplier wave * ‖state wave‖ ^ 2 ≤
        (|ν| ^ 2 * integerWaveViscousMultiplier wave) *
          complexCoordinateAmplitudeSq (state wave) :=
      mul_le_mul_of_nonneg_left rowLe scalarNonneg
    _ =
        ν ^ 2 * integerWaveViscousMultiplier wave *
          complexCoordinateAmplitudeSq (state wave) := by
      rw [sq_abs]

/-- The weighted viscous row as one actual coefficient Hilbert state. -/
def wholeStateVorticityViscousNegativeOneState
    (ν : ℝ)
    (state : ComplexVorticityHilbertState)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (state wave)) :
    ComplexVorticityHilbertState :=
  ⟨wholeStateVorticityViscousNegativeOneWeightedCoefficient ν state, by
    apply memℓp_gen
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      ((gradientSummable.mul_left
          (ν ^ 2 * (2 * Real.pi) ^ 2)).of_nonneg_of_le
        (fun wave => sq_nonneg _)
        (fun wave => by
          calc
            ‖wholeStateVorticityViscousNegativeOneWeightedCoefficient
                ν state wave‖ ^ 2 ≤
                ν ^ 2 * integerWaveViscousMultiplier wave *
                  complexCoordinateAmplitudeSq (state wave) :=
              wholeStateVorticityViscousNegativeOneWeightedCoefficient_norm_sq_le
                ν state wave
            _ =
                (ν ^ 2 * (2 * Real.pi) ^ 2) *
                  (integerWaveNormSq wave *
                    complexCoordinateAmplitudeSq (state wave)) := by
              unfold integerWaveViscousMultiplier
              ring))⟩

@[simp] theorem wholeStateVorticityViscousNegativeOneState_apply
    (ν : ℝ)
    (state : ComplexVorticityHilbertState)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (state wave))
    (wave : IntegerWavevector) :
    wholeStateVorticityViscousNegativeOneState
        ν state gradientSummable wave =
      wholeStateVorticityViscousNegativeOneWeightedCoefficient
        ν state wave := rfl

/-- Applying one square-root Laplacian recovers the actual viscous row. -/
theorem
    sqrt_viscousMultiplier_smul_wholeStateVorticityViscousNegativeOneState_apply
    (ν : ℝ)
    (state : ComplexVorticityHilbertState)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (state wave))
    (wave : IntegerWavevector) :
    Real.sqrt (integerWaveViscousMultiplier wave) •
        wholeStateVorticityViscousNegativeOneState
          ν state gradientSummable wave =
      (ν * integerWaveViscousMultiplier wave) • state wave := by
  rw [wholeStateVorticityViscousNegativeOneState_apply,
    wholeStateVorticityViscousNegativeOneWeightedCoefficient, smul_smul]
  congr 1
  have multiplierNonneg :
      0 ≤ integerWaveViscousMultiplier wave := by
    unfold integerWaveViscousMultiplier
    exact mul_nonneg (sq_nonneg _) (integerWaveNormSq_nonneg wave)
  calc
    Real.sqrt (integerWaveViscousMultiplier wave) *
          (ν * Real.sqrt (integerWaveViscousMultiplier wave)) =
        ν *
          (Real.sqrt (integerWaveViscousMultiplier wave) *
            Real.sqrt (integerWaveViscousMultiplier wave)) := by ring
    _ = ν * integerWaveViscousMultiplier wave := by
      rw [Real.mul_self_sqrt multiplierNonneg]

/-! ## Canonical finite approximations and measurability -/

/-- Finite frequency approximation to the weighted viscous state. -/
def wholeViscousNegativeOneFiniteApproximation
    (radius : ℕ)
    (ν : ℝ)
    (state : ComplexVorticityHilbertState) :
    ComplexVorticityHilbertState :=
  finiteComplexVorticityState
    (integerWaveFrequencyCube radius)
    (wholeStateVorticityViscousNegativeOneWeightedCoefficient ν state)

theorem wholeViscousNegativeOneFiniteApproximation_continuous
    (radius : ℕ)
    (ν : ℝ) :
    Continuous
      (wholeViscousNegativeOneFiniteApproximation radius ν) := by
  unfold wholeViscousNegativeOneFiniteApproximation
    finiteComplexVorticityState
    wholeStateVorticityViscousNegativeOneWeightedCoefficient
  apply continuous_finsetSum
  intro wave waveMem
  exact
    (lp.singleContinuousLinearMap ℂ
      (fun _ : IntegerWavevector => ComplexCoordinateVector)
      2 wave).continuous.comp
        ((complexVorticityEvaluation_contDiff wave).continuous.const_smul
          (ν * Real.sqrt (integerWaveViscousMultiplier wave)))

theorem wholeViscousNegativeOneFiniteApproximation_eq_projection
    (radius : ℕ)
    (ν : ℝ)
    (state : ComplexVorticityHilbertState)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (state wave)) :
    wholeViscousNegativeOneFiniteApproximation radius ν state =
      complexSharpSupportProjection
        (integerWaveFrequencyCube radius)
        (wholeStateVorticityViscousNegativeOneState
          ν state gradientSummable) := by
  ext wave
  simp [wholeViscousNegativeOneFiniteApproximation,
    complexSharpSupportProjection_apply]

theorem wholeViscousNegativeOneFiniteApproximation_tendsto
    (ν : ℝ)
    (state : ComplexVorticityHilbertState)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (state wave)) :
    Tendsto
      (fun radius =>
        wholeViscousNegativeOneFiniteApproximation radius ν state)
      atTop
      (𝓝
        (wholeStateVorticityViscousNegativeOneState
          ν state gradientSummable)) := by
  simpa only [
    wholeViscousNegativeOneFiniteApproximation_eq_projection
      _ ν state gradientSummable] using
    complexSharpSupportProjection_frequencyCube_tendsto
      (wholeStateVorticityViscousNegativeOneState
        ν state gradientSummable)

/-- Pointwise weighted viscous forcing, canonically zero on the null set
where the whole Euclidean gradient density is not summable. -/
def wholeSpaceTimeViscousNegativeOneFunction
    {requestedTime : ℝ}
    (ν : ℝ)
    (state : SpaceTimeState requestedTime)
    (time : Set.Icc (0 : ℝ) requestedTime) :
    ComplexVorticityHilbertState := by
  classical
  exact
    if gradientSummable :
        Summable fun wave : IntegerWavevector =>
          integerWaveNormSq wave *
            complexCoordinateAmplitudeSq (state time wave)
    then
      wholeStateVorticityViscousNegativeOneState
        ν (state time) gradientSummable
    else 0

theorem wholeSpaceTimeViscousNegativeOneFunction_of_summable
    {requestedTime : ℝ}
    (ν : ℝ)
    (state : SpaceTimeState requestedTime)
    (time : Set.Icc (0 : ℝ) requestedTime)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (state time wave)) :
    wholeSpaceTimeViscousNegativeOneFunction ν state time =
      wholeStateVorticityViscousNegativeOneState
        ν (state time) gradientSummable := by
  classical
  unfold wholeSpaceTimeViscousNegativeOneFunction
  rw [dif_pos gradientSummable]

theorem wholeSpaceTimeViscousNegativeOneFunction_aestronglyMeasurable
    {requestedTime : ℝ}
    (ν : ℝ)
    (state : SpaceTimeState requestedTime)
    (pointwiseGradientSummable :
      ∀ᵐ time ∂(commonTimeMeasure requestedTime),
        Summable fun wave : IntegerWavevector =>
          integerWaveNormSq wave *
            complexCoordinateAmplitudeSq (state time wave)) :
    AEStronglyMeasurable
      (wholeSpaceTimeViscousNegativeOneFunction ν state)
      (commonTimeMeasure requestedTime) := by
  have finiteMeasurable :
      ∀ radius : ℕ,
        AEStronglyMeasurable
          (fun time =>
            wholeViscousNegativeOneFiniteApproximation
              radius ν (state time))
          (commonTimeMeasure requestedTime) := by
    intro radius
    exact
      (wholeViscousNegativeOneFiniteApproximation_continuous radius ν)
        |>.comp_aestronglyMeasurable
          (MeasureTheory.Lp.aestronglyMeasurable state)
  apply aestronglyMeasurable_of_tendsto_ae atTop finiteMeasurable
  filter_upwards [pointwiseGradientSummable] with
    time timeGradientSummable
  rw [wholeSpaceTimeViscousNegativeOneFunction_of_summable
    ν state time timeGradientSummable]
  exact
    wholeViscousNegativeOneFiniteApproximation_tendsto
      ν (state time) timeGradientSummable

/-! ## Time-`L²` carrier and exact viscous recovery -/

theorem wholeSpaceTimeViscousNegativeOneFunction_norm_sq_ae_le
    {requestedTime : ℝ}
    (ν : ℝ)
    (state : SpaceTimeState requestedTime)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        wholeSpaceTimeVorticityGradientDensity
          requestedTime state wave)
    (pointwiseGradientSummable :
      ∀ᵐ time ∂(commonTimeMeasure requestedTime),
        Summable fun wave : IntegerWavevector =>
          integerWaveNormSq wave *
            complexCoordinateAmplitudeSq (state time wave)) :
    ∀ᵐ time ∂(commonTimeMeasure requestedTime),
      ‖wholeSpaceTimeViscousNegativeOneFunction ν state time‖ ^ 2 ≤
        3 * ν ^ 2 * (2 * Real.pi) ^ 2 *
          (∑' wave : IntegerWavevector,
            wholePointwiseCarrierGradientDensity
              requestedTime state time wave) := by
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
  filter_upwards [pointwiseGradientSummable,
    carrierSummable, rowsAgree] with
      time timeGradientSummable timeCarrierSummable timeRowsAgree
  rw [wholeSpaceTimeViscousNegativeOneFunction_of_summable
    ν state time timeGradientSummable]
  rw [show
    ‖wholeStateVorticityViscousNegativeOneState
        ν (state time) timeGradientSummable‖ ^ 2 =
      ∑' wave : IntegerWavevector,
        ‖wholeStateVorticityViscousNegativeOneState
          ν (state time) timeGradientSummable wave‖ ^ 2 by
      simpa using
        (lp.norm_rpow_eq_tsum
          (p := (2 : ℝ≥0∞)) (by norm_num)
          (wholeStateVorticityViscousNegativeOneState
            ν (state time) timeGradientSummable))]
  have stateNormSummable :
      Summable fun wave : IntegerWavevector =>
        ‖wholeStateVorticityViscousNegativeOneState
          ν (state time) timeGradientSummable wave‖ ^ 2 := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      Memℓp.summable (by norm_num)
        (wholeStateVorticityViscousNegativeOneState
          ν (state time) timeGradientSummable).2
  have weightedSummable :
      Summable fun wave : IntegerWavevector =>
        ν ^ 2 * integerWaveViscousMultiplier wave *
          complexCoordinateAmplitudeSq (state time wave) := by
    simpa only [integerWaveViscousMultiplier] using
      (timeGradientSummable.mul_left
        (ν ^ 2 * (2 * Real.pi) ^ 2)).congr
          (fun wave => by ring)
  calc
    (∑' wave : IntegerWavevector,
        ‖wholeStateVorticityViscousNegativeOneState
          ν (state time) timeGradientSummable wave‖ ^ 2) ≤
        ∑' wave : IntegerWavevector,
          ν ^ 2 * integerWaveViscousMultiplier wave *
            complexCoordinateAmplitudeSq (state time wave) := by
      exact Summable.tsum_le_tsum
        (fun wave =>
          wholeStateVorticityViscousNegativeOneWeightedCoefficient_norm_sq_le
            ν (state time) wave)
        stateNormSummable weightedSummable
    _ =
        ν ^ 2 * (2 * Real.pi) ^ 2 *
          (∑' wave : IntegerWavevector,
            integerWaveNormSq wave *
              complexCoordinateAmplitudeSq (state time wave)) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro wave
      unfold integerWaveViscousMultiplier
      ring
    _ ≤
        ν ^ 2 * (2 * Real.pi) ^ 2 *
          (3 *
            ∑' wave : IntegerWavevector,
              wholePointwiseCarrierGradientDensity
                requestedTime state time wave) := by
      apply mul_le_mul_of_nonneg_left
      · exact
          wholeStateGradientMass_le_three_mul_pointwiseCarrierMass
            requestedTime state time timeRowsAgree
              timeCarrierSummable timeGradientSummable
      · exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
    _ =
        3 * ν ^ 2 * (2 * Real.pi) ^ 2 *
          (∑' wave : IntegerWavevector,
            wholePointwiseCarrierGradientDensity
              requestedTime state time wave) := by ring

theorem wholeSpaceTimeViscousNegativeOneFunction_integrable_norm_sq
    {requestedTime : ℝ}
    (ν : ℝ)
    (state : SpaceTimeState requestedTime)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        wholeSpaceTimeVorticityGradientDensity
          requestedTime state wave)
    (pointwiseGradientSummable :
      ∀ᵐ time ∂(commonTimeMeasure requestedTime),
        Summable fun wave : IntegerWavevector =>
          integerWaveNormSq wave *
            complexCoordinateAmplitudeSq (state time wave)) :
    Integrable
      (fun time =>
        ‖wholeSpaceTimeViscousNegativeOneFunction ν state time‖ ^ 2)
      (commonTimeMeasure requestedTime) := by
  have forcingAEMeasurable :=
    wholeSpaceTimeViscousNegativeOneFunction_aestronglyMeasurable
      ν state pointwiseGradientSummable
  have pointwiseBound :=
    wholeSpaceTimeViscousNegativeOneFunction_norm_sq_ae_le
      ν state gradientSummable pointwiseGradientSummable
  have carrierMassIntegrable :=
    wholePointwiseCarrierGradientMass_integrable
      requestedTime state gradientSummable
  apply
    (carrierMassIntegrable.const_mul
      (3 * ν ^ 2 * (2 * Real.pi) ^ 2)).mono_nonneg
      (forcingAEMeasurable.norm.pow 2)
  · filter_upwards with time
    exact sq_nonneg _
  · exact pointwiseBound

theorem wholeSpaceTimeViscousNegativeOneFunction_memLp
    {requestedTime : ℝ}
    (ν : ℝ)
    (state : SpaceTimeState requestedTime)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        wholeSpaceTimeVorticityGradientDensity
          requestedTime state wave)
    (pointwiseGradientSummable :
      ∀ᵐ time ∂(commonTimeMeasure requestedTime),
        Summable fun wave : IntegerWavevector =>
          integerWaveNormSq wave *
            complexCoordinateAmplitudeSq (state time wave)) :
    MemLp
      (wholeSpaceTimeViscousNegativeOneFunction ν state)
      2 (commonTimeMeasure requestedTime) := by
  have forcingAEMeasurable :=
    wholeSpaceTimeViscousNegativeOneFunction_aestronglyMeasurable
      ν state pointwiseGradientSummable
  exact
    (memLp_two_iff_integrable_sq_norm forcingAEMeasurable).2
      (wholeSpaceTimeViscousNegativeOneFunction_integrable_norm_sq
        ν state gradientSummable pointwiseGradientSummable)

/-- The actual weighted viscous row installed in time-`L²`. -/
def wholeSpaceTimeViscousNegativeOneState
    {requestedTime : ℝ}
    (ν : ℝ)
    (state : SpaceTimeState requestedTime)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        wholeSpaceTimeVorticityGradientDensity
          requestedTime state wave)
    (pointwiseGradientSummable :
      ∀ᵐ time ∂(commonTimeMeasure requestedTime),
        Summable fun wave : IntegerWavevector =>
          integerWaveNormSq wave *
            complexCoordinateAmplitudeSq (state time wave)) :
    SpaceTimeState requestedTime :=
  (wholeSpaceTimeViscousNegativeOneFunction_memLp
    ν state gradientSummable pointwiseGradientSummable).toLp
      (wholeSpaceTimeViscousNegativeOneFunction ν state)

theorem wholeSpaceTimeViscousNegativeOneState_coeFn
    {requestedTime : ℝ}
    (ν : ℝ)
    (state : SpaceTimeState requestedTime)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        wholeSpaceTimeVorticityGradientDensity
          requestedTime state wave)
    (pointwiseGradientSummable :
      ∀ᵐ time ∂(commonTimeMeasure requestedTime),
        Summable fun wave : IntegerWavevector =>
          integerWaveNormSq wave *
            complexCoordinateAmplitudeSq (state time wave)) :
    wholeSpaceTimeViscousNegativeOneState
        ν state gradientSummable pointwiseGradientSummable =ᵐ[
          commonTimeMeasure requestedTime]
      wholeSpaceTimeViscousNegativeOneFunction ν state := by
  exact
    (wholeSpaceTimeViscousNegativeOneFunction_memLp
      ν state gradientSummable pointwiseGradientSummable).coeFn_toLp

theorem wholeSpaceTimeViscousNegativeOneState_norm_sq_le
    {requestedTime : ℝ}
    (ν : ℝ)
    (state : SpaceTimeState requestedTime)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        wholeSpaceTimeVorticityGradientDensity
          requestedTime state wave)
    (pointwiseGradientSummable :
      ∀ᵐ time ∂(commonTimeMeasure requestedTime),
        Summable fun wave : IntegerWavevector =>
          integerWaveNormSq wave *
            complexCoordinateAmplitudeSq (state time wave)) :
    ‖wholeSpaceTimeViscousNegativeOneState
        ν state gradientSummable pointwiseGradientSummable‖ ^ 2 ≤
      3 * ν ^ 2 * (2 * Real.pi) ^ 2 *
        wholeSpaceTimeVorticityGradientMass requestedTime state := by
  rw [spaceTime_norm_sq_eq_integral]
  calc
    (∫ time,
        ‖wholeSpaceTimeViscousNegativeOneState
          ν state gradientSummable pointwiseGradientSummable time‖ ^ 2
        ∂(commonTimeMeasure requestedTime)) =
        ∫ time,
          ‖wholeSpaceTimeViscousNegativeOneFunction ν state time‖ ^ 2
          ∂(commonTimeMeasure requestedTime) := by
      apply integral_congr_ae
      filter_upwards [
        wholeSpaceTimeViscousNegativeOneState_coeFn
          ν state gradientSummable pointwiseGradientSummable] with
          time forcingEq
      rw [forcingEq]
    _ ≤
        ∫ time,
          3 * ν ^ 2 * (2 * Real.pi) ^ 2 *
            (∑' wave : IntegerWavevector,
              wholePointwiseCarrierGradientDensity
                requestedTime state time wave)
          ∂(commonTimeMeasure requestedTime) := by
      exact integral_mono_ae
        (wholeSpaceTimeViscousNegativeOneFunction_integrable_norm_sq
          ν state gradientSummable pointwiseGradientSummable)
        ((wholePointwiseCarrierGradientMass_integrable
          requestedTime state gradientSummable).const_mul
            (3 * ν ^ 2 * (2 * Real.pi) ^ 2))
        (wholeSpaceTimeViscousNegativeOneFunction_norm_sq_ae_le
          ν state gradientSummable pointwiseGradientSummable)
    _ =
        3 * ν ^ 2 * (2 * Real.pi) ^ 2 *
          wholeSpaceTimeVorticityGradientMass requestedTime state := by
      rw [integral_const_mul]
      rw [wholePointwiseCarrierGradientMass_integral
        requestedTime state gradientSummable]

theorem wholeSpaceTimeViscousNegativeOneState_unweighted_row_ae
    {requestedTime : ℝ}
    (ν : ℝ)
    (state : SpaceTimeState requestedTime)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        wholeSpaceTimeVorticityGradientDensity
          requestedTime state wave)
    (pointwiseGradientSummable :
      ∀ᵐ time ∂(commonTimeMeasure requestedTime),
        Summable fun wave : IntegerWavevector =>
          integerWaveNormSq wave *
            complexCoordinateAmplitudeSq (state time wave))
    (wave : IntegerWavevector) :
    ∀ᵐ time ∂(commonTimeMeasure requestedTime),
      Real.sqrt (integerWaveViscousMultiplier wave) •
          (wholeSpaceTimeViscousNegativeOneState
            ν state gradientSummable pointwiseGradientSummable time) wave =
        (ν * integerWaveViscousMultiplier wave) • state time wave := by
  filter_upwards [
    wholeSpaceTimeViscousNegativeOneState_coeFn
      ν state gradientSummable pointwiseGradientSummable,
    pointwiseGradientSummable] with
      time forcingEq timeGradientSummable
  rw [forcingEq,
    wholeSpaceTimeViscousNegativeOneFunction_of_summable
      ν state time timeGradientSummable]
  exact
    sqrt_viscousMultiplier_smul_wholeStateVorticityViscousNegativeOneState_apply
      ν (state time) timeGradientSummable wave

/-! ## Source-generated whole tangent -/

/-- A continuous time test acts identically on two almost-everywhere equal
rows, whether the row is presented in `L²` or in the older `L¹` carrier. -/
theorem fixedL2Action_eq_fixedLInfAction_of_ae
    (requestedTime : ℝ)
    (test : ℝ → ℂ)
    (testContinuous :
      ContinuousOn test (Set.Icc (0 : ℝ) requestedTime))
    (rowL2 : FixedWaveSpaceTimeState requestedTime)
    (rowL1 : NonlinearRowSpaceTimeState requestedTime)
    (rowEq :
      rowL2 =ᵐ[commonTimeMeasure requestedTime] rowL1) :
    fixedL2ScalarL2IntegralCLM requestedTime
        (restrictedScalarL2 requestedTime test testContinuous) rowL2 =
      fixedLInfScalarL1IntegralCLM requestedTime
        (restrictedScalarLInf requestedTime test testContinuous) rowL1 := by
  let scalarL2 :=
    restrictedScalarL2 requestedTime test testContinuous
  let scalarLInf :=
    restrictedScalarLInf requestedTime test testContinuous
  have scalarL2AE :=
    BoundedContinuousFunction.coeFn_toLp
      (p := (2 : ℝ≥0∞))
      (μ := commonTimeMeasure requestedTime) ℂ
      (restrictedScalarBoundedPath
        requestedTime test testContinuous)
  have scalarLInfAE :=
    BoundedContinuousFunction.coeFn_toLp
      (p := (∞ : ℝ≥0∞))
      (μ := commonTimeMeasure requestedTime) ℂ
      (restrictedScalarBoundedPath
        requestedTime test testContinuous)
  have productL2AE :
      ⇑(scalarL2 • rowL2 :
          MeasureTheory.Lp ComplexCoordinateVector 1
            (commonTimeMeasure requestedTime)) =ᵐ[
          commonTimeMeasure requestedTime]
        ⇑scalarL2 • ⇑rowL2 :=
    MeasureTheory.Lp.coeFn_lpSMul scalarL2 rowL2
  have productLInfAE :
      ⇑(scalarLInf • rowL1 :
          MeasureTheory.Lp ComplexCoordinateVector 1
            (commonTimeMeasure requestedTime)) =ᵐ[
          commonTimeMeasure requestedTime]
        ⇑scalarLInf • ⇑rowL1 :=
    MeasureTheory.Lp.coeFn_lpSMul scalarLInf rowL1
  change
    (MeasureTheory.L1.integralCLM' ℂ)
        (scalarL2 • rowL2) =
      (MeasureTheory.L1.integralCLM' ℂ)
        (scalarLInf • rowL1)
  rw [← MeasureTheory.L1.integral_eq' ℂ,
    ← MeasureTheory.L1.integral_eq' ℂ,
    MeasureTheory.L1.integral_eq_integral,
    MeasureTheory.L1.integral_eq_integral]
  apply integral_congr_ae
  filter_upwards [productL2AE, productLInfAE,
    scalarL2AE, scalarLInfAE, rowEq] with
      time productL2Eq productLInfEq
      scalarL2Eq scalarLInfEq rowPointEq
  rw [productL2Eq, productLInfEq]
  change scalarL2 time • rowL2 time =
    scalarLInf time • rowL1 time
  have scalarL2Point : scalarL2 time = test time.1 := by
    have scalarL2Point' :
        scalarL2 time =
          restrictedScalarBoundedPath requestedTime test
            testContinuous time := by
      simpa [scalarL2, restrictedScalarL2] using scalarL2Eq
    exact scalarL2Point'.trans rfl
  have scalarLInfPoint : scalarLInf time = test time.1 := by
    have scalarLInfPoint' :
        scalarLInf time =
          restrictedScalarBoundedPath requestedTime test
            testContinuous time := by
      simpa [scalarLInf, restrictedScalarLInf] using scalarLInfEq
    exact scalarLInfPoint'.trans rfl
  rw [scalarL2Point, scalarLInfPoint, rowPointEq]

/-- The weighted viscous half of the actual source-generated weak tangent. -/
def NonlinearNegativeOneForcingReceipt.wholeViscousNegativeOneForcing
    {lineage : GeneratedIntegerShellInfiniteLineage}
    {ν : Viscosity}
    {θ requestedTime : ℝ}
    {θLtOne : θ < 1}
    {criticalMargin :
      ∀ length : ℕ,
        criticalEnstrophyLatticeConstant *
            finiteStateVorticityCoefficientEnstrophy
              (generatedSupport (lineage.current length))
              (generatedComplexVorticityState
                (lineage.current length)
                (generatedSupport (lineage.current length))) ≤
          θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2}
    {requestedTimePos : 0 < requestedTime}
    (receipt :
      NonlinearNegativeOneForcingReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos) :
    SpaceTimeState requestedTime :=
  wholeSpaceTimeViscousNegativeOneState
    ν.coeff receipt.stateLimit receipt.gradient_summable
      receipt.pointwiseGradient_ae_summable

/-- The complete vorticity tangent `N(ω) - ν(-Δ)ω` in
`L²_t H⁻¹_x`, generated by the same source receipt. -/
def NonlinearNegativeOneForcingReceipt.wholeNegativeOneTangent
    {lineage : GeneratedIntegerShellInfiniteLineage}
    {ν : Viscosity}
    {θ requestedTime : ℝ}
    {θLtOne : θ < 1}
    {criticalMargin :
      ∀ length : ℕ,
        criticalEnstrophyLatticeConstant *
            finiteStateVorticityCoefficientEnstrophy
              (generatedSupport (lineage.current length))
              (generatedComplexVorticityState
                (lineage.current length)
                (generatedSupport (lineage.current length))) ≤
          θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2}
    {requestedTimePos : 0 < requestedTime}
    (receipt :
      NonlinearNegativeOneForcingReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos) :
    SpaceTimeState requestedTime :=
  receipt.negativeOneForcing -
    NonlinearNegativeOneForcingReceipt.wholeViscousNegativeOneForcing receipt

theorem NonlinearNegativeOneForcingReceipt.wholeViscousNegativeOneForcing_norm_sq_le
    {lineage : GeneratedIntegerShellInfiniteLineage}
    {ν : Viscosity}
    {θ requestedTime : ℝ}
    {θLtOne : θ < 1}
    {criticalMargin :
      ∀ length : ℕ,
        criticalEnstrophyLatticeConstant *
            finiteStateVorticityCoefficientEnstrophy
              (generatedSupport (lineage.current length))
              (generatedComplexVorticityState
                (lineage.current length)
                (generatedSupport (lineage.current length))) ≤
          θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2}
    {requestedTimePos : 0 < requestedTime}
    (receipt :
      NonlinearNegativeOneForcingReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos) :
    ‖NonlinearNegativeOneForcingReceipt.wholeViscousNegativeOneForcing
        receipt‖ ^ 2 ≤
      3 * ν.coeff ^ 2 * (2 * Real.pi) ^ 2 *
        wholeSpaceTimeVorticityGradientMass
          requestedTime receipt.stateLimit := by
  exact
    wholeSpaceTimeViscousNegativeOneState_norm_sq_le
      ν.coeff receipt.stateLimit receipt.gradient_summable
        receipt.pointwiseGradient_ae_summable

/-- Every nonzero wave of the whole tangent is the exact
nonlinear-minus-viscous Fourier generator of the same weak limit. -/
theorem NonlinearNegativeOneForcingReceipt.wholeNegativeOneTangent_unweighted_row_ae
    {lineage : GeneratedIntegerShellInfiniteLineage}
    {ν : Viscosity}
    {θ requestedTime : ℝ}
    {θLtOne : θ < 1}
    {criticalMargin :
      ∀ length : ℕ,
        criticalEnstrophyLatticeConstant *
            finiteStateVorticityCoefficientEnstrophy
              (generatedSupport (lineage.current length))
              (generatedComplexVorticityState
                (lineage.current length)
                (generatedSupport (lineage.current length))) ≤
          θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2}
    {requestedTimePos : 0 < requestedTime}
    (receipt :
      NonlinearNegativeOneForcingReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (wave : IntegerWavevector)
    (waveNe : wave ≠ 0) :
    ∀ᵐ time ∂(commonTimeMeasure requestedTime),
      Real.sqrt (integerWaveViscousMultiplier wave) •
          (NonlinearNegativeOneForcingReceipt.wholeNegativeOneTangent
            receipt time) wave =
        transverseSpaceTimeNonlinearRow
            receipt.transverseLimit wave time -
          (ν.coeff * integerWaveViscousMultiplier wave) •
            receipt.stateLimit time wave := by
  filter_upwards [
    MeasureTheory.Lp.coeFn_sub
      receipt.negativeOneForcing
      (NonlinearNegativeOneForcingReceipt.wholeViscousNegativeOneForcing
        receipt),
    receipt.negativeOneForcing_unweighted_row_ae wave waveNe,
    wholeSpaceTimeViscousNegativeOneState_unweighted_row_ae
      ν.coeff receipt.stateLimit receipt.gradient_summable
        receipt.pointwiseGradient_ae_summable wave] with
      time tangentEq nonlinearEq viscousEq
  rw [NonlinearNegativeOneForcingReceipt.wholeNegativeOneTangent,
    tangentEq]
  change
    Real.sqrt (integerWaveViscousMultiplier wave) •
        ((receipt.negativeOneForcing time) wave -
          (NonlinearNegativeOneForcingReceipt.wholeViscousNegativeOneForcing
            receipt time) wave) =
      _
  have viscousEq' :
      Real.sqrt (integerWaveViscousMultiplier wave) •
          (NonlinearNegativeOneForcingReceipt.wholeViscousNegativeOneForcing
            receipt time) wave =
        (ν.coeff * integerWaveViscousMultiplier wave) •
          receipt.stateLimit time wave := by
    simpa only [
      NonlinearNegativeOneForcingReceipt.wholeViscousNegativeOneForcing]
      using viscousEq
  rw [smul_sub, nonlinearEq, viscousEq']

/-- Unweight one nonzero wave of the whole negative-one tangent. -/
def NonlinearNegativeOneForcingReceipt.fixedWaveNegativeOneTangentL2
    {lineage : GeneratedIntegerShellInfiniteLineage}
    {ν : Viscosity}
    {θ requestedTime : ℝ}
    {θLtOne : θ < 1}
    {criticalMargin :
      ∀ length : ℕ,
        criticalEnstrophyLatticeConstant *
            finiteStateVorticityCoefficientEnstrophy
              (generatedSupport (lineage.current length))
              (generatedComplexVorticityState
                (lineage.current length)
                (generatedSupport (lineage.current length))) ≤
          θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2}
    {requestedTimePos : 0 < requestedTime}
    (receipt :
      NonlinearNegativeOneForcingReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (wave : IntegerWavevector) :
    FixedWaveSpaceTimeState requestedTime :=
  (Real.sqrt (integerWaveViscousMultiplier wave) : ℂ) •
    fixedWaveSpaceTimeRestriction requestedTime wave
      (NonlinearNegativeOneForcingReceipt.wholeNegativeOneTangent
        receipt)

/-- The unweighted whole tangent commutes with pair formation in time:
it is exactly the new `L²` nonlinear row minus the viscous row of the same
state limit. -/
theorem
    NonlinearNegativeOneForcingReceipt.fixedWaveNegativeOneTangentL2_eq
    {lineage : GeneratedIntegerShellInfiniteLineage}
    {ν : Viscosity}
    {θ requestedTime : ℝ}
    {θLtOne : θ < 1}
    {criticalMargin :
      ∀ length : ℕ,
        criticalEnstrophyLatticeConstant *
            finiteStateVorticityCoefficientEnstrophy
              (generatedSupport (lineage.current length))
              (generatedComplexVorticityState
                (lineage.current length)
                (generatedSupport (lineage.current length))) ≤
          θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2}
    {requestedTimePos : 0 < requestedTime}
    (receipt :
      NonlinearNegativeOneForcingReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (wave : IntegerWavevector)
    (waveNe : wave ≠ 0) :
    NonlinearNegativeOneForcingReceipt.fixedWaveNegativeOneTangentL2
        receipt wave =
      NonlinearNegativeOneForcingReceipt.fixedWaveNonlinearL2
          receipt wave -
        (((ν.coeff * integerWaveViscousMultiplier wave : ℝ) : ℂ) •
          fixedWaveSpaceTimeRestriction
            requestedTime wave receipt.stateLimit) := by
  apply MeasureTheory.Lp.ext
  filter_upwards [
    MeasureTheory.Lp.coeFn_smul
      (Real.sqrt (integerWaveViscousMultiplier wave) : ℂ)
      (fixedWaveSpaceTimeRestriction requestedTime wave
        (NonlinearNegativeOneForcingReceipt.wholeNegativeOneTangent
          receipt)),
    fixedWaveSpaceTimeRestriction_coeFn requestedTime wave
      (NonlinearNegativeOneForcingReceipt.wholeNegativeOneTangent
        receipt),
    NonlinearNegativeOneForcingReceipt.wholeNegativeOneTangent_unweighted_row_ae
      receipt wave waveNe,
    MeasureTheory.Lp.coeFn_sub
      (NonlinearNegativeOneForcingReceipt.fixedWaveNonlinearL2
        receipt wave)
      (((ν.coeff * integerWaveViscousMultiplier wave : ℝ) : ℂ) •
        fixedWaveSpaceTimeRestriction requestedTime wave
          receipt.stateLimit),
    NonlinearNegativeOneForcingReceipt.fixedWaveNonlinearL2_coeFn
      receipt wave waveNe,
    MeasureTheory.Lp.coeFn_smul
      (((ν.coeff * integerWaveViscousMultiplier wave : ℝ) : ℂ))
      (fixedWaveSpaceTimeRestriction requestedTime wave
        receipt.stateLimit),
    fixedWaveSpaceTimeRestriction_coeFn requestedTime wave
      receipt.stateLimit] with
      time tangentSmulEq tangentRestrictionEq tangentRowEq
      subEq nonlinearEq viscousSmulEq stateRestrictionEq
  change
    (((Real.sqrt (integerWaveViscousMultiplier wave) : ℂ) •
        fixedWaveSpaceTimeRestriction requestedTime wave
          (NonlinearNegativeOneForcingReceipt.wholeNegativeOneTangent
            receipt)) time) =
      ((NonlinearNegativeOneForcingReceipt.fixedWaveNonlinearL2
          receipt wave -
        (((ν.coeff * integerWaveViscousMultiplier wave : ℝ) : ℂ) •
          fixedWaveSpaceTimeRestriction requestedTime wave
            receipt.stateLimit)) time)
  rw [tangentSmulEq, subEq]
  simp only [Pi.smul_apply, Pi.sub_apply]
  rw [tangentRestrictionEq, nonlinearEq,
    viscousSmulEq]
  simp only [Pi.smul_apply]
  rw [stateRestrictionEq]
  have tangentScalarEq :
      (Real.sqrt (integerWaveViscousMultiplier wave) : ℂ) •
          (NonlinearNegativeOneForcingReceipt.wholeNegativeOneTangent
            receipt time) wave =
        (Real.sqrt (integerWaveViscousMultiplier wave) : ℝ) •
          (NonlinearNegativeOneForcingReceipt.wholeNegativeOneTangent
            receipt time) wave := by
    ext coordinate
    simp [Complex.real_smul]
  have viscousScalarEq :
      ((ν.coeff * integerWaveViscousMultiplier wave : ℝ) : ℂ) •
          receipt.stateLimit time wave =
        (ν.coeff * integerWaveViscousMultiplier wave : ℝ) •
          receipt.stateLimit time wave := by
    ext coordinate
    simp [Complex.real_smul]
  rw [tangentScalarEq, viscousScalarEq, tangentRowEq]

/--
The existing weak Fourier equation is now consumed by the complete
whole-carrier tangent.  Both nonlinear and viscous terms occur through one
`L²_t H⁻¹_x` state rather than through unrelated row carriers.
-/
theorem NonlinearNegativeOneForcingReceipt.weak_action_via_wholeNegativeOneTangent
    {lineage : GeneratedIntegerShellInfiniteLineage}
    {ν : Viscosity}
    {θ requestedTime : ℝ}
    {θLtOne : θ < 1}
    {criticalMargin :
      ∀ length : ℕ,
        criticalEnstrophyLatticeConstant *
            finiteStateVorticityCoefficientEnstrophy
              (generatedSupport (lineage.current length))
              (generatedComplexVorticityState
                (lineage.current length)
                (generatedSupport (lineage.current length))) ≤
          θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2}
    {requestedTimePos : 0 < requestedTime}
    (receipt :
      NonlinearNegativeOneForcingReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (wave : IntegerWavevector)
    (waveNe : wave ≠ 0)
    (test testDerivative : ℝ → ℂ)
    (testHasDeriv :
      ∀ time ∈ Set.Icc (0 : ℝ) requestedTime,
        HasDerivAt test (testDerivative time) time)
    (testDerivativeContinuous :
      ContinuousOn testDerivative
        (Set.Icc (0 : ℝ) requestedTime))
    (testZero : test 0 = 0)
    (testRequestedTimeZero : test requestedTime = 0) :
    fixedL2ScalarL2IntegralCLM requestedTime
          (restrictedScalarL2 requestedTime testDerivative
            testDerivativeContinuous)
          (fixedWaveSpaceTimeRestriction
            requestedTime wave receipt.stateLimit) +
        fixedL2ScalarL2IntegralCLM requestedTime
          (restrictedScalarL2 requestedTime test
            (fun time timeMem =>
              (testHasDeriv time timeMem).continuousAt.continuousWithinAt))
          (NonlinearNegativeOneForcingReceipt.fixedWaveNegativeOneTangentL2
            receipt wave) =
      0 := by
  let testContinuous :
      ContinuousOn test (Set.Icc (0 : ℝ) requestedTime) :=
    fun time timeMem =>
      (testHasDeriv time timeMem).continuousAt.continuousWithinAt
  have nonlinearActionEq :
      fixedL2ScalarL2IntegralCLM requestedTime
          (restrictedScalarL2 requestedTime test testContinuous)
          (NonlinearNegativeOneForcingReceipt.fixedWaveNonlinearL2
            receipt wave) =
        fixedLInfScalarL1IntegralCLM requestedTime
          (restrictedScalarLInf requestedTime test testContinuous)
          (transverseSpaceTimeNonlinearRow
            receipt.transverseLimit wave) :=
    fixedL2Action_eq_fixedLInfAction_of_ae
      requestedTime test testContinuous
      (NonlinearNegativeOneForcingReceipt.fixedWaveNonlinearL2
        receipt wave)
      (transverseSpaceTimeNonlinearRow
        receipt.transverseLimit wave)
      (NonlinearNegativeOneForcingReceipt.fixedWaveNonlinearL2_coeFn
        receipt wave waveNe)
  have weakAction :=
    receipt.weak_action wave waveNe test testDerivative
      testHasDeriv testDerivativeContinuous
      testZero testRequestedTimeZero
  rw [
    NonlinearNegativeOneForcingReceipt.fixedWaveNegativeOneTangentL2_eq
      receipt wave waveNe,
    map_sub,
    nonlinearActionEq]
  unfold fixedWaveWeakAction at weakAction
  simpa only [testContinuous, sub_eq_add_neg, add_assoc] using weakAction

end

end ThreeDimensionalVorticityCoefficientWholeSpaceTimeViscousNegativeOne
end NavierStokes
end SaturationMonoid
