import H0mework.NavierStokes.WholeSpace.WholeSpaceTimeCriticalSerrin
import H0mework.NavierStokes.Fourier.TransverseSpaceTimeNonlinearRow

/-!
# Whole space-time nonlinear negative-one forcing

The pointwise whole-lattice nonlinear tangent is assembled here on the
actual space-time carrier.  For one transverse `L²` state, canonical finite
frequency projections converge almost everywhere to the inverse-Laplacian
weighted whole nonlinearity.  This proves strong measurability without
postulating a measurable nonlinear forcing.

If the same state has finite whole gradient mass and an almost-everywhere
coefficient-enstrophy ceiling, the weighted nonlinearity belongs to
`L²_t ℓ²_k`.  Its squared norm is bounded by the exact product of:

* the critical lattice constant;
* the coefficient-enstrophy ceiling; and
* the whole space-time gradient mass.

Thus the actual quadratic Fourier nonlinearity occupies the
`L²_t H⁻¹_x` forcing carrier used by weak and mild Navier--Stokes
formulations.  Measurability and negative-one membership are conclusions,
not certificate fields.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientWholeSpaceTimeNonlinearNegativeOne

open scoped BigOperators ENNReal Topology

open Filter
open MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalIntegerLatticeCriticalKernel
open ThreeDimensionalVorticityCoefficientFiniteSupportCriticalSobolev
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeSubsequence
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientInfiniteNonlinearNegativeSobolev
open ThreeDimensionalVorticityCoefficientTransverseSpaceTimeNonlinearRow
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeGradientLowerSemicontinuity
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeCriticalSerrin

noncomputable section

/-! ## Canonical finite approximations -/

theorem
    wholeStateVorticityNonlinearNegativeOneWeightedCoefficient_continuous
    (output : IntegerWavevector) :
    Continuous
      (fun state : WholeTransverseVorticityState =>
        wholeStateVorticityNonlinearNegativeOneWeightedCoefficient
          state.1 output) := by
  unfold wholeStateVorticityNonlinearNegativeOneWeightedCoefficient
  split_ifs
  · exact continuous_const
  · exact
      (wholeStateVorticityNonlinearCoefficientAt_continuous output).const_smul
        ((Real.sqrt (integerWaveViscousMultiplier output))⁻¹ : ℝ)

/-- The finite output-frequency projection of the actual whole nonlinear
negative-one state.  The input convolution is not truncated. -/
def wholeNonlinearNegativeOneFiniteApproximation
    (radius : ℕ)
    (state : WholeTransverseVorticityState) :
    ComplexVorticityHilbertState :=
  finiteComplexVorticityState
    (integerWaveFrequencyCube radius)
    (wholeStateVorticityNonlinearNegativeOneWeightedCoefficient state.1)

theorem wholeNonlinearNegativeOneFiniteApproximation_continuous
    (radius : ℕ) :
    Continuous
      (wholeNonlinearNegativeOneFiniteApproximation radius) := by
  unfold wholeNonlinearNegativeOneFiniteApproximation
    finiteComplexVorticityState
  apply continuous_finsetSum
  intro output outputMem
  exact
    (lp.singleContinuousLinearMap ℂ
      (fun _ : IntegerWavevector => ComplexCoordinateVector)
      2 output).continuous.comp
        (wholeStateVorticityNonlinearNegativeOneWeightedCoefficient_continuous
          output)

theorem wholeNonlinearNegativeOneFiniteApproximation_eq_projection
    (radius : ℕ)
    (state : WholeTransverseVorticityState)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (state.1 wave)) :
    wholeNonlinearNegativeOneFiniteApproximation radius state =
      complexSharpSupportProjection
        (integerWaveFrequencyCube radius)
        (wholeStateVorticityNonlinearNegativeOneState
          state.1 state.2 gradientSummable) := by
  ext output
  simp [wholeNonlinearNegativeOneFiniteApproximation,
    complexSharpSupportProjection_apply]

theorem wholeNonlinearNegativeOneFiniteApproximation_tendsto
    (state : WholeTransverseVorticityState)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (state.1 wave)) :
    Tendsto
      (fun radius =>
        wholeNonlinearNegativeOneFiniteApproximation radius state)
      atTop
      (𝓝
        (wholeStateVorticityNonlinearNegativeOneState
          state.1 state.2 gradientSummable)) := by
  simpa only [
    wholeNonlinearNegativeOneFiniteApproximation_eq_projection
      _ state gradientSummable] using
    complexSharpSupportProjection_frequencyCube_tendsto
      (wholeStateVorticityNonlinearNegativeOneState
        state.1 state.2 gradientSummable)

/-! ## Actual measurable forcing -/

/-- Pointwise whole nonlinear negative-one forcing.  At the null set where
the whole gradient density is not summable, it is canonically set to zero. -/
def wholeSpaceTimeNonlinearNegativeOneFunction
    {requestedTime : ℝ}
    (state : TransverseSpaceTimeState requestedTime)
    (time : Set.Icc (0 : ℝ) requestedTime) :
    ComplexVorticityHilbertState := by
  classical
  exact
    if gradientSummable :
        Summable fun wave : IntegerWavevector =>
          integerWaveNormSq wave *
            complexCoordinateAmplitudeSq ((state time).1 wave)
    then
      wholeStateVorticityNonlinearNegativeOneState
        (state time).1 (state time).2 gradientSummable
    else 0

theorem wholeSpaceTimeNonlinearNegativeOneFunction_of_summable
    {requestedTime : ℝ}
    (state : TransverseSpaceTimeState requestedTime)
    (time : Set.Icc (0 : ℝ) requestedTime)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq ((state time).1 wave)) :
    wholeSpaceTimeNonlinearNegativeOneFunction state time =
      wholeStateVorticityNonlinearNegativeOneState
        (state time).1 (state time).2 gradientSummable := by
  classical
  unfold wholeSpaceTimeNonlinearNegativeOneFunction
  rw [dif_pos gradientSummable]

theorem
    wholeSpaceTimeNonlinearNegativeOneFunction_aestronglyMeasurable
    {requestedTime : ℝ}
    (state : TransverseSpaceTimeState requestedTime)
    (pointwiseGradientSummable :
      ∀ᵐ time ∂(commonTimeMeasure requestedTime),
        Summable fun wave : IntegerWavevector =>
          integerWaveNormSq wave *
            complexCoordinateAmplitudeSq ((state time).1 wave)) :
    AEStronglyMeasurable
      (wholeSpaceTimeNonlinearNegativeOneFunction state)
      (commonTimeMeasure requestedTime) := by
  have finiteMeasurable :
      ∀ radius : ℕ,
        AEStronglyMeasurable
          (fun time =>
            wholeNonlinearNegativeOneFiniteApproximation
              radius (state time))
          (commonTimeMeasure requestedTime) := by
    intro radius
    exact
      (wholeNonlinearNegativeOneFiniteApproximation_continuous radius)
        |>.comp_aestronglyMeasurable
          (MeasureTheory.Lp.aestronglyMeasurable state)
  apply aestronglyMeasurable_of_tendsto_ae atTop finiteMeasurable
  filter_upwards [pointwiseGradientSummable] with
    time timeGradientSummable
  rw [wholeSpaceTimeNonlinearNegativeOneFunction_of_summable
    state time timeGradientSummable]
  exact
    wholeNonlinearNegativeOneFiniteApproximation_tendsto
      (state time) timeGradientSummable

theorem wholeSpaceTimeNonlinearNegativeOneFunction_norm_sq
    {requestedTime : ℝ}
    (state : TransverseSpaceTimeState requestedTime)
    (time : Set.Icc (0 : ℝ) requestedTime)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq ((state time).1 wave)) :
    ‖wholeSpaceTimeNonlinearNegativeOneFunction state time‖ ^ 2 =
      wholeStateVorticityNonlinearNegativeOneMass
        (state time).1 := by
  rw [wholeSpaceTimeNonlinearNegativeOneFunction_of_summable
    state time gradientSummable]
  exact
    wholeStateVorticityNonlinearNegativeOneState_norm_sq
      (state time).1 (state time).2 gradientSummable

/-! ## Time-`L²` negative-one forcing -/

theorem transversePointwiseGradient_ae_summable
    {requestedTime : ℝ}
    (state : TransverseSpaceTimeState requestedTime)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        wholeSpaceTimeVorticityGradientDensity requestedTime
          (transverseSpaceTimeInclusion requestedTime state) wave) :
    ∀ᵐ time ∂(commonTimeMeasure requestedTime),
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq ((state time).1 wave) := by
  have wholeGradientSummable :=
    wholePointwiseGradientDensity_ae_summable
      requestedTime
      (transverseSpaceTimeInclusion requestedTime state)
      gradientSummable
  filter_upwards [wholeGradientSummable,
    transverseSpaceTimeInclusion_coeFn requestedTime state] with
      time timeGradientSummable inclusionEq
  simpa only [inclusionEq] using timeGradientSummable

theorem wholeSpaceTimeNonlinearNegativeOneFunction_norm_sq_ae_le
    {requestedTime coefficientCeiling : ℝ}
    (state : TransverseSpaceTimeState requestedTime)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        wholeSpaceTimeVorticityGradientDensity requestedTime
          (transverseSpaceTimeInclusion requestedTime state) wave)
    (coefficientCeilingNonneg : 0 ≤ coefficientCeiling)
    (coefficientMassLe :
      ∀ᵐ time ∂(commonTimeMeasure requestedTime),
        wholeVorticityEuclideanMass ((state time).1) ≤
          coefficientCeiling) :
    ∀ᵐ time ∂(commonTimeMeasure requestedTime),
      ‖wholeSpaceTimeNonlinearNegativeOneFunction state time‖ ^ 2 ≤
        12 *
          (biotSavartSerrinConstant *
            (∑' wave : IntegerWavevector,
              integerWaveCriticalKernel wave)) *
          coefficientCeiling *
          (∑' wave : IntegerWavevector,
            wholePointwiseCarrierGradientDensity requestedTime
              (transverseSpaceTimeInclusion requestedTime state)
              time wave) := by
  let wholeState :=
    transverseSpaceTimeInclusion requestedTime state
  have pointwiseGradientSummable :=
    wholePointwiseGradientDensity_ae_summable
      requestedTime wholeState gradientSummable
  have carrierSummable :=
    wholePointwiseCarrierGradientDensity_ae_summable
      requestedTime wholeState gradientSummable
  have rowsAgree :
      ∀ᵐ time ∂(commonTimeMeasure requestedTime),
        ∀ wave : IntegerWavevector,
          fixedWaveSpaceTimeRestriction
              requestedTime wave wholeState time =
            wholeState time wave :=
    eventually_countable_forall.2 fun wave =>
      fixedWaveSpaceTimeRestriction_coeFn
        requestedTime wave wholeState
  filter_upwards [pointwiseGradientSummable,
    carrierSummable, rowsAgree,
    transverseSpaceTimeInclusion_coeFn requestedTime state,
    coefficientMassLe] with
      time timeGradientSummable timeCarrierSummable
      timeRowsAgree inclusionEq timeCoefficientMassLe
  have subtypeGradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq ((state time).1 wave) := by
    simpa only [wholeState, inclusionEq] using
      timeGradientSummable
  have staticBound :=
    wholeStateVorticityNonlinearNegativeOneState_norm_sq_le
      (state time).1 (state time).2 subtypeGradientSummable
  have gradientMassLe :
      wholeStateVorticityGradientMass ((state time).1) ≤
        3 *
          ∑' wave : IntegerWavevector,
            wholePointwiseCarrierGradientDensity
              requestedTime wholeState time wave := by
    have wholeGradientMassLe :=
      wholeStateGradientMass_le_three_mul_pointwiseCarrierMass
        requestedTime wholeState time timeRowsAgree
        timeCarrierSummable timeGradientSummable
    simpa only [wholeState, inclusionEq] using wholeGradientMassLe
  have criticalConstantNonneg :
      0 ≤
        biotSavartSerrinConstant *
          (∑' wave : IntegerWavevector,
            integerWaveCriticalKernel wave) :=
    mul_nonneg biotSavartSerrinConstant_nonneg
      integerWaveCriticalKernel_tsum_nonneg
  have gradientMassNonneg :
      0 ≤ wholeStateVorticityGradientMass ((state time).1) := by
    unfold wholeStateVorticityGradientMass
    exact tsum_nonneg fun wave =>
      mul_nonneg (integerWaveNormSq_nonneg wave)
        (complexCoordinateAmplitudeSq_nonneg _)
  rw [wholeSpaceTimeNonlinearNegativeOneFunction_norm_sq
    state time subtypeGradientSummable]
  calc
    wholeStateVorticityNonlinearNegativeOneMass ((state time).1) ≤
        4 *
          (biotSavartSerrinConstant *
            (∑' wave : IntegerWavevector,
              integerWaveCriticalKernel wave)) *
          wholeStateVorticityGradientMass ((state time).1) *
          wholeVorticityEuclideanMass ((state time).1) := by
      simpa only [
        wholeStateVorticityNonlinearNegativeOneState_norm_sq
          (state time).1 (state time).2 subtypeGradientSummable] using
        staticBound
    _ ≤
        4 *
          (biotSavartSerrinConstant *
            (∑' wave : IntegerWavevector,
              integerWaveCriticalKernel wave)) *
          wholeStateVorticityGradientMass ((state time).1) *
          coefficientCeiling :=
      mul_le_mul_of_nonneg_left timeCoefficientMassLe
        (mul_nonneg
          (mul_nonneg (by norm_num) criticalConstantNonneg)
          gradientMassNonneg)
    _ ≤
        4 *
          (biotSavartSerrinConstant *
            (∑' wave : IntegerWavevector,
              integerWaveCriticalKernel wave)) *
          (3 *
            ∑' wave : IntegerWavevector,
              wholePointwiseCarrierGradientDensity
                requestedTime wholeState time wave) *
          coefficientCeiling := by
      exact
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left gradientMassLe
            (mul_nonneg (by norm_num) criticalConstantNonneg))
          coefficientCeilingNonneg
    _ =
        12 *
          (biotSavartSerrinConstant *
            (∑' wave : IntegerWavevector,
              integerWaveCriticalKernel wave)) *
          coefficientCeiling *
          (∑' wave : IntegerWavevector,
            wholePointwiseCarrierGradientDensity requestedTime
              (transverseSpaceTimeInclusion requestedTime state)
              time wave) := by
      simp only [wholeState]
      ring

theorem wholeSpaceTimeNonlinearNegativeOneFunction_integrable_norm_sq
    {requestedTime coefficientCeiling : ℝ}
    (state : TransverseSpaceTimeState requestedTime)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        wholeSpaceTimeVorticityGradientDensity requestedTime
          (transverseSpaceTimeInclusion requestedTime state) wave)
    (coefficientCeilingNonneg : 0 ≤ coefficientCeiling)
    (coefficientMassLe :
      ∀ᵐ time ∂(commonTimeMeasure requestedTime),
        wholeVorticityEuclideanMass ((state time).1) ≤
          coefficientCeiling) :
    Integrable
      (fun time =>
        ‖wholeSpaceTimeNonlinearNegativeOneFunction state time‖ ^ 2)
      (commonTimeMeasure requestedTime) := by
  have pointwiseGradientSummable :=
    transversePointwiseGradient_ae_summable state gradientSummable
  have forcingAEMeasurable :=
    wholeSpaceTimeNonlinearNegativeOneFunction_aestronglyMeasurable
      state pointwiseGradientSummable
  have pointwiseBound :=
    wholeSpaceTimeNonlinearNegativeOneFunction_norm_sq_ae_le
      state gradientSummable coefficientCeilingNonneg coefficientMassLe
  have carrierMassIntegrable :=
    wholePointwiseCarrierGradientMass_integrable
      requestedTime
      (transverseSpaceTimeInclusion requestedTime state)
      gradientSummable
  apply
    (carrierMassIntegrable.const_mul
      (12 *
        (biotSavartSerrinConstant *
          (∑' wave : IntegerWavevector,
            integerWaveCriticalKernel wave)) *
        coefficientCeiling)).mono_nonneg
      (forcingAEMeasurable.norm.pow 2)
  · filter_upwards with time
    exact sq_nonneg _
  · exact pointwiseBound

theorem wholeSpaceTimeNonlinearNegativeOneFunction_memLp
    {requestedTime coefficientCeiling : ℝ}
    (state : TransverseSpaceTimeState requestedTime)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        wholeSpaceTimeVorticityGradientDensity requestedTime
          (transverseSpaceTimeInclusion requestedTime state) wave)
    (coefficientCeilingNonneg : 0 ≤ coefficientCeiling)
    (coefficientMassLe :
      ∀ᵐ time ∂(commonTimeMeasure requestedTime),
        wholeVorticityEuclideanMass ((state time).1) ≤
          coefficientCeiling) :
    MemLp
      (wholeSpaceTimeNonlinearNegativeOneFunction state)
      2 (commonTimeMeasure requestedTime) := by
  have pointwiseGradientSummable :=
    transversePointwiseGradient_ae_summable state gradientSummable
  have forcingAEMeasurable :=
    wholeSpaceTimeNonlinearNegativeOneFunction_aestronglyMeasurable
      state pointwiseGradientSummable
  exact
    (memLp_two_iff_integrable_sq_norm forcingAEMeasurable).2
      (wholeSpaceTimeNonlinearNegativeOneFunction_integrable_norm_sq
        state gradientSummable coefficientCeilingNonneg coefficientMassLe)

/-- The actual inverse-Laplacian weighted whole nonlinearity installed in
the time-`L²` forcing carrier. -/
def wholeSpaceTimeNonlinearNegativeOneState
    {requestedTime coefficientCeiling : ℝ}
    (state : TransverseSpaceTimeState requestedTime)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        wholeSpaceTimeVorticityGradientDensity requestedTime
          (transverseSpaceTimeInclusion requestedTime state) wave)
    (coefficientCeilingNonneg : 0 ≤ coefficientCeiling)
    (coefficientMassLe :
      ∀ᵐ time ∂(commonTimeMeasure requestedTime),
        wholeVorticityEuclideanMass ((state time).1) ≤
          coefficientCeiling) :
    SpaceTimeState requestedTime :=
  (wholeSpaceTimeNonlinearNegativeOneFunction_memLp
    state gradientSummable coefficientCeilingNonneg coefficientMassLe).toLp
      (wholeSpaceTimeNonlinearNegativeOneFunction state)

theorem wholeSpaceTimeNonlinearNegativeOneState_coeFn
    {requestedTime coefficientCeiling : ℝ}
    (state : TransverseSpaceTimeState requestedTime)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        wholeSpaceTimeVorticityGradientDensity requestedTime
          (transverseSpaceTimeInclusion requestedTime state) wave)
    (coefficientCeilingNonneg : 0 ≤ coefficientCeiling)
    (coefficientMassLe :
      ∀ᵐ time ∂(commonTimeMeasure requestedTime),
        wholeVorticityEuclideanMass ((state time).1) ≤
          coefficientCeiling) :
    wholeSpaceTimeNonlinearNegativeOneState
        state gradientSummable coefficientCeilingNonneg coefficientMassLe =ᵐ[
          commonTimeMeasure requestedTime]
      wholeSpaceTimeNonlinearNegativeOneFunction state := by
  exact
    (wholeSpaceTimeNonlinearNegativeOneFunction_memLp
      state gradientSummable coefficientCeilingNonneg
        coefficientMassLe).coeFn_toLp

theorem wholeSpaceTimeNonlinearNegativeOneFunction_integral_norm_sq_le
    {requestedTime coefficientCeiling : ℝ}
    (state : TransverseSpaceTimeState requestedTime)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        wholeSpaceTimeVorticityGradientDensity requestedTime
          (transverseSpaceTimeInclusion requestedTime state) wave)
    (coefficientCeilingNonneg : 0 ≤ coefficientCeiling)
    (coefficientMassLe :
      ∀ᵐ time ∂(commonTimeMeasure requestedTime),
        wholeVorticityEuclideanMass ((state time).1) ≤
          coefficientCeiling) :
    (∫ time,
        ‖wholeSpaceTimeNonlinearNegativeOneFunction state time‖ ^ 2
        ∂(commonTimeMeasure requestedTime)) ≤
      12 *
        (biotSavartSerrinConstant *
          (∑' wave : IntegerWavevector,
            integerWaveCriticalKernel wave)) *
        coefficientCeiling *
        wholeSpaceTimeVorticityGradientMass requestedTime
          (transverseSpaceTimeInclusion requestedTime state) := by
  calc
    (∫ time,
        ‖wholeSpaceTimeNonlinearNegativeOneFunction state time‖ ^ 2
        ∂(commonTimeMeasure requestedTime)) ≤
        ∫ time,
          12 *
            (biotSavartSerrinConstant *
              (∑' wave : IntegerWavevector,
                integerWaveCriticalKernel wave)) *
            coefficientCeiling *
            (∑' wave : IntegerWavevector,
              wholePointwiseCarrierGradientDensity requestedTime
                (transverseSpaceTimeInclusion requestedTime state)
                time wave)
          ∂(commonTimeMeasure requestedTime) := by
      exact integral_mono_ae
        (wholeSpaceTimeNonlinearNegativeOneFunction_integrable_norm_sq
          state gradientSummable coefficientCeilingNonneg coefficientMassLe)
        ((wholePointwiseCarrierGradientMass_integrable
          requestedTime
          (transverseSpaceTimeInclusion requestedTime state)
          gradientSummable).const_mul
            (12 *
              (biotSavartSerrinConstant *
                (∑' wave : IntegerWavevector,
                  integerWaveCriticalKernel wave)) *
              coefficientCeiling))
        (wholeSpaceTimeNonlinearNegativeOneFunction_norm_sq_ae_le
          state gradientSummable coefficientCeilingNonneg coefficientMassLe)
    _ =
        12 *
          (biotSavartSerrinConstant *
            (∑' wave : IntegerWavevector,
              integerWaveCriticalKernel wave)) *
          coefficientCeiling *
          wholeSpaceTimeVorticityGradientMass requestedTime
            (transverseSpaceTimeInclusion requestedTime state) := by
      rw [integral_const_mul]
      rw [wholePointwiseCarrierGradientMass_integral
        requestedTime
        (transverseSpaceTimeInclusion requestedTime state)
        gradientSummable]

theorem wholeSpaceTimeNonlinearNegativeOneState_norm_sq_le
    {requestedTime coefficientCeiling : ℝ}
    (state : TransverseSpaceTimeState requestedTime)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        wholeSpaceTimeVorticityGradientDensity requestedTime
          (transverseSpaceTimeInclusion requestedTime state) wave)
    (coefficientCeilingNonneg : 0 ≤ coefficientCeiling)
    (coefficientMassLe :
      ∀ᵐ time ∂(commonTimeMeasure requestedTime),
        wholeVorticityEuclideanMass ((state time).1) ≤
          coefficientCeiling) :
    ‖wholeSpaceTimeNonlinearNegativeOneState
        state gradientSummable coefficientCeilingNonneg coefficientMassLe‖ ^ 2 ≤
      12 *
        (biotSavartSerrinConstant *
          (∑' wave : IntegerWavevector,
            integerWaveCriticalKernel wave)) *
        coefficientCeiling *
        wholeSpaceTimeVorticityGradientMass requestedTime
          (transverseSpaceTimeInclusion requestedTime state) := by
  rw [spaceTime_norm_sq_eq_integral]
  calc
    (∫ time,
        ‖wholeSpaceTimeNonlinearNegativeOneState
          state gradientSummable coefficientCeilingNonneg
            coefficientMassLe time‖ ^ 2
        ∂(commonTimeMeasure requestedTime)) =
        ∫ time,
          ‖wholeSpaceTimeNonlinearNegativeOneFunction state time‖ ^ 2
          ∂(commonTimeMeasure requestedTime) := by
      apply integral_congr_ae
      filter_upwards [
        wholeSpaceTimeNonlinearNegativeOneState_coeFn
          state gradientSummable coefficientCeilingNonneg
            coefficientMassLe] with time forcingEq
      rw [forcingEq]
    _ ≤ _ :=
      wholeSpaceTimeNonlinearNegativeOneFunction_integral_norm_sq_le
        state gradientSummable coefficientCeilingNonneg coefficientMassLe

/-! ## Recovery of the actual quadratic row -/

theorem
    sqrt_viscousMultiplier_smul_wholeStateVorticityNonlinearNegativeOneWeightedCoefficient
    (state : ComplexVorticityHilbertState)
    (output : IntegerWavevector)
    (outputNe : output ≠ 0) :
    (Real.sqrt (integerWaveViscousMultiplier output) : ℝ) •
        wholeStateVorticityNonlinearNegativeOneWeightedCoefficient
          state output =
      wholeStateVorticityNonlinearCoefficientAt state output := by
  have multiplierPos :
      0 < integerWaveViscousMultiplier output := by
    unfold integerWaveViscousMultiplier
    exact
      mul_pos
        (sq_pos_of_pos (mul_pos (by norm_num) Real.pi_pos))
        (integerWaveNormSq_pos outputNe)
  simp [wholeStateVorticityNonlinearNegativeOneWeightedCoefficient,
    outputNe, Real.sqrt_ne_zero'.2 multiplierPos]

/--
Every nonzero Fourier row of the time-`L²` negative-one state recovers the
actual quadratic nonlinear row after applying the square-root Laplacian.
-/
theorem wholeSpaceTimeNonlinearNegativeOneState_unweighted_row_ae
    {requestedTime coefficientCeiling : ℝ}
    (state : TransverseSpaceTimeState requestedTime)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        wholeSpaceTimeVorticityGradientDensity requestedTime
          (transverseSpaceTimeInclusion requestedTime state) wave)
    (coefficientCeilingNonneg : 0 ≤ coefficientCeiling)
    (coefficientMassLe :
      ∀ᵐ time ∂(commonTimeMeasure requestedTime),
        wholeVorticityEuclideanMass ((state time).1) ≤
          coefficientCeiling)
    (output : IntegerWavevector)
    (outputNe : output ≠ 0) :
    ∀ᵐ time ∂(commonTimeMeasure requestedTime),
      (Real.sqrt (integerWaveViscousMultiplier output) : ℝ) •
          (wholeSpaceTimeNonlinearNegativeOneState
            state gradientSummable coefficientCeilingNonneg
              coefficientMassLe time) output =
        transverseSpaceTimeNonlinearRow state output time := by
  have pointwiseGradientSummable :=
    transversePointwiseGradient_ae_summable state gradientSummable
  filter_upwards [
    wholeSpaceTimeNonlinearNegativeOneState_coeFn
      state gradientSummable coefficientCeilingNonneg coefficientMassLe,
    pointwiseGradientSummable,
    transverseSpaceTimeNonlinearRow_coeFn state output] with
      time forcingEq timeGradientSummable nonlinearRowEq
  rw [forcingEq,
    wholeSpaceTimeNonlinearNegativeOneFunction_of_summable
      state time timeGradientSummable,
    nonlinearRowEq]
  change
    (Real.sqrt (integerWaveViscousMultiplier output) : ℝ) •
        wholeStateVorticityNonlinearNegativeOneWeightedCoefficient
          (state time).1 output =
      wholeStateVorticityNonlinearCoefficientAt (state time).1 output
  exact
    sqrt_viscousMultiplier_smul_wholeStateVorticityNonlinearNegativeOneWeightedCoefficient
      (state time).1 output outputNe

end

end ThreeDimensionalVorticityCoefficientWholeSpaceTimeNonlinearNegativeOne
end NavierStokes
end SaturationMonoid
