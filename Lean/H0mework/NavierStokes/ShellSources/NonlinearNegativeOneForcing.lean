import H0mework.NavierStokes.ShellSources.PointwiseMassLimit
import H0mework.NavierStokes.WholeSpace.WholeSpaceTimeNonlinearNegativeOne

/-!
# Source-generated whole nonlinear negative-one forcing

The source-generated critical weak limit now produces its actual quadratic
nonlinearity in the complete `L²_t H⁻¹_x` Fourier carrier.

The construction uses the same transverse state, the same weak-limit
subsequence, the generated pointwise coefficient-enstrophy ceiling, and the
whole gradient lower-semicontinuity budget.  It yields the explicit bound

`‖N(ω)‖²_{L²_t H⁻¹_x} ≤
  6 K_crit C_crit² / A_θ`.

No nonlinear-forcing witness, negative Sobolev membership, cutoff,
terminal shell, continuation target, or strong solution is assumed.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientGeneratedIntegerShellNonlinearNegativeOneForcing

open scoped BigOperators ENNReal Topology

open Filter
open MeasureTheory
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
open ThreeDimensionalVorticityCoefficientGeneratedPathFiniteObservedCompactness
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageReceiptSquare
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageReceiptSquare.GeneratedIntegerShellInfiniteLineage
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellClosedNonlinearWeakLimit
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellCriticalSerrinWeakLimit
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellPointwiseMassLimit
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeGradientLowerSemicontinuity
open ThreeDimensionalVorticityCoefficientTransverseSpaceTimeNonlinearRow
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeNonlinearNegativeOne

noncomputable section

theorem CriticalSerrinWeakLimitReceipt.transverseGradient_summable
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
      CriticalSerrinWeakLimitReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos) :
    Summable fun wave : IntegerWavevector =>
      wholeSpaceTimeVorticityGradientDensity requestedTime
        (transverseSpaceTimeInclusion requestedTime
          receipt.transverseLimit) wave := by
  simpa only [receipt.inclusion_eq] using receipt.gradient_summable

theorem
    CriticalSerrinWeakLimitReceipt.transverseWholeVorticityEuclideanMass_ae_le_generated
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
      CriticalSerrinWeakLimitReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos) :
    ∀ᵐ time ∂(commonTimeMeasure requestedTime),
      wholeVorticityEuclideanMass
          ((receipt.transverseLimit time).1) ≤
        criticalCoefficientEnstrophyCeiling ν θ := by
  have wholeMassLe :
      ∀ᵐ time ∂(commonTimeMeasure requestedTime),
        wholeVorticityEuclideanMass
            ((transverseSpaceTimeInclusion requestedTime
              receipt.transverseLimit) time) ≤
          criticalCoefficientEnstrophyCeiling ν θ := by
    simpa only [receipt.inclusion_eq] using
      ThreeDimensionalVorticityCoefficientGeneratedIntegerShellPointwiseMassLimit.CriticalSerrinWeakLimitReceipt.stateLimit_wholeVorticityEuclideanMass_ae_le_ceiling
        receipt
  filter_upwards [wholeMassLe,
    transverseSpaceTimeInclusion_coeFn requestedTime
      receipt.transverseLimit] with time timeMassLe inclusionEq
  simpa only [inclusionEq] using timeMassLe

/-- Actual whole nonlinear forcing generated by one source-produced critical
weak limit, weighted by the inverse square root of the Laplacian. -/
def CriticalSerrinWeakLimitReceipt.wholeNonlinearNegativeOneForcing
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
      CriticalSerrinWeakLimitReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos) :
    SpaceTimeState requestedTime :=
  wholeSpaceTimeNonlinearNegativeOneState
    receipt.transverseLimit
    (CriticalSerrinWeakLimitReceipt.transverseGradient_summable receipt)
    (criticalCoefficientEnstrophyCeiling_nonneg ν θ)
    (CriticalSerrinWeakLimitReceipt.transverseWholeVorticityEuclideanMass_ae_le_generated
      receipt)

theorem
    CriticalSerrinWeakLimitReceipt.wholeNonlinearNegativeOneForcing_coeFn
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
      CriticalSerrinWeakLimitReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos) :
    CriticalSerrinWeakLimitReceipt.wholeNonlinearNegativeOneForcing
        receipt =ᵐ[
        commonTimeMeasure requestedTime]
      wholeSpaceTimeNonlinearNegativeOneFunction
        receipt.transverseLimit := by
  exact
    wholeSpaceTimeNonlinearNegativeOneState_coeFn
      receipt.transverseLimit
      (CriticalSerrinWeakLimitReceipt.transverseGradient_summable receipt)
      (criticalCoefficientEnstrophyCeiling_nonneg ν θ)
      (CriticalSerrinWeakLimitReceipt.transverseWholeVorticityEuclideanMass_ae_le_generated
        receipt)

theorem
    CriticalSerrinWeakLimitReceipt.wholeNonlinearNegativeOneForcing_norm_sq_le_gradient
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
      CriticalSerrinWeakLimitReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos) :
    ‖CriticalSerrinWeakLimitReceipt.wholeNonlinearNegativeOneForcing
        receipt‖ ^ 2 ≤
      12 *
        (biotSavartSerrinConstant *
          (∑' wave : IntegerWavevector,
            integerWaveCriticalKernel wave)) *
        criticalCoefficientEnstrophyCeiling ν θ *
        wholeSpaceTimeVorticityGradientMass requestedTime
          receipt.stateLimit := by
  have baseBound :=
    wholeSpaceTimeNonlinearNegativeOneState_norm_sq_le
      receipt.transverseLimit
      (CriticalSerrinWeakLimitReceipt.transverseGradient_summable receipt)
      (criticalCoefficientEnstrophyCeiling_nonneg ν θ)
      (CriticalSerrinWeakLimitReceipt.transverseWholeVorticityEuclideanMass_ae_le_generated
        receipt)
  unfold CriticalSerrinWeakLimitReceipt.wholeNonlinearNegativeOneForcing
  rw [receipt.inclusion_eq] at baseBound
  calc
    _ ≤
        12 *
          (biotSavartSerrinConstant *
            (∑' wave : IntegerWavevector,
              integerWaveCriticalKernel wave)) *
          criticalCoefficientEnstrophyCeiling ν θ *
          wholeSpaceTimeVorticityGradientMass requestedTime
            receipt.stateLimit :=
      baseBound

theorem
    CriticalSerrinWeakLimitReceipt.wholeNonlinearNegativeOneForcing_norm_sq_le_generated
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
      CriticalSerrinWeakLimitReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos) :
    ‖CriticalSerrinWeakLimitReceipt.wholeNonlinearNegativeOneForcing
        receipt‖ ^ 2 ≤
      6 *
        (biotSavartSerrinConstant *
          (∑' wave : IntegerWavevector,
            integerWaveCriticalKernel wave)) *
        criticalCoefficientEnstrophyCeiling ν θ ^ 2 /
        criticalEnstrophyAbsorptionCoefficient θ ν := by
  have criticalConstantNonneg :
      0 ≤
        12 *
          (biotSavartSerrinConstant *
            (∑' wave : IntegerWavevector,
              integerWaveCriticalKernel wave)) *
          criticalCoefficientEnstrophyCeiling ν θ :=
    mul_nonneg
      (mul_nonneg (by norm_num)
        (mul_nonneg biotSavartSerrinConstant_nonneg
          integerWaveCriticalKernel_tsum_nonneg))
      (criticalCoefficientEnstrophyCeiling_nonneg ν θ)
  calc
    ‖CriticalSerrinWeakLimitReceipt.wholeNonlinearNegativeOneForcing
        receipt‖ ^ 2 ≤
        12 *
          (biotSavartSerrinConstant *
            (∑' wave : IntegerWavevector,
              integerWaveCriticalKernel wave)) *
          criticalCoefficientEnstrophyCeiling ν θ *
          wholeSpaceTimeVorticityGradientMass requestedTime
            receipt.stateLimit :=
      CriticalSerrinWeakLimitReceipt.wholeNonlinearNegativeOneForcing_norm_sq_le_gradient
        receipt
    _ ≤
        12 *
          (biotSavartSerrinConstant *
            (∑' wave : IntegerWavevector,
              integerWaveCriticalKernel wave)) *
          criticalCoefficientEnstrophyCeiling ν θ *
          (((1 / 2 : ℝ) *
              criticalCoefficientEnstrophyCeiling ν θ) /
            criticalEnstrophyAbsorptionCoefficient θ ν) :=
      mul_le_mul_of_nonneg_left receipt.gradient_mass_le
        criticalConstantNonneg
    _ =
        6 *
          (biotSavartSerrinConstant *
            (∑' wave : IntegerWavevector,
              integerWaveCriticalKernel wave)) *
          criticalCoefficientEnstrophyCeiling ν θ ^ 2 /
          criticalEnstrophyAbsorptionCoefficient θ ν := by
      ring

theorem
    CriticalSerrinWeakLimitReceipt.wholeNonlinearNegativeOneForcing_unweighted_row_ae
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
      CriticalSerrinWeakLimitReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (output : IntegerWavevector)
    (outputNe : output ≠ 0) :
    ∀ᵐ time ∂(commonTimeMeasure requestedTime),
      (Real.sqrt (integerWaveViscousMultiplier output) : ℝ) •
          (CriticalSerrinWeakLimitReceipt.wholeNonlinearNegativeOneForcing
            receipt time) output =
        transverseSpaceTimeNonlinearRow
          receipt.transverseLimit output time := by
  simpa only [
    CriticalSerrinWeakLimitReceipt.wholeNonlinearNegativeOneForcing] using
    wholeSpaceTimeNonlinearNegativeOneState_unweighted_row_ae
      receipt.transverseLimit
      (CriticalSerrinWeakLimitReceipt.transverseGradient_summable receipt)
      (criticalCoefficientEnstrophyCeiling_nonneg ν θ)
      (CriticalSerrinWeakLimitReceipt.transverseWholeVorticityEuclideanMass_ae_le_generated
        receipt)
      output outputNe

/-! ## Source-owned forcing receipt -/

/--
One source-generated critical weak solution together with its actual
whole-lattice `L²_t H⁻¹_x` quadratic forcing.
-/
structure NonlinearNegativeOneForcingReceipt
    (lineage : GeneratedIntegerShellInfiniteLineage)
    (ν : Viscosity)
    (θ requestedTime : ℝ)
    (θLtOne : θ < 1)
    (criticalMargin :
      ∀ length : ℕ,
        criticalEnstrophyLatticeConstant *
            finiteStateVorticityCoefficientEnstrophy
              (generatedSupport (lineage.current length))
              (generatedComplexVorticityState
                (lineage.current length)
                (generatedSupport (lineage.current length))) ≤
          θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2)
    (requestedTimePos : 0 < requestedTime)
    extends
      CriticalSerrinWeakLimitReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos where
  negativeOneForcing : SpaceTimeState requestedTime
  negativeOneForcing_coeFn :
    negativeOneForcing =ᵐ[commonTimeMeasure requestedTime]
      wholeSpaceTimeNonlinearNegativeOneFunction transverseLimit
  negativeOneForcing_unweighted_row_ae :
    ∀ output : IntegerWavevector,
      output ≠ 0 →
        ∀ᵐ time ∂(commonTimeMeasure requestedTime),
          (Real.sqrt (integerWaveViscousMultiplier output) : ℝ) •
              (negativeOneForcing time) output =
            transverseSpaceTimeNonlinearRow transverseLimit output time
  negativeOneForcing_norm_sq_le_generated :
    ‖negativeOneForcing‖ ^ 2 ≤
      6 *
        (biotSavartSerrinConstant *
          (∑' wave : IntegerWavevector,
            integerWaveCriticalKernel wave)) *
        criticalCoefficientEnstrophyCeiling ν θ ^ 2 /
        criticalEnstrophyAbsorptionCoefficient θ ν

/--
Every strict-critical source-generated infinite lineage produces its
actual whole nonlinear forcing in `L²_t H⁻¹_x`, with a cutoff-independent
quantitative bound and exact recovery of every nonzero Fourier row.
-/
noncomputable def
    GeneratedIntegerShellInfiniteLineage.generates_nonlinearNegativeOneForcing
    (lineage : GeneratedIntegerShellInfiniteLineage)
    (ν : Viscosity)
    (θ requestedTime : ℝ)
    (θLtOne : θ < 1)
    (criticalMargin :
      ∀ length : ℕ,
        criticalEnstrophyLatticeConstant *
            finiteStateVorticityCoefficientEnstrophy
              (generatedSupport (lineage.current length))
              (generatedComplexVorticityState
                (lineage.current length)
                (generatedSupport (lineage.current length))) ≤
          θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2)
    (requestedTimePos : 0 < requestedTime) :
    NonlinearNegativeOneForcingReceipt
      lineage ν θ requestedTime θLtOne criticalMargin
      requestedTimePos := by
  let criticalReceipt :=
    ThreeDimensionalVorticityCoefficientGeneratedIntegerShellCriticalSerrinWeakLimit.GeneratedIntegerShellInfiniteLineage.generates_criticalSerrinWeakLimit
      lineage ν θ requestedTime θLtOne criticalMargin
      requestedTimePos
  let forcing :=
    CriticalSerrinWeakLimitReceipt.wholeNonlinearNegativeOneForcing
      criticalReceipt
  exact
    { toCriticalSerrinWeakLimitReceipt := criticalReceipt
      negativeOneForcing := forcing
      negativeOneForcing_coeFn := by
        exact
          CriticalSerrinWeakLimitReceipt.wholeNonlinearNegativeOneForcing_coeFn
            criticalReceipt
      negativeOneForcing_unweighted_row_ae := by
        intro output outputNe
        exact
          CriticalSerrinWeakLimitReceipt.wholeNonlinearNegativeOneForcing_unweighted_row_ae
            criticalReceipt output outputNe
      negativeOneForcing_norm_sq_le_generated := by
        exact
          CriticalSerrinWeakLimitReceipt.wholeNonlinearNegativeOneForcing_norm_sq_le_generated
            criticalReceipt }

end

end ThreeDimensionalVorticityCoefficientGeneratedIntegerShellNonlinearNegativeOneForcing
end NavierStokes
end SaturationMonoid
