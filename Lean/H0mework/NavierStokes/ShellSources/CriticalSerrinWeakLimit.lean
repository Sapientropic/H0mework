import H0mework.NavierStokes.ShellSources.ClosedNonlinearWeakLimit
import H0mework.NavierStokes.WholeSpace.WholeSpaceTimeCriticalSerrin

/-!
# Source-generated critical Serrin weak limit

The closed nonlinear weak-limit receipt is consumed by the whole-lattice
Tonelli/Serrin estimate.  The same source-generated state and subsequence
therefore carry:

* the actual nonlinear Fourier row of the same transverse state;
* finite whole space-time vorticity-gradient mass; and
* an explicit time-`L²` bound for the full Fourier velocity majorant.

No velocity-majorant integrability, continuation witness, target strong
solution, cutoff, or terminal shell is assumed.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientGeneratedIntegerShellCriticalSerrinWeakLimit

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
open ThreeDimensionalVorticityCoefficientInfiniteFixedWaveWeakCarrier
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageReceiptSquare
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageReceiptSquare.GeneratedIntegerShellInfiniteLineage
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellClosedNonlinearWeakLimit
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeGradientLowerSemicontinuity
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeCriticalSerrin

noncomputable section

/-- One source-generated closed nonlinear weak solution together with its
cutoff-free critical Serrin budget. -/
structure CriticalSerrinWeakLimitReceipt
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
      ClosedNonlinearWeakLimitReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos where
  pointwiseGradient_ae_summable :
    ∀ᵐ time ∂(commonTimeMeasure requestedTime),
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq
            (stateLimit time wave)
  velocityMajorantSq_integrable :
    Integrable
      (fun time =>
        wholeStateVelocityMajorant
          (stateLimit time) ^ 2)
      (commonTimeMeasure requestedTime)
  velocityMajorantSq_integral_le_gradientMass :
    (∫ time,
        wholeStateVelocityMajorant
          (stateLimit time) ^ 2
        ∂(commonTimeMeasure requestedTime)) ≤
      3 *
        (biotSavartSerrinConstant *
          (∑' wave : IntegerWavevector,
            integerWaveCriticalKernel wave)) *
        wholeSpaceTimeVorticityGradientMass
          requestedTime stateLimit
  velocityMajorantSq_integral_le_generated :
    (∫ time,
        wholeStateVelocityMajorant
          (stateLimit time) ^ 2
        ∂(commonTimeMeasure requestedTime)) ≤
      3 *
        (biotSavartSerrinConstant *
          (∑' wave : IntegerWavevector,
            integerWaveCriticalKernel wave)) *
        (((1 / 2 : ℝ) *
            criticalCoefficientEnstrophyCeiling ν θ) /
          criticalEnstrophyAbsorptionCoefficient θ ν)

/--
An arbitrary strict-critical infinite lineage generates one common weak
Fourier state with its actual nonlinearity and an explicit critical Serrin
budget.
-/
noncomputable def
    GeneratedIntegerShellInfiniteLineage.generates_criticalSerrinWeakLimit
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
    CriticalSerrinWeakLimitReceipt
      lineage ν θ requestedTime θLtOne criticalMargin
      requestedTimePos := by
  let weakLimit :=
    ThreeDimensionalVorticityCoefficientGeneratedIntegerShellClosedNonlinearWeakLimit.GeneratedIntegerShellInfiniteLineage.generates_closedNonlinearWeakLimit
      lineage ν θ requestedTime θLtOne criticalMargin
      requestedTimePos
  have pointwiseGradientSummable :
      ∀ᵐ time ∂(commonTimeMeasure requestedTime),
        Summable fun wave : IntegerWavevector =>
          integerWaveNormSq wave *
            complexCoordinateAmplitudeSq
              (weakLimit.stateLimit time wave) :=
    wholePointwiseGradientDensity_ae_summable
      requestedTime weakLimit.stateLimit
      weakLimit.gradient_summable
  have serrinIntegrable :
      Integrable
        (fun time =>
          wholeStateVelocityMajorant
            (weakLimit.stateLimit time) ^ 2)
        (commonTimeMeasure requestedTime) :=
    wholeVelocityMajorantSq_integrable
      requestedTime weakLimit.stateLimit
      weakLimit.gradient_summable
  have serrinLeGradient :
      (∫ time,
          wholeStateVelocityMajorant
            (weakLimit.stateLimit time) ^ 2
          ∂(commonTimeMeasure requestedTime)) ≤
        3 *
          (biotSavartSerrinConstant *
            (∑' wave : IntegerWavevector,
              integerWaveCriticalKernel wave)) *
          wholeSpaceTimeVorticityGradientMass
            requestedTime weakLimit.stateLimit :=
    wholeVelocityMajorantSq_integral_le
      requestedTime weakLimit.stateLimit
      weakLimit.gradient_summable
  have criticalConstantNonneg :
      0 ≤
        3 *
          (biotSavartSerrinConstant *
            (∑' wave : IntegerWavevector,
              integerWaveCriticalKernel wave)) := by
    exact mul_nonneg (by norm_num)
      (mul_nonneg biotSavartSerrinConstant_nonneg
        integerWaveCriticalKernel_tsum_nonneg)
  have serrinLeGenerated :
      (∫ time,
          wholeStateVelocityMajorant
            (weakLimit.stateLimit time) ^ 2
          ∂(commonTimeMeasure requestedTime)) ≤
        3 *
          (biotSavartSerrinConstant *
            (∑' wave : IntegerWavevector,
              integerWaveCriticalKernel wave)) *
          (((1 / 2 : ℝ) *
              criticalCoefficientEnstrophyCeiling ν θ) /
            criticalEnstrophyAbsorptionCoefficient θ ν) :=
    serrinLeGradient.trans <|
      mul_le_mul_of_nonneg_left
        weakLimit.gradient_mass_le criticalConstantNonneg
  exact
    { toClosedNonlinearWeakLimitReceipt := weakLimit
      pointwiseGradient_ae_summable :=
        pointwiseGradientSummable
      velocityMajorantSq_integrable := serrinIntegrable
      velocityMajorantSq_integral_le_gradientMass :=
        serrinLeGradient
      velocityMajorantSq_integral_le_generated :=
        serrinLeGenerated }

end

end ThreeDimensionalVorticityCoefficientGeneratedIntegerShellCriticalSerrinWeakLimit
end NavierStokes
end SaturationMonoid
