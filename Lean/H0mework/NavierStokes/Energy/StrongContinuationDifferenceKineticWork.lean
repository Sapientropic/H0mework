import H0mework.NavierStokes.Energy.StrongContinuationDifferenceKineticEnergy

/-!
# Nonlinear and viscous work on the kinetic difference carrier

The actual kinetic-scale work of two strong continuations is split before
any estimate is taken.  At every nonzero frequency, the genuine difference
tangent contributes

```text
2 <difference, nonlinear_left - nonlinear_right> / multiplier
  - 2 * viscosity * |difference|².
```

Thus the Laplacian weight cancels exactly in the viscous term, while the
nonlinear term remains on the same Biot--Savart/kinetic carrier required by
the incompressible cancellation argument.

No bound, smallness hypothesis, cancellation certificate, finite cutoff, or
path equality is supplied by a caller.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticWork

open scoped BigOperators

open Set
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellSource
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageReceiptSquare
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageReceiptSquare.GeneratedIntegerShellInfiniteLineage
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellWholeContinuousMild
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuation
open ThreeDimensionalVorticityCoefficientWholeTangentEnergyTransport
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceEnergy
open ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy

noncomputable section

section SameHorizon

variable
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

/-- Genuine nonlinear kinetic power at one actual nonzero Fourier row. -/
def actualWaveDifferenceNonlinearKineticPower
    (left right :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (wave : NonzeroIntegerWavevector)
    (time : ℝ) : ℝ :=
  2 *
      complexCoordinateRealInner
        (actualWaveDifferencePath left right wave time)
        (WholeContinuousMildReceipt.actualWaveNonlinearExtension
            left.toWholeContinuousMildReceipt wave.1 time -
          WholeContinuousMildReceipt.actualWaveNonlinearExtension
            right.toWholeContinuousMildReceipt wave.1 time) /
    integerWaveViscousMultiplier wave.1

/-- Exact unweighted viscous power left after kinetic reweighting. -/
def actualWaveDifferenceViscousKineticPower
    (left right :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (wave : NonzeroIntegerWavevector)
    (time : ℝ) : ℝ :=
  2 * ν.coeff *
    complexCoordinateAmplitudeSq
      (actualWaveDifferencePath left right wave time)

/--
The complete row tangent splits pointwise into nonlinear kinetic power and
the exactly cancelled Laplacian/viscosity power.
-/
theorem actualWaveDifference_kineticPower_split
    (left right :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (wave : NonzeroIntegerWavevector)
    (time : ℝ) :
    (2 *
        complexCoordinateRealInner
          (actualWaveDifferencePath left right wave time)
          (actualWaveDifferenceTangent left right wave time)) /
        integerWaveViscousMultiplier wave.1 =
      actualWaveDifferenceNonlinearKineticPower
          left right wave time -
        actualWaveDifferenceViscousKineticPower
          left right wave time := by
  have multiplierNe :
      integerWaveViscousMultiplier wave.1 ≠ 0 :=
    ne_of_gt (integerWaveViscousMultiplier_pos wave)
  unfold actualWaveDifferenceTangent
  change
    (2 *
        complexCoordinateRealInner
          (actualWaveDifferencePath left right wave time)
          (((WholeContinuousMildReceipt.actualWaveNonlinearExtension
                left.toWholeContinuousMildReceipt wave.1 time -
              (ν.coeff * integerWaveViscousMultiplier wave.1) •
                WholeContinuousMildReceipt.actualWaveHeatDuhamelPath
                  left.toWholeContinuousMildReceipt wave.1 time) -
            (WholeContinuousMildReceipt.actualWaveNonlinearExtension
                right.toWholeContinuousMildReceipt wave.1 time -
              (ν.coeff * integerWaveViscousMultiplier wave.1) •
                WholeContinuousMildReceipt.actualWaveHeatDuhamelPath
                  right.toWholeContinuousMildReceipt wave.1 time)))) /
        integerWaveViscousMultiplier wave.1 =
      _
  rw [show
      ((WholeContinuousMildReceipt.actualWaveNonlinearExtension
              left.toWholeContinuousMildReceipt wave.1 time -
            (ν.coeff * integerWaveViscousMultiplier wave.1) •
              WholeContinuousMildReceipt.actualWaveHeatDuhamelPath
                left.toWholeContinuousMildReceipt wave.1 time) -
          (WholeContinuousMildReceipt.actualWaveNonlinearExtension
              right.toWholeContinuousMildReceipt wave.1 time -
            (ν.coeff * integerWaveViscousMultiplier wave.1) •
              WholeContinuousMildReceipt.actualWaveHeatDuhamelPath
                right.toWholeContinuousMildReceipt wave.1 time)) =
        (WholeContinuousMildReceipt.actualWaveNonlinearExtension
              left.toWholeContinuousMildReceipt wave.1 time -
            WholeContinuousMildReceipt.actualWaveNonlinearExtension
              right.toWholeContinuousMildReceipt wave.1 time) -
          (ν.coeff * integerWaveViscousMultiplier wave.1) •
            actualWaveDifferencePath left right wave time by
      unfold actualWaveDifferencePath
      rw [smul_sub]
      abel]
  rw [complexCoordinateRealInner_sub_right,
    complexCoordinateRealInner_real_smul_right,
    complexCoordinateRealInner_self,
    ← complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
  unfold actualWaveDifferenceNonlinearKineticPower
    actualWaveDifferenceViscousKineticPower
  field_simp [multiplierNe]

/--
One row's exact kinetic work is the interval integral of nonlinear power
minus the unweighted viscous power.
-/
theorem actualWaveDifferenceKineticWork_eq_integral_split
    (left right :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (terminal : Icc (0 : ℝ) requestedTime)
    (wave : NonzeroIntegerWavevector) :
    actualWaveDifferenceKineticWork left right terminal wave =
      ∫ time in (0 : ℝ)..terminal.1,
        (actualWaveDifferenceNonlinearKineticPower
            left right wave time -
          actualWaveDifferenceViscousKineticPower
            left right wave time) := by
  unfold actualWaveDifferenceKineticWork
    actualWaveDifferenceEnergyWork
  rw [← intervalIntegral.integral_div]
  apply intervalIntegral.integral_congr
  intro time timeMem
  exact
    actualWaveDifference_kineticPower_split
      left right wave time

end SameHorizon

end

end ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticWork
end NavierStokes
end SaturationMonoid
