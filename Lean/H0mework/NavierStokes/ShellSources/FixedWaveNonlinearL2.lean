import H0mework.NavierStokes.ShellSources.NonlinearNegativeOneForcing

/-!
# Fixed-wave time-`L²` nonlinear rows

The source-generated whole `L²_t H⁻¹_x` forcing is evaluated at an arbitrary
nonzero Fourier wave and unweighted by the square-root Laplacian.  The
result is an actual time-`L²` representative of the same nonlinear row that
appears in the weak equation and mild Duhamel identity.

This upgrades the earlier rowwise `L¹` carrier using the whole forcing
receipt.  The wave is arbitrary; no finite inventory, cutoff, target row,
or rowwise integrability witness is supplied.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientGeneratedIntegerShellFixedWaveNonlinearL2

open scoped BigOperators ENNReal Topology

open MeasureTheory
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeSubsequence
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageReceiptSquare
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageReceiptSquare.GeneratedIntegerShellInfiniteLineage
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellCriticalSerrinWeakLimit
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellNonlinearNegativeOneForcing
open ThreeDimensionalVorticityCoefficientTransverseSpaceTimeNonlinearRow

noncomputable section

/-- The actual nonlinear row at one nonzero wave, now represented in
time `L²` by unweighting the corresponding coordinate of the whole
negative-one forcing. -/
def NonlinearNegativeOneForcingReceipt.fixedWaveNonlinearL2
    {lineage : GeneratedIntegerShellInfiniteLineage}
    {ν : Viscosity}
    {θ requestedTime : ℝ}
    {θLtOne : θ < 1}
    {criticalMargin :
      ∀ length : ℕ,
        ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier.criticalEnstrophyLatticeConstant *
            ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance.finiteStateVorticityCoefficientEnstrophy
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
    (output : IntegerWavevector) :
    FixedWaveSpaceTimeState requestedTime :=
  (Real.sqrt (integerWaveViscousMultiplier output) : ℂ) •
    fixedWaveSpaceTimeRestriction requestedTime output
      receipt.negativeOneForcing

/--
The new time-`L²` row is almost everywhere the actual whole quadratic
nonlinear row of the same transverse weak-limit state.
-/
theorem NonlinearNegativeOneForcingReceipt.fixedWaveNonlinearL2_coeFn
    {lineage : GeneratedIntegerShellInfiniteLineage}
    {ν : Viscosity}
    {θ requestedTime : ℝ}
    {θLtOne : θ < 1}
    {criticalMargin :
      ∀ length : ℕ,
        ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier.criticalEnstrophyLatticeConstant *
            ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance.finiteStateVorticityCoefficientEnstrophy
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
    (output : IntegerWavevector)
    (outputNe : output ≠ 0) :
    ∀ᵐ time ∂(commonTimeMeasure requestedTime),
      NonlinearNegativeOneForcingReceipt.fixedWaveNonlinearL2
          receipt output time =
        transverseSpaceTimeNonlinearRow
          receipt.transverseLimit output time := by
  filter_upwards [
    MeasureTheory.Lp.coeFn_smul
      (Real.sqrt (integerWaveViscousMultiplier output) : ℂ)
      (fixedWaveSpaceTimeRestriction requestedTime output
        receipt.negativeOneForcing),
    fixedWaveSpaceTimeRestriction_coeFn requestedTime output
      receipt.negativeOneForcing,
    receipt.negativeOneForcing_unweighted_row_ae output outputNe] with
      time smulEq restrictionEq unweightedEq
  rw [NonlinearNegativeOneForcingReceipt.fixedWaveNonlinearL2,
    smulEq]
  change
    (Real.sqrt (integerWaveViscousMultiplier output) : ℂ) •
        fixedWaveSpaceTimeRestriction requestedTime output
          receipt.negativeOneForcing time =
      transverseSpaceTimeNonlinearRow
        receipt.transverseLimit output time
  rw [restrictionEq]
  have scalarActionEq :
      (Real.sqrt (integerWaveViscousMultiplier output) : ℂ) •
          (receipt.negativeOneForcing time) output =
        (Real.sqrt (integerWaveViscousMultiplier output) : ℝ) •
          (receipt.negativeOneForcing time) output := by
    ext coordinate
    simp [Complex.real_smul]
  rw [scalarActionEq]
  exact unweightedEq

end

end ThreeDimensionalVorticityCoefficientGeneratedIntegerShellFixedWaveNonlinearL2
end NavierStokes
end SaturationMonoid
