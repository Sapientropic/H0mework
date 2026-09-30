import H0mework.NavierStokes.ShellSources.InfiniteMildDuhamel
import H0mework.NavierStokes.WholeSpace.InfiniteFixedWaveResidualSilenceWeakCarrier

/-!
# Fixed-wave Duhamel law from whole-residual silence

An actual finite Galerkin trajectory already has an exact heat/Duhamel law
on every retained Fourier row.  This module closes the complementary case:
if an omitted row has zero whole-PDE residual throughout the same physical
interval, then the support law makes its coefficient zero, and residual
silence makes its whole nonlinear row zero.  Its Duhamel value is therefore
zero as well.

The theorem is a local actual-trajectory consumer.  It accepts neither
coverage nor a target limit, continuation path, or external mild witness.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
    ThreeDimensionalVorticityCoefficientInfiniteFixedWaveResidualSilenceMildDuhamel

open scoped ENNReal Topology

open Set
open Filter
open MeasureTheory
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinMildDuhamel
open ThreeDimensionalVorticityCoefficientCanonicalExhaustiveGalerkinTarget
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientGeneratedPathInfiniteNonlinearRowLimit
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientInfiniteFixedWaveWeakCarrier
open ThreeDimensionalVorticityCoefficientInfiniteFixedWaveResidualSilenceWeakCarrier
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteMildDuhamel

noncomputable section

/--
Every fixed row of one actual finite Galerkin trajectory has its exact
heat/Duhamel representation when its whole PDE residual vanishes on the
same physical interval.  Retained rows use the existing finite-row theorem;
omitted rows are forced silent in both state and nonlinear readout.
-/
theorem finiteSupportWave_eq_fixedWaveHeatDuhamelValue_of_wholeResidual_zero
    (modes : Finset IntegerWavevector)
    (wave : IntegerWavevector)
    (ν requestedTime : ℝ)
    (requestedTimePos : 0 < requestedTime)
    (trajectory : ℝ → ComplexVorticityHilbertState)
    (evolves :
      ∀ t ∈ Icc (0 : ℝ) requestedTime,
        HasDerivAt trajectory
          (finiteStateVorticityGenerator
            modes ν (trajectory t)) t)
    (supported :
      ∀ t ∈ Icc (0 : ℝ) requestedTime,
        ∀ output : IntegerWavevector,
          output ∉ modes → trajectory t output = 0)
    (transverse :
      ∀ t ∈ Icc (0 : ℝ) requestedTime,
        WholeStateTransverse (trajectory t))
    (wholeResidualZero :
      ∀ t ∈ Icc (0 : ℝ) requestedTime,
        wholeLatticeVorticityFourierPDEResidualAt
            ν (trajectory t)
            (finiteStateVorticityGenerator
              modes ν (trajectory t))
            wave =
          0)
    (time : Icc (0 : ℝ) requestedTime) :
    trajectory time.1 wave =
      fixedWaveHeatDuhamelValue requestedTime ν wave
        (trajectory 0 wave)
        (wholeNonlinearRowSpaceTimePath requestedTime
          trajectory
          (fun t timeMem =>
            (evolves t timeMem).continuousAt.continuousWithinAt)
          transverse wave)
        time := by
  by_cases waveMem : wave ∈ modes
  · exact
      finiteSupportWave_eq_fixedWaveHeatDuhamelValue
        modes wave waveMem ν requestedTime requestedTimePos
        trajectory evolves supported transverse time
  · let trajectoryContinuous :
        ContinuousOn trajectory (Icc (0 : ℝ) requestedTime) :=
      fun t timeMem =>
        (evolves t timeMem).continuousAt.continuousWithinAt
    let nonlinearLp : NonlinearRowSpaceTimeState requestedTime :=
      wholeNonlinearRowSpaceTimePath requestedTime
        trajectory trajectoryContinuous transverse wave
    have stateZero :
        ∀ t ∈ Icc (0 : ℝ) requestedTime,
          trajectory t wave = 0 := by
      intro t timeMem
      exact supported t timeMem wave waveMem
    have nonlinearZero :
        ∀ t ∈ Icc (0 : ℝ) requestedTime,
          wholeStateVorticityNonlinearCoefficientAt
            (trajectory t) wave = 0 := by
      intro t timeMem
      have residualZero := wholeResidualZero t timeMem
      have rowZero := stateZero t timeMem
      simpa [wholeLatticeVorticityFourierPDEResidualAt,
        wholeLatticeVorticityFourierTangentAt,
        finiteStateVorticityGenerator_apply,
        waveMem, rowZero] using residualZero
    have nonlinearLpZero : nonlinearLp = 0 := by
      apply MeasureTheory.Lp.ext
      have nonlinearBoundedAE :
          ⇑nonlinearLp =ᵐ[commonTimeMeasure requestedTime]
            ⇑(wholeNonlinearRowBoundedPath requestedTime
              trajectory trajectoryContinuous transverse wave) := by
        dsimp [nonlinearLp, wholeNonlinearRowSpaceTimePath]
        exact
          BoundedContinuousFunction.coeFn_toLp
            (p := (1 : ℝ≥0∞))
            (μ := commonTimeMeasure requestedTime)
            ℂ
            (wholeNonlinearRowBoundedPath requestedTime
              trajectory trajectoryContinuous transverse wave)
      filter_upwards [nonlinearBoundedAE,
        MeasureTheory.Lp.coeFn_zero ComplexCoordinateVector 1
          (commonTimeMeasure requestedTime)] with t nonlinearEq zeroEq
      rw [nonlinearEq, zeroEq]
      exact nonlinearZero t.1 t.2
    have initialZero : trajectory 0 wave = 0 := by
      exact stateZero 0 ⟨le_rfl, requestedTimePos.le⟩
    have valueZero : trajectory time.1 wave = 0 :=
      stateZero time.1 time.2
    have duhamelZero :
        (∫ earlier in Iic time,
            finiteStateVorticityHeatMultiplier
                ν (time.1 - earlier.1) wave •
              (0 : NonlinearRowSpaceTimeState requestedTime) earlier
            ∂(commonTimeMeasure requestedTime)) = 0 := by
      calc
        (∫ earlier in Iic time,
            finiteStateVorticityHeatMultiplier
                ν (time.1 - earlier.1) wave •
              (0 : NonlinearRowSpaceTimeState requestedTime) earlier
            ∂(commonTimeMeasure requestedTime)) =
            ∫ _earlier in Iic time,
              (0 : ComplexCoordinateVector)
            ∂(commonTimeMeasure requestedTime) := by
              apply integral_congr_ae
              filter_upwards [ae_restrict_of_ae
                (MeasureTheory.Lp.coeFn_zero ComplexCoordinateVector 1
                  (commonTimeMeasure requestedTime))] with earlier zeroEq
              rw [zeroEq]
              exact smul_zero _
        _ = 0 := by simp
    change trajectory time.1 wave =
      fixedWaveHeatDuhamelValue requestedTime ν wave
        (trajectory 0 wave) nonlinearLp time
    rw [fixedWaveHeatDuhamelValue, initialZero, nonlinearLpZero,
      duhamelZero]
    rw [smul_zero, zero_add]
    exact valueZero

end

end
    ThreeDimensionalVorticityCoefficientInfiniteFixedWaveResidualSilenceMildDuhamel
end NavierStokes
end SaturationMonoid
