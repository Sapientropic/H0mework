import H0mework.NavierStokes.SourceGeometry.SymmetryForcing

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.SourceEvenFrequency

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientTransverseSpaceTimeNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellFixedWaveNonlinearL2
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientFiniteGalerkinMildDuhamel
open ThreeDimensionalVorticityCoefficientGeneratedPathInfiniteNonlinearRowLimit
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteMildDuhamel
open ThreeDimensionalVorticityCoefficientWholeTangentEnergyTransport

noncomputable section

theorem nonlinearRow_shift {time : ℝ} (field : TransverseSpaceTimeState time)
    (wave : IntegerWavevector) :
    transverseSpaceTimeNonlinearRow (transverseTimeShift time field) wave =
      phase wave • transverseSpaceTimeNonlinearRow field wave := by
  apply Lp.ext
  filter_upwards [transverseSpaceTimeNonlinearRow_coeFn (transverseTimeShift time field) wave,
    transverseSpaceTimeNonlinearRow_coeFn field wave, transverseTimeShift_ae field,
    Lp.coeFn_smul (phase wave) (transverseSpaceTimeNonlinearRow field wave)] with actual first second same fourth
  rw [first, fourth]
  change wholeStateVorticityNonlinearCoefficientAt
    (transverseTimeShift time field actual).val wave =
      phase wave • (transverseSpaceTimeNonlinearRow field wave) actual
  rw [second]
  change wholeStateVorticityNonlinearCoefficientAt
    (transverseTimeShift time field actual).val wave =
      phase wave • wholeStateVorticityNonlinearCoefficientAt (field actual).val wave
  rw [same, nonlinear_shift]

theorem mild_shift (time viscosity : ℝ) (wave : IntegerWavevector)
    (initial : ComplexCoordinateVector) (nonlinear : NonlinearRowSpaceTimeState time)
    (actual : Icc (0 : ℝ) time) :
    fixedWaveHeatDuhamelValue time viscosity wave (phase wave • initial) (phase wave • nonlinear) actual =
      phase wave • fixedWaveHeatDuhamelValue time viscosity wave initial nonlinear actual := by
  unfold fixedWaveHeatDuhamelValue
  rw [smul_add]
  congr 1
  · exact smul_comm _ _ _
  · calc
      _ = ∫ earlier in Iic actual, phase wave •
          (finiteStateVorticityHeatMultiplier viscosity (actual.val - earlier.val) wave • nonlinear earlier)
          ∂commonTimeMeasure time := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_of_ae (Lp.coeFn_smul (phase wave) nonlinear)] with earlier same
        rw [same]
        exact smul_comm
          (finiteStateVorticityHeatMultiplier viscosity (actual.val - earlier.val) wave)
          (phase wave) (nonlinear earlier)
      _ = _ := integral_smul _ _

theorem zeroExtension_shift (time : ℝ) (wave : IntegerWavevector)
    (tangent : Icc (0 : ℝ) time → ComplexCoordinateVector) (actual : ℝ) :
    commonTimeZeroExtension time (fun point => phase wave • tangent point) actual =
      phase wave • commonTimeZeroExtension time tangent actual := by
  unfold commonTimeZeroExtension
  split_ifs <;> simp

end
end SaturationMonoid.NavierStokes.SourceEvenFrequency
