import H0mework.NavierStokes.SourceGeometry.SymmetryTime

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.SourceEvenFrequency

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientTransverseSpaceTimeNonlinearRow
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientInfiniteNonlinearNegativeSobolev
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeNonlinearNegativeOne
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeViscousNegativeOne

noncomputable section

theorem nonlinear_shift (field : ComplexVorticityHilbertState) (wave : IntegerWavevector) :
    wholeStateVorticityNonlinearCoefficientAt (shift field) wave =
      phase wave • wholeStateVorticityNonlinearCoefficientAt field wave := by
  simpa only [wholeStateVorticityBilinearCoefficientAt_self] using shifted_nonlinear field field wave

theorem weightedNonlinear_shift (field : ComplexVorticityHilbertState) (wave : IntegerWavevector) :
    wholeStateVorticityNonlinearNegativeOneWeightedCoefficient (shift field) wave =
      phase wave • wholeStateVorticityNonlinearNegativeOneWeightedCoefficient field wave := by
  unfold wholeStateVorticityNonlinearNegativeOneWeightedCoefficient
  by_cases zero : wave = 0
  · simp only [if_pos zero, smul_zero]
  · rw [if_neg zero, if_neg zero, nonlinear_shift]
    exact smul_comm _ _ _

theorem weightedViscous_shift (viscosity : ℝ) (field : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) :
    wholeStateVorticityViscousNegativeOneWeightedCoefficient viscosity (shift field) wave =
      phase wave • wholeStateVorticityViscousNegativeOneWeightedCoefficient viscosity field wave := by
  simp only [wholeStateVorticityViscousNegativeOneWeightedCoefficient, shift_apply]
  exact smul_comm _ _ _

theorem nonlinearFunction_shift {time : ℝ} (field : TransverseSpaceTimeState time) :
    ∀ᵐ actual ∂commonTimeMeasure time,
      wholeSpaceTimeNonlinearNegativeOneFunction (transverseTimeShift time field) actual =
        shift (wholeSpaceTimeNonlinearNegativeOneFunction field actual) := by
  filter_upwards [transverseTimeShift_ae field] with actual same
  by_cases gradient : Summable fun wave : IntegerWavevector =>
      integerWaveNormSq wave * complexCoordinateAmplitudeSq ((field actual).val wave)
  · have newGradient : Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave * complexCoordinateAmplitudeSq
          ((transverseTimeShift time field actual).val wave) := by
      simpa only [same, shift_amplitude] using gradient
    rw [wholeSpaceTimeNonlinearNegativeOneFunction_of_summable _ _ newGradient,
      wholeSpaceTimeNonlinearNegativeOneFunction_of_summable _ _ gradient]
    apply Subtype.ext
    funext wave
    simp only [wholeStateVorticityNonlinearNegativeOneState_apply, shift_apply, same,
      weightedNonlinear_shift]
    rfl
  · have newGradient : ¬ Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave * complexCoordinateAmplitudeSq
          ((transverseTimeShift time field actual).val wave) := by
      simpa only [same, shift_amplitude] using gradient
    simp only [wholeSpaceTimeNonlinearNegativeOneFunction, dif_neg gradient, dif_neg newGradient, map_zero]

theorem viscousFunction_shift {time : ℝ} (viscosity : ℝ) (field : SpaceTimeState time) :
    ∀ᵐ actual ∂commonTimeMeasure time,
      wholeSpaceTimeViscousNegativeOneFunction viscosity (timeShift time field) actual =
        shift (wholeSpaceTimeViscousNegativeOneFunction viscosity field actual) := by
  filter_upwards [timeShift_ae field] with actual same
  by_cases gradient : Summable fun wave : IntegerWavevector =>
      integerWaveNormSq wave * complexCoordinateAmplitudeSq (field actual wave)
  · have newGradient : Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave * complexCoordinateAmplitudeSq (timeShift time field actual wave) := by
      simpa only [same, shift_amplitude] using gradient
    rw [wholeSpaceTimeViscousNegativeOneFunction_of_summable _ _ _ newGradient,
      wholeSpaceTimeViscousNegativeOneFunction_of_summable _ _ _ gradient]
    apply Subtype.ext
    funext wave
    simp only [wholeStateVorticityViscousNegativeOneState_apply, shift_apply, same,
      weightedViscous_shift]
  · have newGradient : ¬ Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave * complexCoordinateAmplitudeSq (timeShift time field actual wave) := by
      simpa only [same, shift_amplitude] using gradient
    simp only [wholeSpaceTimeViscousNegativeOneFunction, dif_neg gradient, dif_neg newGradient, map_zero]

end
end SaturationMonoid.NavierStokes.SourceEvenFrequency
