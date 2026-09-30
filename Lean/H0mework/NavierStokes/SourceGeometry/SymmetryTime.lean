import H0mework.NavierStokes.SourceGeometry.SymmetryFields

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.SourceEvenFrequency

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeSubsequence
open ThreeDimensionalVorticityCoefficientInfiniteFixedWaveWeakCarrier
open ThreeDimensionalVorticityCoefficientTransverseSpaceTimeNonlinearRow
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeGradientLowerSemicontinuity

noncomputable section

def timeShift (time : ℝ) : SpaceTimeState time →L[ℂ] SpaceTimeState time :=
  shift.compLpL 2 (commonTimeMeasure time)

def transverseTimeShift (time : ℝ) : TransverseSpaceTimeState time →L[ℂ] TransverseSpaceTimeState time :=
  transverseShift.compLpL 2 (commonTimeMeasure time)

theorem timeShift_ae {time : ℝ} (field : SpaceTimeState time) :
    ∀ᵐ actual ∂commonTimeMeasure time, timeShift time field actual = shift (field actual) :=
  shift.coeFn_compLpL field

theorem transverseTimeShift_ae {time : ℝ} (field : TransverseSpaceTimeState time) :
    ∀ᵐ actual ∂commonTimeMeasure time,
      (transverseTimeShift time field actual).val = shift (field actual).val := by
  filter_upwards [transverseShift.coeFn_compLpL field] with actual same
  exact congrArg Subtype.val same

theorem timeShift_inclusion {time : ℝ} (field : TransverseSpaceTimeState time) :
    transverseSpaceTimeInclusion time (transverseTimeShift time field) =
      timeShift time (transverseSpaceTimeInclusion time field) := by
  apply Lp.ext
  filter_upwards [transverseSpaceTimeInclusion_coeFn time (transverseTimeShift time field),
    transverseTimeShift_ae field, timeShift_ae (transverseSpaceTimeInclusion time field),
    transverseSpaceTimeInclusion_coeFn time field] with actual first second third fourth
  rw [first, second, third, fourth]

theorem timeShift_row {time : ℝ} (field : SpaceTimeState time) (wave : IntegerWavevector) :
    fixedWaveSpaceTimeRestriction time wave (timeShift time field) =
      phase wave • fixedWaveSpaceTimeRestriction time wave field := by
  apply Lp.ext
  filter_upwards [fixedWaveSpaceTimeRestriction_coeFn time wave (timeShift time field),
    timeShift_ae field, fixedWaveSpaceTimeRestriction_coeFn time wave field,
    Lp.coeFn_smul (phase wave) (fixedWaveSpaceTimeRestriction time wave field)] with
      actual first second third fourth
  rw [first, second, fourth]
  simpa only [Pi.smul_apply, shift_apply] using
    (congrArg (fun row : ComplexCoordinateVector => phase wave • row) third).symm

theorem timeShift_gradient {time : ℝ} (field : SpaceTimeState time) (wave : IntegerWavevector) :
    wholeSpaceTimeVorticityGradientDensity time (timeShift time field) wave =
      wholeSpaceTimeVorticityGradientDensity time field wave := by
  simp only [wholeSpaceTimeVorticityGradientDensity, timeShift_row, norm_smul, phase_norm, one_mul]

def pathShift {time : ℝ}
    (path : BoundedContinuousFunction (Icc (0 : ℝ) time) ComplexVorticityHilbertState) :
    BoundedContinuousFunction (Icc (0 : ℝ) time) ComplexVorticityHilbertState :=
  BoundedContinuousFunction.mkOfCompact ⟨fun actual => shift (path actual),
    shift.continuous.comp path.continuous⟩

@[simp] theorem pathShift_apply {time : ℝ}
    (path : BoundedContinuousFunction (Icc (0 : ℝ) time) ComplexVorticityHilbertState)
    (actual : Icc (0 : ℝ) time) : pathShift path actual = shift (path actual) := rfl

theorem pathShift_toLp {time : ℝ}
    (path : BoundedContinuousFunction (Icc (0 : ℝ) time) ComplexVorticityHilbertState) :
    BoundedContinuousFunction.toLp 2 (commonTimeMeasure time) ℂ (pathShift path) =
      timeShift time (BoundedContinuousFunction.toLp 2 (commonTimeMeasure time) ℂ path) := by
  apply Lp.ext
  filter_upwards [BoundedContinuousFunction.coeFn_toLp (p := 2) (μ := commonTimeMeasure time)
      (𝕜 := ℂ) (pathShift path),
    timeShift_ae (BoundedContinuousFunction.toLp 2 (commonTimeMeasure time) ℂ path),
    BoundedContinuousFunction.coeFn_toLp (p := 2) (μ := commonTimeMeasure time) (𝕜 := ℂ) path] with
      actual first second third
  rw [first, second, third, pathShift_apply]

end
end SaturationMonoid.NavierStokes.SourceEvenFrequency
