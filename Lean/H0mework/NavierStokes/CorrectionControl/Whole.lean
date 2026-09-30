import H0mework.NavierStokes.CorrectionControl.Rows
import H0mework.NavierStokes.Fourier.IntegerLatticeCriticalKernel

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.NativeTurbulenceControl

open scoped BigOperators ENNReal
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy
open ThreeDimensionalVorticityCoefficientWholeKineticMassSeparation
open ThreeDimensionalIntegerLatticeCriticalKernel
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationNativeTurbulenceLaw

noncomputable section

def correctionCap (state : ComplexVorticityHilbertState) : ℝ :=
  2 * (6 * Real.pi) ^ 2 * puncturedWholeVorticityKineticMass state

theorem correctionCap_nonneg (state : ComplexVorticityHilbertState) : 0 ≤ correctionCap state := by
  exact mul_nonneg (by positivity) (puncturedWholeVorticityKineticMass_nonneg state)

/-- The original complete correction in the homogeneous negative-four metric.
The multiplier uses integer frequencies; no mode is removed from the whole sum. -/
def weightedCorrectionRow (modes : Finset IntegerWavevector) (state : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) : ComplexCoordinateVector :=
  (integerWaveNormSq wave)⁻¹ ^ 2 • nativeTurbulenceCorrectionAt modes state wave

theorem weightedCorrectionRow_norm_le (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) (zero : state 0 = 0)
    (transverse : WholeStateTransverse state) (wave : IntegerWavevector) :
    ‖weightedCorrectionRow modes state wave‖ ≤ correctionCap state * (integerWaveNormSq wave)⁻¹ := by
  by_cases vanishes : integerWaveNormSq wave = 0
  · simp [weightedCorrectionRow, vanishes]
  calc
    ‖weightedCorrectionRow modes state wave‖ = (integerWaveNormSq wave)⁻¹ ^ 2 *
        ‖nativeTurbulenceCorrectionAt modes state wave‖ := by
      rw [weightedCorrectionRow, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    _ ≤ (integerWaveNormSq wave)⁻¹ ^ 2 *
        (2 * curlWeight wave ^ 2 * puncturedWholeVorticityKineticMass state) :=
      mul_le_mul_of_nonneg_left (correction_row_norm_le_kinetic modes state zero transverse wave) (sq_nonneg _)
    _ = _ := by
      unfold curlWeight correctionCap
      rw [mul_pow, Real.sq_sqrt (integerWaveNormSq_nonneg wave)]
      field_simp

theorem weightedCorrectionRow_sq_le (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) (zero : state 0 = 0)
    (transverse : WholeStateTransverse state) (wave : IntegerWavevector) :
    ‖weightedCorrectionRow modes state wave‖ ^ 2 ≤ correctionCap state ^ 2 * integerWaveCriticalKernel wave := by
  have positive := mul_nonneg (correctionCap_nonneg state) (inv_nonneg.mpr (integerWaveNormSq_nonneg wave))
  have bound := (sq_le_sq₀ (norm_nonneg _) positive).mpr
    (weightedCorrectionRow_norm_le modes state zero transverse wave)
  simpa only [integerWaveCriticalKernel, mul_pow] using bound

theorem weightedCorrectionRow_sq_summable (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) (zero : state 0 = 0) (transverse : WholeStateTransverse state) :
    Summable fun wave => ‖weightedCorrectionRow modes state wave‖ ^ 2 :=
  Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
    (weightedCorrectionRow_sq_le modes state zero transverse)
    (summable_integerWaveCriticalKernel.mul_left (correctionCap state ^ 2))

def wholeCorrection (modes : Finset IntegerWavevector) (state : ComplexVorticityHilbertState)
    (zero : state 0 = 0) (transverse : WholeStateTransverse state) : ComplexVorticityHilbertState :=
  ⟨weightedCorrectionRow modes state, by
    apply memℓp_gen
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      weightedCorrectionRow_sq_summable modes state zero transverse⟩

@[simp] theorem wholeCorrection_apply (modes : Finset IntegerWavevector) (state : ComplexVorticityHilbertState)
    (zero : state 0 = 0) (transverse : WholeStateTransverse state) (wave : IntegerWavevector) :
    wholeCorrection modes state zero transverse wave = weightedCorrectionRow modes state wave := rfl

theorem wholeCorrection_reconstruct (modes : Finset IntegerWavevector) (state : ComplexVorticityHilbertState)
    (zero : state 0 = 0) (transverse : WholeStateTransverse state) (wave : IntegerWavevector) :
    integerWaveNormSq wave ^ 2 • wholeCorrection modes state zero transverse wave =
      nativeTurbulenceCorrectionAt modes state wave := by
  by_cases vanishes : integerWaveNormSq wave = 0
  · have bound := correction_row_norm_le_kinetic modes state zero transverse wave
    have rowZero : nativeTurbulenceCorrectionAt modes state wave = 0 := by
      apply norm_le_zero_iff.mp
      simpa [curlWeight, vanishes] using bound
    simp [vanishes, rowZero]
  · rw [wholeCorrection_apply, weightedCorrectionRow, smul_smul, ← mul_pow,
      mul_inv_cancel₀ vanishes, one_pow, one_smul]

/-- One physical kinetic budget controls the full native correction uniformly
in its observation inventory, including arbitrarily many coface revisions. -/
theorem wholeCorrection_norm_sq_le (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) (zero : state 0 = 0) (transverse : WholeStateTransverse state) :
    ‖wholeCorrection modes state zero transverse‖ ^ 2 ≤
      correctionCap state ^ 2 * ∑' wave, integerWaveCriticalKernel wave := by
  have normIdentity : ‖wholeCorrection modes state zero transverse‖ ^ 2 =
      ∑' wave, ‖weightedCorrectionRow modes state wave‖ ^ 2 := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, wholeCorrection_apply] using
      (lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num) (wholeCorrection modes state zero transverse))
  rw [normIdentity]
  calc
    (∑' wave, ‖weightedCorrectionRow modes state wave‖ ^ 2) ≤
        ∑' wave, correctionCap state ^ 2 * integerWaveCriticalKernel wave :=
      (weightedCorrectionRow_sq_summable modes state zero transverse).tsum_le_tsum
        (weightedCorrectionRow_sq_le modes state zero transverse)
        (summable_integerWaveCriticalKernel.mul_left _)
    _ = _ := tsum_mul_left

end
end SaturationMonoid.NavierStokes.NativeTurbulenceControl
