import H0mework.NavierStokes.Accumulation.NativeTurbulenceLaw
import H0mework.NavierStokes.Accumulation.WholeReceiptKineticTimeModulus

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.NativeTurbulenceControl

open Set
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageHilbertCompletion
open ThreeDimensionalVorticityCoefficientWholeVelocityFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientWholeReceiptKineticTimeModulus
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartActualFourierConeAdvance
open ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationNativeTurbulenceLaw

noncomputable section

def curlWeight (wave : IntegerWavevector) : ℝ :=
  (6 * Real.pi) * Real.sqrt (integerWaveNormSq wave)

theorem curlWeight_nonneg (wave : IntegerWavevector) : 0 ≤ curlWeight wave := by
  unfold curlWeight
  positivity

theorem nonlinear_row_norm_le_velocity (state : ComplexVorticityHilbertState)
    (zero : state 0 = 0) (transverse : WholeStateTransverse state) (wave : IntegerWavevector) :
    ‖wholeStateVorticityNonlinearCoefficientAt state wave‖ ≤
      curlWeight wave ^ 2 * ‖wholeBiotSavartVelocityState state‖ ^ 2 := by
  have velocity := wholeStateVelocityBilinearCoefficientAt_norm_le
    (wholeBiotSavartVelocityState state) (wholeBiotSavartVelocityState state)
    (wholeBiotSavartVelocityState_transverse state) wave
  rw [wholeStateVorticityNonlinearCoefficientAt_eq_fourierCurl_velocity state zero transverse]
  calc
    ‖fourierCurlCoefficient wave
        (wholeStateVelocityNonlinearCoefficientAt (wholeBiotSavartVelocityState state) wave)‖ ≤
        curlWeight wave *
          ‖wholeStateVelocityNonlinearCoefficientAt (wholeBiotSavartVelocityState state) wave‖ :=
      fourierCurlCoefficient_norm_le_six_pi_sqrt _ _
    _ ≤ curlWeight wave *
        ((6 * Real.pi) * Real.sqrt (integerWaveNormSq wave) *
          ‖wholeBiotSavartVelocityState state‖ * ‖wholeBiotSavartVelocityState state‖) :=
      mul_le_mul_of_nonneg_left velocity (curlWeight_nonneg wave)
    _ = _ := by unfold curlWeight; ring

theorem velocity_projection (modes : Finset IntegerWavevector) (state : ComplexVorticityHilbertState) :
    wholeBiotSavartVelocityState (complexSharpSupportProjection modes state) =
      complexSharpSupportProjection modes (wholeBiotSavartVelocityState state) := by
  ext wave
  by_cases member : wave ∈ modes <;>
    simp [wholeBiotSavartVelocityState_apply, finiteStateVelocityCoefficient,
      complexSharpSupportProjection_apply, member, biotSavartVelocityCoefficient]

/-- The original coface correction consumes the complete velocity field.
The bound contains no full-vorticity ceiling or truncation of its input interactions. -/
theorem correction_row_norm_le_velocity (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) (zero : state 0 = 0)
    (transverse : WholeStateTransverse state) (wave : IntegerWavevector) :
    ‖nativeTurbulenceCorrectionAt modes state wave‖ ≤
      2 * curlWeight wave ^ 2 * ‖wholeBiotSavartVelocityState state‖ ^ 2 := by
  have projectedZero : complexSharpSupportProjection modes state 0 = 0 := by
    simp [complexSharpSupportProjection_apply, zero]
  have projectedTransverse : WholeStateTransverse (complexSharpSupportProjection modes state) := by
    intro output
    by_cases member : output ∈ modes
    · simpa [complexSharpSupportProjection_apply, member] using transverse output
    · simp [complexSharpSupportProjection_apply, member]
  have projectedNorm : ‖wholeBiotSavartVelocityState (complexSharpSupportProjection modes state)‖ ≤
      ‖wholeBiotSavartVelocityState state‖ := by
    rw [velocity_projection]
    exact complexSharpSupportProjection_norm_le modes _
  have resolved := (nonlinear_row_norm_le_velocity _ projectedZero projectedTransverse wave).trans
    (mul_le_mul_of_nonneg_left
      ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr projectedNorm) (sq_nonneg _))
  have projected : ‖projectedWholeNonlinearCoefficientAt modes state wave‖ ≤
      curlWeight wave ^ 2 * ‖wholeBiotSavartVelocityState state‖ ^ 2 := by
    by_cases member : wave ∈ modes
    · simpa [projectedWholeNonlinearCoefficientAt, member] using
        nonlinear_row_norm_le_velocity state zero transverse wave
    · simp only [projectedWholeNonlinearCoefficientAt, if_neg member, norm_zero]
      positivity
  exact (norm_sub_le _ _).trans ((add_le_add projected resolved).trans_eq (by ring))

theorem correction_row_norm_le_kinetic (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) (zero : state 0 = 0)
    (transverse : WholeStateTransverse state) (wave : IntegerWavevector) :
    ‖nativeTurbulenceCorrectionAt modes state wave‖ ≤
      2 * curlWeight wave ^ 2 * puncturedWholeVorticityKineticMass state := by
  have square := (wholeState_norm_sq_le_wholeVorticityEuclideanMass
    (wholeBiotSavartVelocityState state)).trans_eq
      (wholeVorticityEuclideanMass_wholeBiotSavartVelocityState state transverse)
  exact (correction_row_norm_le_velocity modes state zero transverse wave).trans
    (mul_le_mul_of_nonneg_left square (by positivity))

end
end SaturationMonoid.NavierStokes.NativeTurbulenceControl
