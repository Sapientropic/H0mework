import H0mework.NavierStokes.SourceEstimates.CoefficientWork
import H0mework.NavierStokes.Accumulation.WholeActionTube
import H0mework.NavierStokes.Crossing.FrequencySupportExhaustion
import H0mework.NavierStokes.Restart.VelocityPairDiagonalAction

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.NonlinearWork

open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientInfiniteNonlinearNegativeSobolev
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeViscousNegativeOne
open ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy
open ThreeDimensionalVorticityCoefficientWholeActionTube
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingFrequencySupportExhaustion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityPairDiagonalAction

noncomputable section

def value (field : ComplexVorticityHilbertState) : Real :=
  ∑' wave, complexCoordinateRealInner (field wave) (wholeStateVorticityNonlinearCoefficientAt field wave)

variable (field : ComplexVorticityHilbertState) (transverse : WholeStateTransverse field)
  (gradient : Summable fun wave : IntegerWavevector => integerWaveNormSq wave *
    complexCoordinateAmplitudeSq (field wave))

def gradientState := wholeStateVorticityViscousNegativeOneState 1 field gradient
private def weightedNonlinear := wholeStateVorticityNonlinearNegativeOneState field transverse gradient

private theorem transfer_smul (scalar : Real) (left right : ComplexCoordinateVector) :
    complexCoordinateRealInner (scalar • left) right = complexCoordinateRealInner left (scalar • right) := by
  unfold complexCoordinateRealInner
  apply Finset.sum_congr rfl
  intro coordinate _
  simp only [Pi.smul_apply, Complex.real_smul, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring

private theorem row_eq_weighted (wave : IntegerWavevector) :
    complexCoordinateRealInner (field wave) (wholeStateVorticityNonlinearCoefficientAt field wave) =
      complexCoordinateRealInner (gradientState field gradient wave)
        (weightedNonlinear field transverse gradient wave) := by
  rw [gradientState, wholeStateVorticityViscousNegativeOneState_apply,
    wholeStateVorticityViscousNegativeOneWeightedCoefficient, one_mul,
    weightedNonlinear, wholeStateVorticityNonlinearNegativeOneState_apply,
    wholeStateVorticityNonlinearNegativeOneWeightedCoefficient]
  by_cases zero : wave = 0
  · subst wave
    rw [if_pos rfl, wholeStateVorticityNonlinearCoefficientAt_zero_of_transverse field transverse]
    simp [complexCoordinateRealInner]
  · rw [if_neg zero, transfer_smul, smul_smul,
      mul_inv_cancel₀ (ne_of_gt (Real.sqrt_pos.2 (integerWaveViscousMultiplier_pos ⟨wave, zero⟩))), one_smul]

include transverse gradient in
theorem summable :
    Summable fun wave => complexCoordinateRealInner (field wave) (wholeStateVorticityNonlinearCoefficientAt field wave) :=
  (CoefficientWork.summable (gradientState field gradient) (weightedNonlinear field transverse gradient)).congr
    (fun wave => (row_eq_weighted field transverse gradient wave).symm)

theorem gradientState_mass :
    wholeVorticityEuclideanMass (gradientState field gradient) =
      (2 * Real.pi) ^ 2 * wholeStateVorticityGradientMass field := by
  unfold wholeVorticityEuclideanMass wholeStateVorticityGradientMass
  rw [← tsum_mul_left]
  apply tsum_congr
  intro wave
  rw [vorticityRowAmplitude_sq, gradientState, wholeStateVorticityViscousNegativeOneState_apply,
    wholeStateVorticityViscousNegativeOneWeightedCoefficient, one_mul]
  change complexCoordinateAmplitudeSq (Real.sqrt (integerWaveViscousMultiplier wave) • field wave) = _
  rw [complexCoordinateAmplitudeSq_real_smul, Real.sq_sqrt (by
      unfold integerWaveViscousMultiplier
      exact mul_nonneg (sq_nonneg _) (integerWaveNormSq_nonneg wave))]
  unfold integerWaveViscousMultiplier
  ring

include transverse gradient in
theorem work_sq_le : value field ^ 2 ≤
    3 * (2 * Real.pi) ^ 2 * wholeStateVorticityGradientMass field *
      wholeStateVorticityNonlinearNegativeOneMass field := by
  have bound := CoefficientWork.abs_le (gradientState field gradient) (weightedNonlinear field transverse gradient)
  have same : value field = CoefficientWork.value (gradientState field gradient)
      (weightedNonlinear field transverse gradient) :=
    tsum_congr (row_eq_weighted field transverse gradient)
  rw [← same, gradientState_mass field gradient] at bound
  have massNonneg (state : ComplexVorticityHilbertState) : 0 ≤ wholeVorticityEuclideanMass state :=
    tsum_nonneg fun wave => sq_nonneg (vorticityRowAmplitude state wave)
  have gradientNonneg : 0 ≤ (2 * Real.pi) ^ 2 * wholeStateVorticityGradientMass field := by
    rw [← gradientState_mass field gradient]
    exact massNonneg _
  have squared := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).2 bound
  rw [sq_abs, mul_pow, Real.sq_sqrt gradientNonneg, Real.sq_sqrt (massNonneg _)] at squared
  have nonlinearMass := wholeVorticityEuclideanMass_le_three_mul_norm_sq (weightedNonlinear field transverse gradient)
  rw [weightedNonlinear, wholeStateVorticityNonlinearNegativeOneState_norm_sq] at nonlinearMass
  have upper := mul_le_mul_of_nonneg_left nonlinearMass gradientNonneg
  nlinarith [squared.trans upper]

def cubicCoefficient (nu : Viscosity) : Real :=
  18 * (1557504 * biotSavartSerrinConstant ^ 2) / (nu.coeff ^ 3 * (2 * Real.pi) ^ 2)

include gradient in
theorem mass_le_gradient (zeroRow : field 0 = 0) :
    wholeVorticityEuclideanMass field ≤ wholeStateVorticityGradientMass field := by
  apply (summable_vorticityRowAmplitude_sq field).tsum_le_tsum _ gradient
  intro wave
  rw [vorticityRowAmplitude_sq]
  change complexCoordinateAmplitudeSq (field wave) ≤ integerWaveNormSq wave * complexCoordinateAmplitudeSq (field wave)
  by_cases zero : wave = 0
  · subst wave
    simp [zeroRow, complexCoordinateAmplitudeSq]
  · simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (one_le_integerWaveNormSq ⟨wave, zero⟩) (complexCoordinateAmplitudeSq_nonneg (field wave))

include transverse gradient in
/-- The original whole nonlinear self-work consumes one viscous half and
leaves a cubic error-mass cost, with no finite-output or trajectory input. -/
theorem sub_viscous_le_cubic (nu : Viscosity) :
    2 * value field - 2 * nu.coeff * (2 * Real.pi) ^ 2 * wholeStateVorticityGradientMass field ≤
      -nu.coeff * (2 * Real.pi) ^ 2 * wholeStateVorticityGradientMass field +
        cubicCoefficient nu * wholeVorticityEuclideanMass field ^ 3 := by
  let M := wholeVorticityEuclideanMass field
  let D := wholeStateVorticityGradientMass field
  let N := wholeStateVorticityNonlinearNegativeOneMass field
  let K := (1557504 : Real) * biotSavartSerrinConstant ^ 2
  let L := (2 * Real.pi) ^ 2
  have nuPos := nu.coeff_pos
  have Mnonneg : 0 ≤ M := tsum_nonneg fun wave => sq_nonneg (vorticityRowAmplitude field wave)
  have Dnonneg : 0 ≤ D := tsum_nonneg fun wave =>
    mul_nonneg (integerWaveNormSq_nonneg wave) (complexCoordinateAmplitudeSq_nonneg _)
  have Nnonneg : 0 ≤ N := tsum_nonneg (wholeStateVorticityNonlinearNegativeOneDensity_nonneg field)
  have Knonneg : 0 ≤ K := by dsimp [K]; positivity
  have Lpos : 0 < L := by dsimp [L]; positivity
  have selfBound : |value field| ^ 2 ≤ (L * D) * (3 * N) := by
    rw [sq_abs]
    nlinarith [work_sq_le field transverse gradient]
  have first := CoefficientWork.square_le_product_split (abs_nonneg (value field)) (mul_nonneg Lpos.le Dnonneg)
    (by positivity : 0 ≤ 3 * N) (show 0 < nu.coeff / 4 by positivity) selfBound
  have nonlinearBound : N ^ 2 ≤ D * (K * M ^ 3) := by
    nlinarith [wholeStateVorticityNonlinearNegativeOneMass_sq_le_scaleCritical field transverse gradient]
  have second := CoefficientWork.square_le_product_split Nnonneg Dnonneg (by positivity : 0 ≤ K * M ^ 3)
    (show 0 < nu.coeff ^ 2 * L / 12 by positivity) nonlinearBound
  have factorNonneg : 0 ≤ 6 / nu.coeff := by positivity
  calc
    _ ≤ 2 * |value field| - 2 * nu.coeff * L * D := by
      dsimp [D, L]
      linarith [le_abs_self (value field)]
    _ ≤ 2 * (nu.coeff / 4 * (L * D) + 3 * N / (4 * (nu.coeff / 4))) -
        2 * nu.coeff * L * D := by linarith
    _ = (nu.coeff / 2) * (L * D) + (6 / nu.coeff) * N - 2 * nu.coeff * L * D := by
      field_simp
      ring
    _ ≤ (nu.coeff / 2) * (L * D) + (6 / nu.coeff) *
        (nu.coeff ^ 2 * L / 12 * D + K * M ^ 3 / (4 * (nu.coeff ^ 2 * L / 12))) -
        2 * nu.coeff * L * D := by gcongr
    _ = _ := by
      change _ = -nu.coeff * L * D + (18 * K / (nu.coeff ^ 3 * L)) * M ^ 3
      field_simp [ne_of_gt nu.coeff_pos, ne_of_gt Lpos]
      ring

end
end SaturationMonoid.NavierStokes.NonlinearWork
