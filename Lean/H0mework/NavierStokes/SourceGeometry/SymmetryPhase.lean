import H0mework.NavierStokes.WholeSpace.WholeContinuousMildSerrinUniqueness
import H0mework.NavierStokes.Fourier.CoarseFilterProcess

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.SourceEvenFrequency

open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientCoarseFilterProcess

noncomputable section

def phase (wave : IntegerWavevector) : ℂ := (-1) ^ wave 0

theorem phase_norm (wave : IntegerWavevector) : ‖phase wave‖ = 1 := by
  simp [phase, norm_zpow]

theorem phase_add (p q : IntegerWavevector) : phase (p + q) = phase p * phase q := by
  simp only [phase, Pi.add_apply, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]

theorem phase_square (wave : IntegerWavevector) : phase wave * phase wave = 1 := by
  rw [phase, ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
  exact (show Even (wave 0 + wave 0) from ⟨wave 0, rfl⟩).neg_one_zpow

def shift : ComplexVorticityHilbertState →L[ℂ] ComplexVorticityHilbertState :=
  lp.mapCLM 2 (fun wave => phase wave • ContinuousLinearMap.id ℂ ComplexCoordinateVector)
    zero_le_one (fun wave => by simp [norm_smul, phase_norm])

@[simp] theorem shift_apply (field : ComplexVorticityHilbertState) (wave : IntegerWavevector) :
    shift field wave = phase wave • field wave := rfl

theorem shift_involutive (field : ComplexVorticityHilbertState) : shift (shift field) = field := by
  apply Subtype.ext
  funext wave
  simp only [shift_apply, smul_smul, phase_square, one_smul]

theorem shifted_velocity (field : ComplexVorticityHilbertState) (wave : IntegerWavevector) :
    finiteStateVelocityCoefficient (shift field) wave =
      phase wave • finiteStateVelocityCoefficient field wave := by
  simp only [finiteStateVelocityCoefficient, shift_apply, biotSavartVelocityCoefficient_smul]

theorem shifted_pair (left right : ComplexVorticityHilbertState) (p q : IntegerWavevector) :
    finiteStateVorticityBilinearPairContribution (shift left) (shift right) (p, q) =
      phase (p + q) • finiteStateVorticityBilinearPairContribution left right (p, q) := by
  unfold finiteStateVorticityBilinearPairContribution
  rw [shifted_velocity, shifted_velocity, shift_apply, shift_apply, phase_add]
  simp only [dotProduct_smul, smul_sub, smul_smul]
  congr 1 <;> congr 1 <;> ring

theorem shifted_nonlinear (left right : ComplexVorticityHilbertState) (wave : IntegerWavevector) :
    wholeStateVorticityBilinearCoefficientAt (shift left) (shift right) wave =
      phase wave • wholeStateVorticityBilinearCoefficientAt left right wave := by
  unfold wholeStateVorticityBilinearCoefficientAt
  simp only [shifted_pair, add_sub_cancel, tsum_const_smul'']

end
end SaturationMonoid.NavierStokes.SourceEvenFrequency
