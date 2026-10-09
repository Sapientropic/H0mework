import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Dense.Representation
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Field.Values
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Field.Polynomial
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input.PhaseMatrices

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Field
open Spectral Propagation.Interface Propagation.Producer
open scoped Matrix BigOperators Matrix.Norms.L2Operator
noncomputable section

def K : Matrix Basis Basis ℂ :=
  ((clockNumerator : ℂ)/((clockDenominator : ℂ)*(fieldScale : ℂ))) • Cast.complexMatrix Dense.fieldInt

theorem K_original : K=(nativeClockStep : ℝ) • Input.rawFieldHamiltonian := by
  rw [Dense.original_field_exact]
  unfold K Dense.computedField
  rw [← smul_assoc]
  simp only [Complex.real_smul]
  congr 1
  rw [nativeClockStep_exact]
  norm_num [clockNumerator,clockDenominator,fieldScale]

theorem K_norm : ‖K‖ ≤ (1/40 : ℝ) := by
  calc
    ‖K‖=|(nativeClockStep : ℝ)| *‖Input.rawFieldHamiltonian‖ := by rw [K_original,norm_smul,Real.norm_eq_abs]
    _ ≤ |(nativeClockStep : ℝ)| *42 := mul_le_mul_of_nonneg_left Input.raw_field_norm (abs_nonneg _)
    _ ≤ _ := by rw [nativeClockStep_exact]; norm_num

theorem original_polynomial_argument : Input.fieldPolynomial=Phase.polynomial (-Complex.I • K) 14 := by
  rw [Input.fieldPolynomial,Phase.flowPolynomial,K_original,smul_comm (nativeClockStep : ℝ) (-Complex.I)]

theorem source_argument_norm : ‖-Complex.I • K‖ ≤ (1/40 : ℝ) := by
  rw [norm_smul,norm_neg,Complex.norm_I,one_mul]
  exact K_norm

theorem step_denominator_positive (n : Nat) : 0 < stepDenominator n := by
  unfold stepDenominator clockDenominator fieldScale
  positivity

theorem step_coefficient (n : Nat) :
    (((n+1 : Nat) : ℂ)⁻¹)*((clockNumerator : ℂ)/((clockDenominator : ℂ)*(fieldScale : ℂ)))=
      (clockNumerator : ℂ)/(stepDenominator n : ℂ) := by
  simp only [stepDenominator,Int.cast_mul,Int.cast_add,Int.cast_one,Int.cast_natCast,Nat.cast_add,Nat.cast_one,
    div_eq_mul_inv,mul_inv_rev]
  ring

theorem source_step_representation (n : Nat) :
    (((n+1 : Nat) : ℂ)⁻¹) • (K*termMatrix n)=
      ((clockNumerator : ℂ)/(stepDenominator n : ℂ)) •
        (Cast.complexMatrix Dense.fieldInt*((1/10^24 : ℂ) • Cast.complexMatrix (termInt n))) := by
  rw [K,termMatrix,Matrix.smul_mul,smul_smul,step_coefficient]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Field
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
