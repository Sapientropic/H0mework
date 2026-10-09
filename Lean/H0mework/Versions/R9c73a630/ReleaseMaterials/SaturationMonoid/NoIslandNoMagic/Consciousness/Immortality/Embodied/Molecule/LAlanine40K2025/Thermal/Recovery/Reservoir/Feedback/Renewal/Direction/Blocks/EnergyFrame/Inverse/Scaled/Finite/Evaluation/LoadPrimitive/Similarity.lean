import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Basis

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive
open Propagation.Interface Load.Source
open scoped Matrix BigOperators Matrix.Norms.L2Operator
noncomputable section

theorem basis_power (M : Matrix (Fin 8) (Fin 8) ℂ) (n : Nat) :
    (basis*M*inverse)^n=basis*M^n*inverse := by
  induction n with
  | zero => simp only [pow_zero,Matrix.mul_one,basis_right]
  | succ n ih =>
    rw [pow_succ,ih,pow_succ]
    calc
      _=basis*(M^n*(inverse*basis)*M)*inverse := by noncomm_ring
      _=_ := by rw [basis_left,Matrix.mul_one,Matrix.mul_assoc]

theorem basis_polynomial (M : Matrix (Fin 8) (Fin 8) ℂ) (n : Nat) :
    Phase.polynomial (basis*M*inverse) n=basis*Phase.polynomial M n*inverse := by
  simp only [Phase.polynomial,basis_power,Matrix.mul_sum,Matrix.sum_mul,Matrix.smul_mul,Matrix.mul_smul]

theorem basis_flow (M : Matrix (Fin 8) (Fin 8) ℂ) (time : ℝ) :
    Phase.flowPolynomial (basis*M*inverse) time=basis*Phase.flowPolynomial M time*inverse := by
  have argument : time • (-Complex.I • (basis*M*inverse))=basis*(time • (-Complex.I • M))*inverse := by
    simp only [Matrix.mul_smul,Matrix.smul_mul]
  rw [Phase.flowPolynomial,argument,basis_polynomial]
  rfl

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
