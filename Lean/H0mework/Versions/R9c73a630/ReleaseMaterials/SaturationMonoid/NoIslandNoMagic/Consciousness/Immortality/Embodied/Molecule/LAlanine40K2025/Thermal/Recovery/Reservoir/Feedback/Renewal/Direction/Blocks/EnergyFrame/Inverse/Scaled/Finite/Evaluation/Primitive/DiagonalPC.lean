import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.ScalarMaterial

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive
open Propagation.Interface Propagation.Producer Load.Source
open scoped Matrix BigOperators Matrix.Norms.L2Operator

def diagonalScalarEnergy (a : Basis) (n : Fin 2) : ℚ := 2*Diagonal.energy a+1+2*n.val

theorem diagonal_scalar_original (a : Basis) : diagonalHpc (Donor.calculatedEnergy a)=
    Matrix.diagonal (fun n : Fin 2 => (diagonalScalarEnergy a n : ℂ)) := by
  have source : (Diagonal.energy a : ℂ)=(Donor.calculatedEnergy a : ℂ) := by exact_mod_cast recorded_energy_original a
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [diagonalHpc,Matrix.diagonal_apply,diagonalScalarEnergy,source]
  ring

private theorem scalar_polynomial_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι] (d : ι → ℂ) (N : Nat) :
    Phase.polynomial (Matrix.diagonal d) N=Matrix.diagonal (fun i => scalarPolynomial (d i) N) := by
  unfold Phase.polynomial scalarPolynomial
  simp only [Matrix.diagonal_pow]
  ext i j
  by_cases same : i=j
  · subst j
    simp only [Matrix.sum_apply,Matrix.smul_apply,Matrix.diagonal_apply,ite_true,smul_eq_mul,Pi.pow_apply]
  · simp only [Matrix.sum_apply,Matrix.smul_apply,Matrix.diagonal_apply,same,ite_false,smul_zero,Finset.sum_const_zero]

theorem diagonal_pc_scalar_values (a : Basis) (tick : ℚ) :
    diagonalPC a ((tick : ℝ)*(nativeClockStep : ℝ))=
      Matrix.diagonal (fun n : Fin 2 => Scalar.value (Scalar.polynomial (scalarSeed (diagonalScalarEnergy a n) tick) 14)) := by
  rw [diagonalPC,diagonal_scalar_original,Phase.flowPolynomial]
  have argument : ((tick : ℝ)*(nativeClockStep : ℝ)) • (-Complex.I • Matrix.diagonal (fun n : Fin 2 => (diagonalScalarEnergy a n : ℂ)))=
      Matrix.diagonal (fun n : Fin 2 => Scalar.value (scalarSeed (diagonalScalarEnergy a n) tick)) := by
    ext i j
    by_cases same : i=j
    · subst j
      simp only [Matrix.smul_apply,Matrix.diagonal_apply,ite_true,Complex.real_smul,smul_eq_mul,scalar_seed_original,mul_assoc]
    · simp only [Matrix.smul_apply,Matrix.diagonal_apply,same,ite_false,smul_zero]
  rw [argument,scalar_polynomial_diagonal]
  apply congrArg Matrix.diagonal
  funext n
  exact (Scalar.value_polynomial _ _).symm

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
