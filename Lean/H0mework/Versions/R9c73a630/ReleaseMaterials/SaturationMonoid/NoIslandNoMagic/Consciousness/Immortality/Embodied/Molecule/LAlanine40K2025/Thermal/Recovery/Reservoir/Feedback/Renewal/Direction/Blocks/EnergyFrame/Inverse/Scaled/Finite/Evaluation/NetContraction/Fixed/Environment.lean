import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.Phase

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Powered.Dynamics
open scoped Matrix BigOperators

theorem scalar_power_real (r : ℚ) (n : Nat) : (Scalar.power (r,0) n).2=0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [Scalar.power,Scalar.multiply,ih]

theorem scalar_polynomial_real (r : ℚ) (n : Nat) : (Scalar.polynomial (r,0) n).2=0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [Scalar.polynomial,ih,scalar_power_real]

def environmentWeight : ℚ := (Scalar.polynomial (-1/64,0) 14).1^128

def environmentQ : MatrixQ (Fin 2) (Fin 2) :=
  diagonalQ ![((1+environmentWeight)⁻¹,0),(environmentWeight/(1+environmentWeight),0)]

theorem environment_numerator_exact : Prepared.environmentNumerator=
    Matrix.diagonal ![(1 : ℂ),(environmentWeight : ℂ)] := by
  have seed : (1/128 : ℝ) • (-controllerHamiltonian 2)=Matrix.diagonal ![(0 : ℂ),-1/64] := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [controllerHamiltonian,Matrix.diagonal_apply,Matrix.smul_apply,Matrix.neg_apply,Complex.real_smul]
  have atZero : Scalar.complexPolynomial (0 : ℂ) 14=1 := by
    norm_num [Scalar.complexPolynomial,Finset.sum_range_succ]
  have atTwo : Scalar.complexPolynomial (-1/64 : ℂ) 14=((Scalar.polynomial (-1/64,0) 14).1 : ℂ) := by
    have paid := Scalar.value_polynomial (-1/64,0) 14
    rw [Scalar.value,scalar_polynomial_real] at paid
    norm_num [Scalar.value] at paid
    simpa only [neg_div] using paid.symm
  rw [Prepared.environmentNumerator,seed,Diagonal.matrix_polynomial_diagonal,Matrix.diagonal_pow]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [atZero,atTwo,environmentWeight]

theorem environmentQ_value : qvalue environmentQ=Prepared.finiteEnvironment := by
  rw [environmentQ,diagonalQ_value,Prepared.finiteEnvironment,environment_numerator_exact]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.trace_diagonal,Fin.sum_univ_two,Matrix.smul_apply,Scalar.value,smul_eq_mul]
  ring

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
