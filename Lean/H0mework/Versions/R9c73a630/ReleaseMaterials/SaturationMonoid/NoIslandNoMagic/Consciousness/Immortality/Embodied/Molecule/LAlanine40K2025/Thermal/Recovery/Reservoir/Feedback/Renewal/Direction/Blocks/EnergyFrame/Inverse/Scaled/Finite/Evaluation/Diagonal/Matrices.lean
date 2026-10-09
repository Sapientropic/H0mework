import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Diagonal.Certificate

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Diagonal
open Propagation.Interface
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

theorem matrix_polynomial_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (f : ι → ℂ) (n : ℕ) : Phase.polynomial (Matrix.diagonal f) n=
      Matrix.diagonal (fun i => Scalar.complexPolynomial (f i) n) := by
  ext i j
  by_cases same : i=j
  · subst j
    simp only [Phase.polynomial,Matrix.sum_apply,Matrix.smul_apply,Matrix.diagonal_pow,Matrix.diagonal_apply,ite_true,
      Pi.pow_apply,smul_eq_mul,Scalar.complexPolynomial]
  · simp only [Phase.polynomial,Matrix.sum_apply,Matrix.smul_apply,Matrix.diagonal_pow,Matrix.diagonal_apply,if_neg same,
      smul_zero,Finset.sum_const_zero]

theorem active_matrix_seed : (Input.systemTime/1024) • (-Complex.I • E)=Matrix.diagonal (fun i => Scalar.value (activeSeed i)) := by
  ext i j
  by_cases same : i=j
  · subst j
    simpa only [Matrix.smul_apply,Matrix.diagonal_apply,ite_true,smul_eq_mul] using (active_seed_original i).symm
  · simp [E,Matrix.smul_apply,same]

theorem gibbs_matrix_seed : (1/128 : ℝ) • (-E)=Matrix.diagonal (fun i => Scalar.value (gibbsSeed i)) := by
  ext i j
  by_cases same : i=j
  · subst j
    simpa only [Matrix.smul_apply,Matrix.neg_apply,Matrix.diagonal_apply,ite_true] using (gibbs_seed_original i).symm
  · simp [E,Matrix.smul_apply,same]

theorem active_initial_matrix : Phase.flowPolynomial E (Input.systemTime/1024)=Matrix.diagonal activeInitial := by
  rw [Phase.flowPolynomial,active_matrix_seed,matrix_polynomial_diagonal]
  congr 1
  funext i
  exact (Scalar.value_polynomial (activeSeed i) 14).symm

theorem original_active_matrix : Input.activePolynomial=Matrix.diagonal (fun i => (activeInitial i)^1024) := by
  rw [Input.activePolynomial,Phase.longFlowPolynomial,active_initial_matrix,Matrix.diagonal_pow]
  rfl

theorem original_gibbs_numerator : Input.gibbsNumeratorPolynomial=Matrix.diagonal (fun i => (gibbsInitial i)^128) := by
  rw [Input.gibbsNumeratorPolynomial,gibbs_matrix_seed,matrix_polynomial_diagonal,Matrix.diagonal_pow]
  apply congrArg Matrix.diagonal
  funext i
  exact congrArg (fun z : ℂ => z^128) (Scalar.value_polynomial (gibbsSeed i) 14).symm

theorem diagonal_distance {ι : Type*} [Fintype ι] [DecidableEq ι] (a b : ι → ℂ) (d : ℝ)
    (nonnegative : 0 ≤ d) (paid : ∀ i, ‖a i-b i‖ ≤ d) : ‖Matrix.diagonal a-Matrix.diagonal b‖ ≤ d := by
  rw [Matrix.diagonal_sub,Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg nonnegative).mpr paid

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Diagonal
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
