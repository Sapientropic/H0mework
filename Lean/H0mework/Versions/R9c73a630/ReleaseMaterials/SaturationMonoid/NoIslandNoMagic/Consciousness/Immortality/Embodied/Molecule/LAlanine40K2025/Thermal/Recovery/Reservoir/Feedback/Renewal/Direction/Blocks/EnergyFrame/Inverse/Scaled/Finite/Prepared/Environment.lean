import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input.FiniteGibbs
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Phase.Free

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Prepared
open Load.Source Load.Producer.StrictThermal Powered.Dynamics Input
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def environmentNumerator : Matrix (Fin 2) (Fin 2) ℂ :=
  (Phase.polynomial ((1/128 : ℝ) • (-controllerHamiltonian 2)) 14)^128

def finiteEnvironment : Matrix (Fin 2) (Fin 2) ℂ := environmentNumerator.trace⁻¹ • environmentNumerator

theorem environment_hamiltonian_diagonal : controllerHamiltonian 2=Matrix.diagonal (fun i => (environmentEnergies i : ℂ)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [controllerHamiltonian,environmentEnergies]

theorem original_environment_gibbs : environmentState=normalizedExponential (controllerHamiltonian 2) := by
  rw [environment_hamiltonian_diagonal,diagonal_normalized_exponential]
  rfl

theorem environment_partition : (NormedSpace.exp (-controllerHamiltonian 2)).trace=(1+Real.exp (-2) : ℝ) := by
  rw [environment_hamiltonian_diagonal,diagonal_exponential,Matrix.trace_diagonal]
  norm_num [Fin.sum_univ_two,environmentEnergies]

theorem environment_numerator_error :
    ‖NormedSpace.exp (-controllerHamiltonian 2)-environmentNumerator‖ ≤ (2/10^18 : ℝ) := by
  have small : ‖(1/128 : ℝ) • (-controllerHamiltonian 2)‖ ≤ (1/64 : ℝ) := by
    rw [norm_smul,norm_neg,Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/128)]
    nlinarith [controllerHamiltonian_norm_le]
  have step : ‖NormedSpace.exp ((1/128 : ℝ) • (-controllerHamiltonian 2))-
      Phase.polynomial ((1/128 : ℝ) • (-controllerHamiltonian 2)) 14‖ ≤ (1/10^30 : ℝ) :=
    (Phase.polynomial_error _ (1/64) (by norm_num) (by norm_num) small 14).trans (by norm_num [Nat.factorial])
  have first := Phase.small_exponential_norm _ (small.trans (by norm_num))
  have second : ‖Phase.polynomial ((1/128 : ℝ) • (-controllerHamiltonian 2)) 14‖ ≤ (6/5 : ℝ) := by
    have triangle := norm_sub_le_norm_sub_add_norm_sub (Phase.polynomial ((1/128 : ℝ) • (-controllerHamiltonian 2)) 14)
      (NormedSpace.exp ((1/128 : ℝ) • (-controllerHamiltonian 2))) 0
    simp only [sub_zero] at triangle
    rw [norm_sub_rev] at step
    linarith
  have paid := Phase.power_error _ _ (6/5) (1/10^30) (by norm_num) (by norm_num) (first.trans (by norm_num)) second step 128
  rw [Phase.exponential_128_parts]
  exact paid.trans (by norm_num)

theorem original_finite_environment_error : ‖environmentState-finiteEnvironment‖ ≤ (7/10^18 : ℝ) := by
  have mass : (1 : ℝ) ≤ ‖(NormedSpace.exp (-controllerHamiltonian 2)).trace‖ := by
    rw [environment_partition]
    have nonnegative : 0 ≤ 1+Real.exp (-2) := by positivity
    simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg nonnegative]
    linarith [Real.exp_pos (-2)]
  have reference : ‖normalizedExponential (controllerHamiltonian 2)‖ ≤ 1 := by
    rw [← original_environment_gibbs]
    exact state_norm_le_one _ environmentState_positive environmentState_trace
  have reverse : ‖environmentNumerator-NormedSpace.exp (-controllerHamiltonian 2)‖ ≤ (2/10^18 : ℝ) := by
    rw [norm_sub_rev]; exact environment_numerator_error
  have paid := trace_normalization_error environmentNumerator (NormedSpace.exp (-controllerHamiltonian 2))
    1 (2/10^18) (by norm_num) (by norm_num) mass reference reverse
  rw [original_environment_gibbs,norm_sub_rev]
  exact paid.trans (by norm_num)

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Prepared
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
