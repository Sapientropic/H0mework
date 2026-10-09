import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Phase.Powers

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Phase
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def longFlowPolynomial (H : Matrix ι ι ℂ) (time : ℝ) : Matrix ι ι ℂ :=
  (flowPolynomial H (time/1024))^1024

omit [Nonempty ι] in
theorem flow_1024_parts (H : Matrix ι ι ℂ) (time : ℝ) :
    hamiltonianFlow H time=(hamiltonianFlow H (time/1024))^1024 := by
  let : NormedAlgebra ℚ (Matrix ι ι ℂ) := .restrictScalars ℚ ℂ _
  unfold hamiltonianFlow
  rw [← NormedSpace.exp_nsmul]
  congr 1
  ext i j
  simp [Matrix.smul_apply,smul_eq_mul,Complex.real_smul]
  ring

theorem long_flow_polynomial_error (H : Matrix ι ι ℂ) (hermitian : H.IsHermitian) (time : ℝ)
    (size : ‖H‖ ≤ 100) (clock : |time| ≤ 2) :
    ‖hamiltonianFlow H time-longFlowPolynomial H time‖ ≤ (4/10^15 : ℝ) := by
  have small : ‖(time/1024) • (-Complex.I • H)‖ ≤ (1/5 : ℝ) := by
    simp only [norm_smul,Real.norm_eq_abs,norm_neg,Complex.norm_I,one_mul,abs_div,abs_of_nonneg (show (0 : ℝ) ≤ 1024 by norm_num)]
    calc
      _ ≤ (2/1024 : ℝ)*100 := by gcongr
      _ ≤ _ := by norm_num
  have approximation : ‖hamiltonianFlow H (time/1024)-flowPolynomial H (time/1024)‖ ≤ (1/10^18 : ℝ) := by
    exact (polynomial_error _ (1/5) (by norm_num) (by norm_num) small 14).trans (by norm_num [Nat.factorial])
  rw [flow_1024_parts,longFlowPolynomial]
  exact unitary_polynomial_power_error _ _ (hamiltonianFlow_unitary H hermitian _) approximation

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Phase
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
