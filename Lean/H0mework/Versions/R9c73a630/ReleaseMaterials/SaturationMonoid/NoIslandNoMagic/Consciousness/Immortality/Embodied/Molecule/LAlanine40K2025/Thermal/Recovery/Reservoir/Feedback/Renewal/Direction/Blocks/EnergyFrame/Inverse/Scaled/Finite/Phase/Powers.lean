import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Phase.Source

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Phase
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem power_error (A B : Matrix ι ι ℂ) (M d : ℝ) (large : 1 ≤ M) (dpos : 0 ≤ d)
    (normA : ‖A‖ ≤ M) (normB : ‖B‖ ≤ M) (distance : ‖A-B‖ ≤ d) (n : ℕ) :
    ‖A^n-B^n‖ ≤ (n : ℝ)*d*M^n := by
  induction n with
  | zero => simp
  | succ n previous =>
    have split : A^(n+1)-B^(n+1)=A^n*(A-B)+(A^n-B^n)*B := by
      rw [pow_succ,pow_succ]
      noncomm_ring
    have power : ‖A^n‖ ≤ M^n := (norm_pow_le A n).trans (pow_le_pow_left₀ (norm_nonneg A) normA n)
    have inflate : M^n*d ≤ M^n*d*M := le_mul_of_one_le_right (mul_nonneg (pow_nonneg (by linarith) n) dpos) large
    rw [split]
    calc
      _ ≤ ‖A^n*(A-B)‖+‖(A^n-B^n)*B‖ := norm_add_le _ _
      _ ≤ ‖A^n‖*‖A-B‖+‖A^n-B^n‖*‖B‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ M^n*d+((n : ℝ)*d*M^n)*M := by gcongr
      _ ≤ _ := by rw [Nat.cast_succ,pow_succ]; nlinarith

set_option exponentiation.threshold 1024 in
theorem unitary_polynomial_power_error (A B : Matrix ι ι ℂ) (unitary : A ∈ Matrix.unitaryGroup ι ℂ)
    (distance : ‖A-B‖ ≤ (1/10^18 : ℝ)) :
    ‖A^1024-B^1024‖ ≤ (4/10^15 : ℝ) := by
  have normA : ‖A‖=1 := CStarRing.norm_coe_unitary (⟨A,unitary⟩ : Matrix.unitaryGroup ι ℂ)
  have normB : ‖B‖ ≤ (1001/1000 : ℝ) := by
    have triangle := norm_le_norm_add_norm_sub A B
    rw [normA] at triangle
    linarith
  have paid := power_error A B (1001/1000) (1/10^18) (by norm_num) (by norm_num)
    (by rw [normA]; norm_num) normB distance 1024
  apply paid.trans
  norm_num

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Phase
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
