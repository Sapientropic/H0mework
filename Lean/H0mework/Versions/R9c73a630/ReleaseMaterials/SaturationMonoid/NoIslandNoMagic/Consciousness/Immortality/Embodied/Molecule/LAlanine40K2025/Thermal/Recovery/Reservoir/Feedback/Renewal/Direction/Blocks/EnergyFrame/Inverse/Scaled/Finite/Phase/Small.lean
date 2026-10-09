import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Phase.Polynomial

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Phase
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem small_power_error (A B : Matrix ι ι ℂ) (r d : ℝ) (rpos : 0 ≤ r) (dpos : 0 ≤ d)
    (normA : ‖A‖ ≤ r) (normB : ‖B‖ ≤ r) (distance : ‖A-B‖ ≤ d) (n : ℕ) :
    ‖A^(n+1)-B^(n+1)‖ ≤ ((n+1 : ℕ) : ℝ)*d*r^n := by
  induction n with
  | zero => simpa using distance
  | succ n previous =>
    have split : A^(n+1+1)-B^(n+1+1)=A^(n+1)*(A-B)+(A^(n+1)-B^(n+1))*B := by
      rw [pow_succ _ (n+1),pow_succ _ (n+1)]
      noncomm_ring
    have power : ‖A^(n+1)‖ ≤ r^(n+1) := (norm_pow_le A _).trans (pow_le_pow_left₀ (norm_nonneg A) normA _)
    rw [split]
    calc
      _ ≤ ‖A^(n+1)*(A-B)‖+‖(A^(n+1)-B^(n+1))*B‖ := norm_add_le _ _
      _ ≤ ‖A^(n+1)‖*‖A-B‖+‖A^(n+1)-B^(n+1)‖*‖B‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ r^(n+1)*d+(((n+1 : ℕ) : ℝ)*d*r^n)*r := by gcongr
      _ = _ := by push_cast; rw [pow_succ]; ring

theorem small_exponential_error (A B : Matrix ι ι ℂ) (r d : ℝ) (rpos : 0 ≤ r) (small : r < 1)
    (dpos : 0 ≤ d) (normA : ‖A‖ ≤ r) (normB : ‖B‖ ≤ r) (distance : ‖A-B‖ ≤ d) :
    ‖NormedSpace.exp A-NormedSpace.exp B‖ ≤ d/(1-r)^2 := by
  have full := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) A).sub
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) B)
  have shifted := (hasSum_nat_add_iff' 1).mpr full
  have series : HasSum (fun n : ℕ => (((n+1).factorial : ℂ)⁻¹) • (A^(n+1)-B^(n+1)))
      (NormedSpace.exp A-NormedSpace.exp B) := by
    simpa only [Finset.range_one,Finset.sum_singleton,pow_zero,smul_sub,sub_self,sub_zero] using shifted
  have geometry : HasSum (fun n : ℕ => ((n+1 : ℕ) : ℝ)*r^n) (1/(1-r)^2) := by
    simpa only [Nat.choose_one_right] using hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 1 (by rwa [Real.norm_eq_abs,abs_of_nonneg rpos])
  have bound (n : ℕ) : ‖(((n+1).factorial : ℂ)⁻¹) • (A^(n+1)-B^(n+1))‖ ≤ d*(((n+1 : ℕ) : ℝ)*r^n) := by
    rw [norm_smul,norm_inv,Complex.norm_natCast]
    have coefficient : ((n+1).factorial : ℝ)⁻¹ ≤ 1 := by
      apply inv_le_one_of_one_le₀
      exact_mod_cast (Nat.succ_le_of_lt (Nat.factorial_pos (n+1)))
    calc
      _ ≤ 1*(((n+1 : ℕ) : ℝ)*d*r^n) := mul_le_mul coefficient (small_power_error A B r d rpos dpos normA normB distance n) (norm_nonneg _) (by norm_num)
      _ = _ := by ring
  have paid := tsum_of_norm_bounded (geometry.mul_left d) bound
  rw [series.tsum_eq] at paid
  simpa only [div_eq_mul_inv,one_mul] using paid

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Phase
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
