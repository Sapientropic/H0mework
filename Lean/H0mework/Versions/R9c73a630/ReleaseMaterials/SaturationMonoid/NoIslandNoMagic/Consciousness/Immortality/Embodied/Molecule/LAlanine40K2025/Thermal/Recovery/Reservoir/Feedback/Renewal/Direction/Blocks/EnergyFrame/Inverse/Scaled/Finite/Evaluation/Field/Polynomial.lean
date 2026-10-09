import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Phase.Polynomial

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Field
open scoped Matrix BigOperators Matrix.Norms.L2Operator
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def realTerm (K : Matrix ι ι ℂ) (n : Nat) : Matrix ι ι ℂ := ((n.factorial : ℂ)⁻¹) • K^n

theorem realTerm_zero (K : Matrix ι ι ℂ) : realTerm K 0=1 := by simp [realTerm]

theorem realTerm_succ (K : Matrix ι ι ℂ) (n : Nat) :
    realTerm K (n+1)=((n+1 : Nat) : ℂ)⁻¹ • (K*realTerm K n) := by
  simp only [realTerm,Nat.factorial_succ,Nat.cast_mul,mul_inv_rev,pow_succ',mul_smul_comm,smul_smul]
  congr 1
  ring

def phasedSum (values : Nat → Matrix ι ι ℂ) (N : Nat) : Matrix ι ι ℂ :=
  ∑ n ∈ Finset.range N, ((-Complex.I)^n) • values n

theorem polynomial_as_phased_terms (K : Matrix ι ι ℂ) (N : Nat) :
    Phase.polynomial (-Complex.I • K) N=phasedSum (realTerm K) N := by
  apply Finset.sum_congr rfl
  intro n _
  simp only [smul_pow,realTerm,smul_smul]
  congr 1
  ring

variable [Nonempty ι]

theorem short_polynomial_truncation (Z : Matrix ι ι ℂ) (small : ‖Z‖ ≤ (1/40 : ℝ)) :
    ‖Phase.polynomial Z 14-Phase.polynomial Z 8‖ ≤ (4/10^18 : ℝ) := by
  have first := Phase.polynomial_error Z (1/40) (by norm_num) (by norm_num) small 14
  have second := Phase.polynomial_error Z (1/40) (by norm_num) (by norm_num) small 8
  have triangle := norm_sub_le_norm_sub_add_norm_sub (Phase.polynomial Z 14) (NormedSpace.exp Z) (Phase.polynomial Z 8)
  rw [norm_sub_rev (Phase.polynomial Z 14) (NormedSpace.exp Z)] at triangle
  norm_num at first second
  linarith

theorem successor_inv_norm (n : Nat) : ‖(((n+1 : Nat) : ℂ)⁻¹)‖ ≤ 1 := by
  rw [norm_inv,Complex.norm_natCast]
  exact inv_le_one_of_one_le₀ (by exact_mod_cast Nat.succ_pos n)

omit [Nonempty ι] in
theorem rounded_terms_error (K : Matrix ι ι ℂ) (values : Nat → Matrix ι ι ℂ)
    (small : ‖K‖ ≤ (1/40 : ℝ)) (initial : values 0=1)
    (step : ∀ n < 7, ‖values (n+1)-((n+1 : Nat) : ℂ)⁻¹ • (K*values n)‖ ≤ (1/10^22 : ℝ)) :
    ∀ n ≤ 7, ‖realTerm K n-values n‖ ≤ (2/10^22 : ℝ) := by
  intro n
  induction n with
  | zero => intro _; rw [realTerm_zero,initial,sub_self,norm_zero]; norm_num
  | succ n ih =>
    intro hn
    have previous := ih (by omega)
    have next := step n (by omega)
    rw [realTerm_succ]
    have triangle := norm_sub_le_norm_sub_add_norm_sub
      (((n+1 : Nat) : ℂ)⁻¹ • (K*realTerm K n))
      (((n+1 : Nat) : ℂ)⁻¹ • (K*values n)) (values (n+1))
    rw [← smul_sub,← Matrix.mul_sub,norm_smul] at triangle
    have middle : ‖(((n+1 : Nat) : ℂ)⁻¹)‖*‖K*(realTerm K n-values n)‖ ≤ (1/40 : ℝ)*(2/10^22) := by
      calc
        _ ≤ 1*(‖K‖*‖realTerm K n-values n‖) := mul_le_mul (successor_inv_norm n) (norm_mul_le _ _) (norm_nonneg _) (by norm_num)
        _ ≤ _ := by rw [one_mul]; exact mul_le_mul small previous (norm_nonneg _) (by norm_num)
    rw [norm_sub_rev (values (n+1))] at next
    linarith

omit [Nonempty ι] in
theorem rounded_phased_sum_error (K : Matrix ι ι ℂ) (values : Nat → Matrix ι ι ℂ)
    (terms : ∀ n < 8, ‖realTerm K n-values n‖ ≤ (2/10^22 : ℝ)) :
    ‖Phase.polynomial (-Complex.I • K) 8-phasedSum values 8‖ ≤ (2/10^21 : ℝ) := by
  rw [polynomial_as_phased_terms,phasedSum,phasedSum,← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ n ∈ Finset.range 8, ‖(-Complex.I)^n • realTerm K n-(-Complex.I)^n • values n‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.range 8, (2/10^22 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      rw [← smul_sub,norm_smul,norm_pow,norm_neg,Complex.norm_I,one_pow,one_mul]
      exact terms n (Finset.mem_range.mp hn)
    _ ≤ _ := by norm_num

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Field
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
