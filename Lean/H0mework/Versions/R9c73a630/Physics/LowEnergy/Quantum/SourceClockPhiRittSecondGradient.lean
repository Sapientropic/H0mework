import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceInverseVolumePositiveContractionRitt

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
namespace LowEnergy.PositiveContractionRitt
open Filter
open scoped Topology InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def secondGradient (Q : Op (E := E)) (n : ℕ) : Op (E := E) :=
  ((n : ℝ)*(n+1 : ℝ)) • (Q^(n-1)*(1-Q)^2)

private theorem split_bound (k : ℕ) :
    ((k+1 : ℝ)*(k+2 : ℝ)) /
      (((k/2+1 : ℕ):ℝ)*((k-k/2+1 : ℕ):ℝ)) ≤ 4 := by
  have hA : 0 < ((k/2+1 : ℕ):ℝ) := by exact_mod_cast Nat.zero_lt_succ (k/2)
  have hB : 0 < ((k-k/2+1 : ℕ):ℝ) := by exact_mod_cast Nat.zero_lt_succ (k-k/2)
  apply (div_le_iff₀ (mul_pos hA hB)).mpr
  have hdiv : k/2 ≤ k := Nat.div_le_self k 2
  have hb : k-k/2 = k/2 ∨ k-k/2 = k/2+1 := by omega
  rcases hb with hb | hb
  · have he : k = 2*(k/2) := by omega
    have heR : (k:ℝ) = 2*((k/2:ℕ):ℝ) := by exact_mod_cast he
    have hbR : ((k-k/2:ℕ):ℝ) = ((k/2:ℕ):ℝ) := by exact_mod_cast hb
    push_cast
    nlinarith [sq_nonneg ((k/2:ℕ):ℝ)]
  · have he : k = 2*(k/2)+1 := by omega
    have heR : (k:ℝ) = 2*((k/2:ℕ):ℝ)+1 := by exact_mod_cast he
    have hbR : ((k-k/2:ℕ):ℝ) = ((k/2:ℕ):ℝ)+1 := by exact_mod_cast hb
    push_cast
    nlinarith [sq_nonneg ((k/2:ℕ):ℝ)]

omit [CompleteSpace E] in
private theorem second_eq_split (Q : Op (E := E)) (k : ℕ) :
    secondGradient Q (k+1) =
      (((k+1 : ℝ)*(k+2 : ℝ)) /
        (((k/2+1 : ℕ):ℝ)*((k-k/2+1 : ℕ):ℝ))) •
        (gradient Q (k/2) * gradient Q (k-k/2)) := by
  have hk : k/2 ≤ k := Nat.div_le_self k 2
  have hp : (k/2)+(k-k/2)=k := Nat.add_sub_of_le hk
  have hA : 0 < ((k/2+1 : ℕ):ℝ) := by exact_mod_cast Nat.zero_lt_succ (k/2)
  have hB : 0 < ((k-k/2+1 : ℕ):ℝ) := by exact_mod_cast Nat.zero_lt_succ (k-k/2)
  have hden : (((k/2+1 : ℕ):ℝ)*((k-k/2+1 : ℕ):ℝ)) ≠ 0 := ne_of_gt (mul_pos hA hB)
  have hcomm : Commute Q (1-Q) := by
    exact (Commute.one_right Q).sub_right (Commute.refl Q)
  have hprod : (Q^(k/2)*(1-Q))*(Q^(k-k/2)*(1-Q)) = Q^k*(1-Q)^2 := by
    calc
      _ = Q^(k/2)*((1-Q)*Q^(k-k/2))*(1-Q) := by simp only [mul_assoc]
      _ = Q^(k/2)*(Q^(k-k/2)*(1-Q))*(1-Q) := by
        rw [(hcomm.symm.pow_right (k-k/2)).eq]
      _ = Q^(k/2)*Q^(k-k/2)*((1-Q)*(1-Q)) := by simp only [mul_assoc]
      _ = Q^k*(1-Q)^2 := by rw [←pow_add,hp,pow_two]
  have hden' : ((↑(k/2):ℝ)+1)*((↑(k-k/2):ℝ)+1) ≠ 0 := by
    simpa only [Nat.cast_add,Nat.cast_one] using hden
  simp only [secondGradient,gradient,Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one,
    smul_mul_assoc,mul_smul_comm,smul_smul,hprod]
  congr 1
  field_simp [hden']
  ring

theorem secondGradient_norm (Q : Op (E := E)) (h0 : 0≤Q) (h1 : Q≤1) (n : ℕ) :
    ‖secondGradient Q n‖ ≤ 4 := by
  cases n with
  | zero => simp [secondGradient]
  | succ k =>
    rw [second_eq_split]
    have hc : 0 ≤ ((k+1 : ℝ)*(k+2 : ℝ)) /
      (((k/2+1 : ℕ):ℝ)*((k-k/2+1 : ℕ):ℝ)) := by
      have hA : 0 < ((k/2+1 : ℕ):ℝ) := by exact_mod_cast Nat.zero_lt_succ (k/2)
      have hB : 0 < ((k-k/2+1 : ℕ):ℝ) := by exact_mod_cast Nat.zero_lt_succ (k-k/2)
      positivity
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
    have hg : ‖gradient Q (k/2) * gradient Q (k-k/2)‖ ≤ 1 := by
      calc
        _ ≤ ‖gradient Q (k/2)‖ * ‖gradient Q (k-k/2)‖ := norm_mul_le _ _
        _ ≤ 1 * 1 := mul_le_mul (gradient_norm Q h0 h1 _) (gradient_norm Q h0 h1 _)
            (norm_nonneg _) (by norm_num)
        _ = 1 := by norm_num
    calc
      _ ≤ (((k+1 : ℝ)*(k+2 : ℝ)) /
          (((k/2+1 : ℕ):ℝ)*((k-k/2+1 : ℕ):ℝ))) * 1 := mul_le_mul_of_nonneg_left hg hc
      _ ≤ 4 := by simpa using split_bound k

theorem secondGradient_strong (Q : Op (E := E)) (h0 : 0≤Q) (h1 : Q≤1) (x : E) :
    Tendsto (fun n : ℕ => secondGradient Q n x) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨M,hM⟩ := Metric.tendsto_atTop.1 (gradient_strong Q h0 h1 x) (ε/4) (by positivity)
  refine ⟨2*M+2,fun n hn => ?_⟩
  obtain ⟨k,rfl⟩ : ∃ k,n=k+1 := ⟨n-1,by omega⟩
  have ha : M ≤ k-k/2 := by omega
  have hsmall : ‖gradient Q (k-k/2) x‖ < ε/4 := by
    simpa only [dist_zero_right] using hM (k-k/2) ha
  rw [second_eq_split,smul_apply,mul_apply_eq_comp]
  have hc : 0 ≤ ((k+1 : ℝ)*(k+2 : ℝ)) /
      (((k/2+1 : ℕ):ℝ)*((k-k/2+1 : ℕ):ℝ)) := by
    have hA : 0 < ((k/2+1 : ℕ):ℝ) := by exact_mod_cast Nat.zero_lt_succ (k/2)
    have hB : 0 < ((k-k/2+1 : ℕ):ℝ) := by exact_mod_cast Nat.zero_lt_succ (k-k/2)
    positivity
  have hb := (gradient Q (k/2)).le_opNorm (gradient Q (k-k/2) x)
  have hg := gradient_norm Q h0 h1 (k/2)
  rw [dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_nonneg hc]
  calc
    _ ≤ (((k+1 : ℝ)*(k+2 : ℝ)) /
      (((k/2+1 : ℕ):ℝ)*((k-k/2+1 : ℕ):ℝ))) * ‖gradient Q (k-k/2) x‖ := by
        gcongr
        exact hb.trans (mul_le_of_le_one_left (norm_nonneg _) hg)
    _ ≤ 4 * ‖gradient Q (k-k/2) x‖ := mul_le_mul_of_nonneg_right (split_bound k) (norm_nonneg _)
    _ < ε := by linarith

end LowEnergy.PositiveContractionRitt
