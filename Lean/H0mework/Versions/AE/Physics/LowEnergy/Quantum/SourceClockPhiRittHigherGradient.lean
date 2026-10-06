import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockPhiRittSecondGradient

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
namespace LowEnergy.PositiveContractionRitt
open Filter
open scoped Topology InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Falling third jet of Q^(n+1); the coefficient kills both saturated low exponents. -/
def thirdGradient (Q : Op (E := E)) (n : ℕ) : Op (E := E) :=
  ((n:ℝ)*(n+1:ℝ)*((n:ℝ)-1)) • (Q^(n-2)*(1-Q)^3)
/-- Falling fourth jet of Q^(n+1); n=0,1,2 all give the zero operator. -/
def fourthGradient (Q : Op (E := E)) (n : ℕ) : Op (E := E) :=
  ((n:ℝ)*(n+1:ℝ)*((n:ℝ)-1)*((n:ℝ)-2)) • (Q^(n-3)*(1-Q)^4)

private def thirdRatio(k:ℕ):ℝ:=((k+1:ℝ)*(k+2:ℝ)*(k+3:ℝ))/
  (((k/2+1:ℕ):ℝ)*((k/2+2:ℕ):ℝ)*((k-k/2+1:ℕ):ℝ))
private def fourthRatio(k:ℕ):ℝ:=((k+1:ℝ)*(k+2:ℝ)*(k+3:ℝ)*(k+4:ℝ))/
  (((k/2+1:ℕ):ℝ)*((k/2+2:ℕ):ℝ)*((k-k/2+1:ℕ):ℝ)*((k-k/2+2:ℕ):ℝ))
private theorem third_ratio_nonnegative(k:ℕ):0 ≤ thirdRatio k := by
  unfold thirdRatio
  positivity
private theorem fourth_ratio_nonnegative(k:ℕ):0 ≤ fourthRatio k := by
  unfold fourthRatio
  positivity
private theorem third_ratio_bound(k:ℕ):thirdRatio k ≤ 8 := by
  have ha0:0 ≤ ((k/2:ℕ):ℝ):=Nat.cast_nonneg _
  have hA:0<((k/2+1:ℕ):ℝ):=by exact_mod_cast Nat.zero_lt_succ (k/2)
  have hA2:0<((k/2+2:ℕ):ℝ):=by positivity
  have hB:0<((k-k/2+1:ℕ):ℝ):=by exact_mod_cast Nat.zero_lt_succ (k-k/2)
  unfold thirdRatio
  apply (div_le_iff₀ (mul_pos (mul_pos hA hA2) hB)).mpr
  have hb:k-k/2=k/2 ∨ k-k/2=k/2+1:=by omega
  rcases hb with hb | hb
  · have he:k=2*(k/2):=by omega
    have heR:(k:ℝ)=2*((k/2:ℕ):ℝ):=by exact_mod_cast he
    have hbR:((k-k/2:ℕ):ℝ)=((k/2:ℕ):ℝ):=by exact_mod_cast hb
    push_cast
    rw [heR,hbR]
    nlinarith only [sq_nonneg ((k/2:ℕ):ℝ),ha0]
  · have he:k=2*(k/2)+1:=by omega
    have heR:(k:ℝ)=2*((k/2:ℕ):ℝ)+1:=by exact_mod_cast he
    have hbR:((k-k/2:ℕ):ℝ)=((k/2:ℕ):ℝ)+1:=by exact_mod_cast hb
    push_cast
    rw [heR,hbR]
    nlinarith only [sq_nonneg ((k/2:ℕ):ℝ),ha0]
private theorem fourth_ratio_bound(k:ℕ):fourthRatio k ≤ 16 := by
  have ha0:0 ≤ ((k/2:ℕ):ℝ):=Nat.cast_nonneg _
  have hA:0<((k/2+1:ℕ):ℝ):=by exact_mod_cast Nat.zero_lt_succ (k/2)
  have hA2:0<((k/2+2:ℕ):ℝ):=by positivity
  have hB:0<((k-k/2+1:ℕ):ℝ):=by exact_mod_cast Nat.zero_lt_succ (k-k/2)
  have hB2:0<((k-k/2+2:ℕ):ℝ):=by positivity
  have hcube:0 ≤ ((k/2:ℕ):ℝ)^3:=by positivity
  unfold fourthRatio
  apply (div_le_iff₀ (mul_pos (mul_pos (mul_pos hA hA2) hB) hB2)).mpr
  have hb:k-k/2=k/2 ∨ k-k/2=k/2+1:=by omega
  rcases hb with hb | hb
  · have he:k=2*(k/2):=by omega
    have heR:(k:ℝ)=2*((k/2:ℕ):ℝ):=by exact_mod_cast he
    have hbR:((k-k/2:ℕ):ℝ)=((k/2:ℕ):ℝ):=by exact_mod_cast hb
    push_cast
    rw [heR,hbR]
    nlinarith only [sq_nonneg ((k/2:ℕ):ℝ),ha0,hcube]
  · have he:k=2*(k/2)+1:=by omega
    have heR:(k:ℝ)=2*((k/2:ℕ):ℝ)+1:=by exact_mod_cast he
    have hbR:((k-k/2:ℕ):ℝ)=((k/2:ℕ):ℝ)+1:=by exact_mod_cast hb
    push_cast
    rw [heR,hbR]
    nlinarith only [sq_nonneg ((k/2:ℕ):ℝ),ha0,hcube]

omit [CompleteSpace E] in
private theorem jet_product(Q:Op (E:=E))(a b p q:ℕ):
    (Q^a*(1-Q)^p)*(Q^b*(1-Q)^q)=Q^(a+b)*(1-Q)^(p+q) := by
  have hc:Commute Q (1-Q):=(Commute.one_right Q).sub_right (Commute.refl Q)
  calc
    _=Q^a*((1-Q)^p*Q^b)*(1-Q)^q:=by simp only [mul_assoc]
    _=Q^a*(Q^b*(1-Q)^p)*(1-Q)^q:=by rw [((hc.symm.pow_left p).pow_right b).eq]
    _=Q^a*Q^b*((1-Q)^p*(1-Q)^q):=by simp only [mul_assoc]
    _=_:=by rw [←pow_add,←pow_add]

omit [CompleteSpace E] in
private theorem third_eq_split(Q:Op (E:=E))(k:ℕ):
    thirdGradient Q (k+2)=thirdRatio k •
      (secondGradient Q (k/2+1)*gradient Q (k-k/2)) := by
  have hp:k/2+(k-k/2)=k:=Nat.add_sub_of_le (Nat.div_le_self k 2)
  have hprod:(Q^(k/2)*(1-Q)^2)*(Q^(k-k/2)*(1-Q))=Q^k*(1-Q)^3 := by
    simpa only [pow_one,Nat.reduceAdd,hp] using jet_product Q (k/2) (k-k/2) 2 1
  have hden:(((k/2:ℕ):ℝ)+1)*(((k/2:ℕ):ℝ)+2)*(((k-k/2:ℕ):ℝ)+1)≠0:=by positivity
  simp only [thirdGradient,secondGradient,gradient,thirdRatio,Nat.add_sub_cancel,
    Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,smul_mul_assoc,mul_smul_comm,smul_smul,hprod]
  congr 1
  field_simp [hden]
  ring

omit [CompleteSpace E] in
private theorem fourth_eq_split(Q:Op (E:=E))(k:ℕ):
    fourthGradient Q (k+3)=fourthRatio k •
      (secondGradient Q (k/2+1)*secondGradient Q (k-k/2+1)) := by
  have hp:k/2+(k-k/2)=k:=Nat.add_sub_of_le (Nat.div_le_self k 2)
  have hprod:(Q^(k/2)*(1-Q)^2)*(Q^(k-k/2)*(1-Q)^2)=Q^k*(1-Q)^4 := by
    simpa only [Nat.reduceAdd,hp] using jet_product Q (k/2) (k-k/2) 2 2
  have hden:(((k/2:ℕ):ℝ)+1)*(((k/2:ℕ):ℝ)+2)*
      (((k-k/2:ℕ):ℝ)+1)*(((k-k/2:ℕ):ℝ)+2)≠0:=by positivity
  simp only [fourthGradient,secondGradient,fourthRatio,Nat.add_sub_cancel,
    Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,smul_mul_assoc,mul_smul_comm,smul_smul,hprod]
  congr 1
  field_simp [hden]
  ring

theorem thirdGradient_norm(Q:Op (E:=E))(h0:0 ≤ Q)(h1:Q ≤ 1)(n:ℕ):
    ‖thirdGradient Q n‖ ≤ 32 := by
  cases n with
  | zero => norm_num [thirdGradient]
  | succ n =>
    cases n with
    | zero => norm_num [thirdGradient]
    | succ k =>
      change ‖thirdGradient Q (k+2)‖ ≤ 32
      rw [third_eq_split,norm_smul,Real.norm_eq_abs,abs_of_nonneg (third_ratio_nonnegative k)]
      have hp:‖secondGradient Q (k/2+1)*gradient Q (k-k/2)‖ ≤ 4 := by
        calc
          _ ≤ ‖secondGradient Q (k/2+1)‖*‖gradient Q (k-k/2)‖:=norm_mul_le _ _
          _ ≤ 4*1:=mul_le_mul (secondGradient_norm Q h0 h1 _) (gradient_norm Q h0 h1 _)
            (norm_nonneg _) (by norm_num)
          _=4:=by norm_num
      exact (mul_le_mul_of_nonneg_left hp (third_ratio_nonnegative k)).trans
        (by nlinarith only [third_ratio_bound k])

theorem fourthGradient_norm(Q:Op (E:=E))(h0:0 ≤ Q)(h1:Q ≤ 1)(n:ℕ):
    ‖fourthGradient Q n‖ ≤ 256 := by
  cases n with
  | zero => norm_num [fourthGradient]
  | succ n =>
    cases n with
    | zero => norm_num [fourthGradient]
    | succ n =>
      cases n with
      | zero => norm_num [fourthGradient]
      | succ k =>
        change ‖fourthGradient Q (k+3)‖ ≤ 256
        rw [fourth_eq_split,norm_smul,Real.norm_eq_abs,abs_of_nonneg (fourth_ratio_nonnegative k)]
        have hp:‖secondGradient Q (k/2+1)*secondGradient Q (k-k/2+1)‖ ≤ 16 := by
          calc
            _ ≤ ‖secondGradient Q (k/2+1)‖*‖secondGradient Q (k-k/2+1)‖:=norm_mul_le _ _
            _ ≤ 4*4:=mul_le_mul (secondGradient_norm Q h0 h1 _) (secondGradient_norm Q h0 h1 _)
              (norm_nonneg _) (by norm_num)
            _=16:=by norm_num
        exact (mul_le_mul_of_nonneg_left hp (fourth_ratio_nonnegative k)).trans
          (by nlinarith only [fourth_ratio_bound k])

theorem thirdGradient_strong(Q:Op (E:=E))(h0:0 ≤ Q)(h1:Q ≤ 1)(x:E):
    Tendsto (fun n:ℕ=>thirdGradient Q n x) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨M,hM⟩:=Metric.tendsto_atTop.1 (gradient_strong Q h0 h1 x) (ε/32) (by positivity)
  refine ⟨2*M+4,fun n hn=>?_⟩
  obtain ⟨k,rfl⟩:∃k,n=k+2:=⟨n-2,by omega⟩
  have ha:M ≤ k-k/2:=by omega
  have hsmall:‖gradient Q (k-k/2) x‖ < ε/32:=by
    simpa only [dist_zero_right] using hM (k-k/2) ha
  rw [third_eq_split,smul_apply,mul_apply_eq_comp,dist_zero_right,norm_smul,
    Real.norm_eq_abs,abs_of_nonneg (third_ratio_nonnegative k)]
  have hb:‖secondGradient Q (k/2+1) (gradient Q (k-k/2) x)‖ ≤
      4*‖gradient Q (k-k/2) x‖:=
    ((secondGradient Q (k/2+1)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (secondGradient_norm Q h0 h1 _) (norm_nonneg _))
  calc
    _ ≤ thirdRatio k*(4*‖gradient Q (k-k/2) x‖):=
      mul_le_mul_of_nonneg_left hb (third_ratio_nonnegative k)
    _ ≤ 8*(4*‖gradient Q (k-k/2) x‖):=
      mul_le_mul_of_nonneg_right (third_ratio_bound k) (by positivity)
    _ < ε:=by nlinarith only [hsmall]

theorem fourthGradient_strong(Q:Op (E:=E))(h0:0 ≤ Q)(h1:Q ≤ 1)(x:E):
    Tendsto (fun n:ℕ=>fourthGradient Q n x) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨M,hM⟩:=Metric.tendsto_atTop.1 (secondGradient_strong Q h0 h1 x) (ε/64) (by positivity)
  refine ⟨2*M+6,fun n hn=>?_⟩
  obtain ⟨k,rfl⟩:∃k,n=k+3:=⟨n-3,by omega⟩
  have ha:M ≤ k-k/2+1:=by omega
  have hsmall:‖secondGradient Q (k-k/2+1) x‖ < ε/64:=by
    simpa only [dist_zero_right] using hM (k-k/2+1) ha
  rw [fourth_eq_split,smul_apply,mul_apply_eq_comp,dist_zero_right,norm_smul,
    Real.norm_eq_abs,abs_of_nonneg (fourth_ratio_nonnegative k)]
  have hb:‖secondGradient Q (k/2+1) (secondGradient Q (k-k/2+1) x)‖ ≤
      4*‖secondGradient Q (k-k/2+1) x‖:=
    ((secondGradient Q (k/2+1)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (secondGradient_norm Q h0 h1 _) (norm_nonneg _))
  calc
    _ ≤ fourthRatio k*(4*‖secondGradient Q (k-k/2+1) x‖):=
      mul_le_mul_of_nonneg_left hb (fourth_ratio_nonnegative k)
    _ ≤ 16*(4*‖secondGradient Q (k-k/2+1) x‖):=
      mul_le_mul_of_nonneg_right (fourth_ratio_bound k) (by positivity)
    _ < ε:=by nlinarith only [hsmall]

end LowEnergy.PositiveContractionRitt
