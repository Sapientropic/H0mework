import H0mework.Versions.R9c73a630.ThirdParty.Physlib.QuantumInfo.Entropy.DPI
import H0mework.Versions.R9c73a630.ThirdParty.Physlib.QuantumInfo.States.Entanglement

set_option autoImplicit false

namespace PhyslibCoherence

open scoped ComplexOrder RealInnerProductSpace Matrix

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Born distribution in the coordinate basis of a matrix state. -/
def diagonalDist (ρ : MState ι) : ProbDistribution ι :=
  ProbDistribution.mk' (fun i => (ρ.m i i).re)
    (fun i => (Complex.nonneg_iff.mp (ρ.psd.diag_nonneg (i := i))).1)
    (by
      have h := congrArg Complex.re ρ.tr'
      simpa only [Matrix.trace, Matrix.diag, Complex.re_sum, Complex.one_re] using h)

/-- Erase off-diagonal entries in the fixed coordinate frame. -/
def diagonalState (ρ : MState ι) : MState ι :=
  MState.ofClassical (diagonalDist ρ)

theorem diagonalDist_apply (ρ : MState ι) (i : ι) :
    ((diagonalDist ρ i : Prob) : ℝ) = (ρ.m i i).re := rfl

theorem diagonalState_matrix (ρ : MState ι) (i j : ι) :
    (diagonalState ρ).m i j = if i = j then ((ρ.m i i).re : ℂ) else 0 := by
  simp [diagonalState, MState.m, MState.ofClassical, HermitianMat.diagonal,
    diagonalDist, ProbDistribution.mk', Matrix.diagonal_apply]

theorem column_zero_of_diagonal_zero (ρ : MState ι) (j : ι)
    (hj : (ρ.m j j).re = 0) (i : ι) : ρ.m i j = 0 := by
  have hjc : ρ.m j j = 0 := by
    have hreal := Complex.nonneg_iff.mp (ρ.psd.diag_nonneg (i := j))
    apply Complex.ext
    · simpa using hj
    · simpa using hreal.2.symm
  let e : ι → ℂ := Pi.single j 1
  have hdot : star e ⬝ᵥ (ρ.m *ᵥ e) = 0 := by
    simpa [e, Matrix.mulVec_single] using hjc
  have he := (ρ.psd.dotProduct_mulVec_zero_iff e).mp hdot
  have hi := congrFun he i
  simpa [e, Matrix.mulVec_single] using hi

theorem diagonalState_m (ρ : MState ι) :
    (diagonalState ρ).m = Matrix.diagonal (fun i => ((ρ.m i i).re : ℂ)) := by
  ext i j
  simpa only [Matrix.diagonal_apply] using diagonalState_matrix ρ i j

theorem diagonalState_ker_le (ρ : MState ι) :
    (diagonalState ρ).M.ker ≤ ρ.M.ker := by
  intro v hv
  apply (HermitianMat.mem_ker_iff_mulVec_zero ρ.M v).mpr
  have hvdiag := (HermitianMat.mem_ker_iff_mulVec_zero (diagonalState ρ).M v).mp hv
  ext i
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_eq_zero
  intro j _
  by_cases hdiag : (ρ.m j j).re = 0
  · change ρ.m i j * (WithLp.ofLp v) j = 0
    rw [column_zero_of_diagonal_zero ρ j hdiag i]
    simp
  · have hcoord := congrFun hvdiag j
    change ((diagonalState ρ).m *ᵥ (WithLp.ofLp v)) j = 0 at hcoord
    rw [diagonalState_m, Matrix.mulVec_diagonal] at hcoord
    have hnonzero : (((ρ.m j j).re : ℂ)) ≠ 0 := by exact_mod_cast hdiag
    have hvj : v j = 0 := (mul_eq_zero.mp hcoord).resolve_left hnonzero
    simp [hvj]

theorem diagonalState_M (ρ : MState ι) :
    (diagonalState ρ).M = HermitianMat.diagonal ℂ (fun i => (ρ.m i i).re) := by
  ext1
  exact diagonalState_m ρ

theorem inner_diagonal_eq (A : HermitianMat ι ℂ) (d : ι → ℝ) :
    ⟪A, HermitianMat.diagonal ℂ d⟫ = ∑ i, (A.mat i i).re * d i := by
  rw [HermitianMat.inner_eq_re_trace]
  simp [Matrix.trace, Matrix.mul_diagonal, HermitianMat.diagonal]

theorem diagonalState_log (ρ : MState ι) :
    (diagonalState ρ).M.log =
      HermitianMat.diagonal ℂ (fun i => Real.log (ρ.m i i).re) := by
  rw [diagonalState_M, HermitianMat.log, HermitianMat.cfc_diagonal]
  rfl

theorem inner_diagonalState_log (ρ : MState ι) :
    ⟪ρ.M, (diagonalState ρ).M.log⟫ =
      ⟪(diagonalState ρ).M, (diagonalState ρ).M.log⟫ := by
  rw [diagonalState_log, inner_diagonal_eq, inner_diagonal_eq]
  apply Finset.sum_congr rfl
  intro i _
  change (ρ.m i i).re * Real.log (ρ.m i i).re =
    ((diagonalState ρ).m i i).re * Real.log (ρ.m i i).re
  rw [diagonalState_matrix]
  simp

theorem mixedState_M (ρ₀ ρ₁ : MState ι) (p : Prob) :
    (p [ρ₀ ↔ ρ₁]).M = (p : ℝ) • ρ₀.M + (1 - (p : ℝ)) • ρ₁.M := by
  simp [Mixable.mix, Mixable.mix_ab, MState.instMixable]
  rfl

theorem mixedState_matrix (ρ₀ ρ₁ : MState ι) (p : Prob) (i j : ι) :
    (p [ρ₀ ↔ ρ₁]).m i j =
      ((p : ℝ) : ℂ) * ρ₀.m i j + ((1 - (p : ℝ) : ℝ) : ℂ) * ρ₁.m i j := by
  have h := congrArg (HermitianMat.mat : HermitianMat ι ℂ → Matrix ι ι ℂ)
    (mixedState_M ρ₀ ρ₁ p)
  rw [HermitianMat.mat_add, HermitianMat.mat_smul, HermitianMat.mat_smul] at h
  have hij := congrArg (fun A : Matrix ι ι ℂ => A i j) h
  simpa only [MState.m, Matrix.add_apply, Matrix.smul_apply, Complex.real_smul] using hij

theorem diagonalState_mix (ρ₀ ρ₁ : MState ι) (p : Prob) :
    diagonalState (p [ρ₀ ↔ ρ₁]) = p [diagonalState ρ₀ ↔ diagonalState ρ₁] := by
  apply MState.ext_m
  ext i j
  simp only [diagonalState_matrix, mixedState_matrix]
  by_cases hij : i = j
  · subst j
    simp only [ite_true, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im]
    push_cast
    ring
  · simp [hij]

/-- Relative-entropy coherence is convex along any affine, fixed-frame dephasing map. -/
theorem qRelativeCoherence_mix_le
    (dephase : MState ι → MState ι)
    (hdephase : ∀ (ρ₀ ρ₁ : MState ι) (p : Prob),
      dephase (p [ρ₀ ↔ ρ₁]) = p [dephase ρ₀ ↔ dephase ρ₁])
    (ρ₀ ρ₁ : MState ι) (p : Prob) :
    𝐃(p [ρ₀ ↔ ρ₁]‖dephase (p [ρ₀ ↔ ρ₁])) ≤
      p * 𝐃(ρ₀‖dephase ρ₀) + (1 - p) * 𝐃(ρ₁‖dephase ρ₁) := by
  rw [hdephase]
  exact qRelativeEnt_joint_convexity ρ₀ ρ₁ (dephase ρ₀) (dephase ρ₁) p

/-- PSD boundary included: the relative entropy to the fixed-frame diagonal state is convex. -/
theorem qRelativeCoherence_diagonal_mix_le (ρ₀ ρ₁ : MState ι) (p : Prob) :
    𝐃(p [ρ₀ ↔ ρ₁]‖diagonalState (p [ρ₀ ↔ ρ₁])) ≤
      p * 𝐃(ρ₀‖diagonalState ρ₀) +
      (1 - p) * 𝐃(ρ₁‖diagonalState ρ₁) :=
  qRelativeCoherence_mix_le diagonalState diagonalState_mix ρ₀ ρ₁ p

theorem qRelativeEnt_diagonal_toReal (ρ : MState ι) :
    (𝐃(ρ‖diagonalState ρ)).toReal =
      Sᵥₙ (diagonalState ρ) - Sᵥₙ ρ := by
  have hker := diagonalState_ker_le ρ
  have hinner := inner_diagonalState_log ρ
  have hreal : ⟪ρ.M, ρ.M.log - (diagonalState ρ).M.log⟫ =
      Sᵥₙ (diagonalState ρ) - Sᵥₙ ρ := by
    simp only [inner_sub_right, Sᵥₙ_eq_neg_trace_log]
    rw [real_inner_comm (diagonalState ρ).M (diagonalState ρ).M.log,
      real_inner_comm ρ.M ρ.M.log]
    rw [← hinner]
    ring
  have h : (𝐃(ρ‖diagonalState ρ)).toEReal =
      ((Sᵥₙ (diagonalState ρ) - Sᵥₙ ρ : ℝ) : EReal) := by
    rw [qRelativeEnt_ker hker]
    exact congrArg (fun x : ℝ => (x : EReal)) hreal
  have ht := congrArg EReal.toReal h
  simpa only [EReal.toReal_coe_ennreal, EReal.toReal_coe] using ht

theorem qRelativeEnt_diagonal_toReal_classical (ρ : MState ι) :
    (𝐃(ρ‖diagonalState ρ)).toReal = Hₛ (diagonalDist ρ) - Sᵥₙ ρ := by
  rw [qRelativeEnt_diagonal_toReal]
  simp [diagonalState, Sᵥₙ_ofClassical]

theorem realCoherence_mix_le (ρ₀ ρ₁ : MState ι) (p : Prob) :
    Hₛ (diagonalDist (p [ρ₀ ↔ ρ₁])) - Sᵥₙ (p [ρ₀ ↔ ρ₁]) ≤
      (p : ℝ) * (Hₛ (diagonalDist ρ₀) - Sᵥₙ ρ₀) +
      (1 - (p : ℝ)) * (Hₛ (diagonalDist ρ₁) - Sᵥₙ ρ₁) := by
  have h := qRelativeCoherence_diagonal_mix_le ρ₀ ρ₁ p
  have h₀ : 𝐃(ρ₀‖diagonalState ρ₀) ≠ ⊤ :=
    qRelativeEnt_ne_top_iff.mpr (diagonalState_ker_le ρ₀)
  have h₁ : 𝐃(ρ₁‖diagonalState ρ₁) ≠ ⊤ :=
    qRelativeEnt_ne_top_iff.mpr (diagonalState_ker_le ρ₁)
  have hp : (((p : NNReal) : ENNReal)) ≠ ⊤ := by simp
  have h1p : (1 - (((p : NNReal) : ENNReal))) ≠ ⊤ := by simp
  have ht₀ : (((p : NNReal) : ENNReal) * 𝐃(ρ₀‖diagonalState ρ₀)) ≠ ⊤ :=
    ENNReal.mul_ne_top hp h₀
  have ht₁ : ((1 - (((p : NNReal) : ENNReal))) * 𝐃(ρ₁‖diagonalState ρ₁)) ≠ ⊤ :=
    ENNReal.mul_ne_top h1p h₁
  have hrhs : (((p : NNReal) : ENNReal) * 𝐃(ρ₀‖diagonalState ρ₀) +
      (1 - (((p : NNReal) : ENNReal))) * 𝐃(ρ₁‖diagonalState ρ₁)) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ht₀, ht₁⟩
  have hreal := ENNReal.toReal_mono hrhs h
  rw [ENNReal.toReal_add ht₀ ht₁, ENNReal.toReal_mul,
      ENNReal.toReal_mul] at hreal
  rw [qRelativeEnt_diagonal_toReal_classical,
      qRelativeEnt_diagonal_toReal_classical,
      qRelativeEnt_diagonal_toReal_classical] at hreal
  have hpcoeff : ((((p : NNReal) : ENNReal)).toReal) = (p : ℝ) := by rfl
  have hcoeff : (1 - (((p : NNReal) : ENNReal))).toReal = 1 - (p : ℝ) := by
    rw [ENNReal.toReal_sub_of_le (by exact_mod_cast p.coe_le_one) (by simp)]
    rw [hpcoeff]
    norm_num
  rw [hpcoeff, hcoeff] at hreal
  simpa using hreal

end
end PhyslibCoherence
