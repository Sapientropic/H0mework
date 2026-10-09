import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Quantum.Coherence.Relative

set_option autoImplicit false

namespace PhyslibCoherence

open scoped Matrix ComplexOrder
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def branchProjector (b : Fin 2) : Matrix (ι × Fin 2) (ι × Fin 2) ℂ :=
  Matrix.diagonal (fun x => if x.2 = b then 1 else 0)

theorem branchProjector_tp :
    (∑ b : Fin 2, (branchProjector (ι := ι) b)ᴴ * branchProjector b) = 1 := by
  ext x y
  rcases x with ⟨i, a⟩
  rcases y with ⟨j, c⟩
  fin_cases a <;> fin_cases c <;>
    simp [branchProjector, Fin.sum_univ_two, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply, Matrix.one_apply,
      Prod.mk.injEq]

def blockDephase : CPTPMap (ι × Fin 2) (ι × Fin 2) ℂ :=
  CPTPMap.of_kraus_CPTPMap (branchProjector (ι := ι)) branchProjector_tp

theorem blockDephase_matrix (ρ : MState (ι × Fin 2)) (x y : ι × Fin 2) :
    (blockDephase (ι := ι) ρ).m x y = if x.2 = y.2 then ρ.m x y else 0 := by
  change (∑ b : Fin 2, (branchProjector (ι := ι) b * ρ.m *
    (branchProjector (ι := ι) b)ᴴ) x y) = _
  simp [branchProjector, Matrix.diagonal_mul,
    Matrix.mul_diagonal, Matrix.diagonal_conjTranspose]

theorem blockDephase_body (ρ : MState (ι × Fin 2)) :
    (blockDephase (ι := ι) ρ).traceRight = ρ.traceRight := by
  apply MState.ext_m
  ext i j
  change (∑ b : Fin 2, (blockDephase (ι := ι) ρ).m (i, b) (j, b)) =
    ∑ b : Fin 2, ρ.m (i, b) (j, b)
  simp only [blockDephase_matrix, ite_true]

theorem blockDephase_pointer (ρ : MState (ι × Fin 2)) (a b : Fin 2) :
    (blockDephase (ι := ι) ρ).traceLeft.m a b =
      if a = b then ρ.traceLeft.m a b else 0 := by
  change (∑ i : ι, (blockDephase (ι := ι) ρ).m (i, a) (i, b)) = _
  simp only [blockDephase_matrix]
  split_ifs with h
  · subst b
    rfl
  · simp

theorem blockDephase_pointer_state (ρ : MState (ι × Fin 2)) :
    (blockDephase (ι := ι) ρ).traceLeft =
      diagonalState ρ.traceLeft := by
  apply MState.ext_m
  ext a b
  rw [blockDephase_pointer, diagonalState_matrix]
  split_ifs with h
  · subst b
    have hreal := (Complex.nonneg_iff.mp (ρ.traceLeft.psd.diag_nonneg (i := a))).2
    apply Complex.ext
    · simp
    · simpa using hreal.symm
  · rfl

private theorem prod_matrix (ρ : MState ι) (σ : MState (Fin 2))
    (i j : ι) (a b : Fin 2) :
    (ρ ⊗ᴹ σ).m (i, a) (j, b) = ρ.m i j * σ.m a b := rfl

theorem blockDephase_product (ρ : MState (ι × Fin 2)) :
    blockDephase (ι := ι) (ρ.traceRight ⊗ᴹ ρ.traceLeft) =
      (blockDephase (ι := ι) ρ).traceRight ⊗ᴹ
        (blockDephase (ι := ι) ρ).traceLeft := by
  apply MState.ext_m
  ext ⟨i, a⟩ ⟨j, b⟩
  rw [blockDephase_matrix, prod_matrix, prod_matrix, blockDephase_body,
    blockDephase_pointer]
  split_ifs <;> simp

theorem qMutualInfo_blockDephase_le (ρ : MState (ι × Fin 2)) :
    qMutualInfo (blockDephase (ι := ι) ρ) ≤ qMutualInfo ρ := by
  have hdpi := sandwichedRenyiEntropy_DPI_eq_one ρ
    (ρ.traceRight ⊗ᴹ ρ.traceLeft) (blockDephase (ι := ι))
  change 𝐃(blockDephase (ι := ι) ρ‖
    blockDephase (ι := ι) (ρ.traceRight ⊗ᴹ ρ.traceLeft)) ≤
    𝐃(ρ‖ρ.traceRight ⊗ᴹ ρ.traceLeft) at hdpi
  rw [blockDephase_product] at hdpi
  have he : (qMutualInfo (blockDephase (ι := ι) ρ) : EReal) ≤
      (qMutualInfo ρ : EReal) := by
    rw [qMutualInfo_as_qRelativeEnt, qMutualInfo_as_qRelativeEnt]
    exact_mod_cast hdpi
  exact EReal.coe_le_coe_iff.mp he

theorem qMutualInfo_block_residual (ρ : MState (ι × Fin 2)) :
    qMutualInfo ρ - qMutualInfo (blockDephase (ι := ι) ρ) =
      (Sᵥₙ (blockDephase (ι := ι) ρ) - Sᵥₙ ρ) -
        (Sᵥₙ (diagonalState ρ.traceLeft) - Sᵥₙ ρ.traceLeft) := by
  rw [qMutualInfo, qMutualInfo, blockDephase_body,
    blockDephase_pointer_state]
  ring

theorem qMutualInfo_block_residual_nonnegative (ρ : MState (ι × Fin 2)) :
    0 ≤ (Sᵥₙ (blockDephase (ι := ι) ρ) - Sᵥₙ ρ) -
      (Sᵥₙ (diagonalState ρ.traceLeft) - Sᵥₙ ρ.traceLeft) := by
  rw [← qMutualInfo_block_residual]
  exact sub_nonneg.mpr (qMutualInfo_blockDephase_le ρ)

theorem blockDephase_ne_of_cross (ρ : MState (ι × Fin 2)) (i j : ι)
    (hcross : ρ.m (i, 0) (j, 1) ≠ 0) : blockDephase (ι := ι) ρ ≠ ρ := by
  intro h
  have hij := congrArg (fun σ : MState (ι × Fin 2) => σ.m (i, 0) (j, 1)) h
  rw [blockDephase_matrix] at hij
  simp only [zero_ne_one, ↓reduceIte] at hij
  exact hcross hij.symm

theorem blockDephase_idempotent (ρ : MState (ι × Fin 2)) :
    blockDephase (ι := ι) (blockDephase (ι := ι) ρ) =
      blockDephase (ι := ι) ρ := by
  apply MState.ext_m
  ext x y
  rw [blockDephase_matrix, blockDephase_matrix]
  split_ifs <;> simp

theorem blockDephase_no_common_recovery (ρ : MState (ι × Fin 2))
    (hne : blockDephase (ι := ι) ρ ≠ ρ) :
    ¬ ∃ recover : MState (ι × Fin 2) → MState (ι × Fin 2),
      recover (blockDephase (ι := ι) ρ) = ρ ∧
      recover (blockDephase (ι := ι) (blockDephase (ι := ι) ρ)) =
        blockDephase (ι := ι) ρ := by
  rintro ⟨recover, left, right⟩
  rw [blockDephase_idempotent] at right
  exact hne (right.symm.trans left)

theorem binaryDiagonalEntropy (ρ : MState (Fin 2)) (p q : ℝ)
    (h0 : ρ.m 0 0 = (p : ℂ)) (h1 : ρ.m 1 1 = (q : ℂ)) :
    Sᵥₙ (diagonalState ρ) = Real.negMulLog p + Real.negMulLog q := by
  rw [diagonalState, Sᵥₙ_ofClassical]
  simp only [Hₛ, H₁, Fin.sum_univ_two, diagonalDist_apply]
  rw [h0, h1]
  simp

end
end PhyslibCoherence
