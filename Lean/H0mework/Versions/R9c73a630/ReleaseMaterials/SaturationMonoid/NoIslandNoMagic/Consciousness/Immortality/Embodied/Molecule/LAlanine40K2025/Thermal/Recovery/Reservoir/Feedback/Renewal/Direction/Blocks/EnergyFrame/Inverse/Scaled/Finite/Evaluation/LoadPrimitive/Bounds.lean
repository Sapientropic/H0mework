import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Splice
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Basis

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive
open Propagation.Interface Load.Source
open scoped Matrix BigOperators Matrix.Norms.L2Operator
noncomputable section

theorem inverse_star : inverse=(1/2 : ℂ) • star basis := by
  ext i j
  norm_num [inverse,castMatrix,inverseQ,basis,Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_apply,Matrix.transpose_apply,Matrix.smul_apply,smul_eq_mul]

theorem basis_adjoint_square : star basis*basis=(2 : ℂ) • (1 : Matrix (Fin 8) (Fin 8) ℂ) := by
  have h := congrArg (fun M : Matrix (Fin 8) (Fin 8) ℂ => (2 : ℂ) • M) basis_left
  rw [inverse_star,Matrix.smul_mul,smul_smul] at h
  norm_num at h
  exact h

theorem basis_norm_product : ‖basis‖*‖inverse‖=1 := by
  have square := CStarRing.norm_star_mul_self (x := basis)
  rw [basis_adjoint_square,norm_smul,norm_one] at square
  norm_num at square
  rw [inverse_star,norm_smul,norm_star]
  norm_num
  nlinarith

theorem basis_action_norm (M : Matrix (Fin 8) (Fin 8) ℂ) : ‖basis*M*inverse‖ ≤ ‖M‖ := by
  calc
    _ ≤ ‖basis‖*‖M‖*‖inverse‖ := (norm_mul_le (basis*M) inverse).trans
      (mul_le_mul_of_nonneg_right (norm_mul_le basis M) (norm_nonneg inverse))
    _ = _ := by rw [mul_right_comm,basis_norm_product,one_mul]

private def joinEmbedding {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] :
    (Matrix ι ι ℂ × Matrix κ κ ℂ) →⋆ₐ[ℂ] Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ where
  toFun p := Matrix.fromBlocks p.1 0 0 p.2
  map_zero' := by ext i j; cases i <;> cases j <;> rfl
  map_one' := Matrix.fromBlocks_one
  map_add' A B := by ext i j; cases i <;> cases j <;> simp
  map_mul' A B := by rw [Matrix.fromBlocks_multiply]; simp
  commutes' c := by ext i j; cases i <;> cases j <;> simp [Algebra.algebraMap_eq_smul_one,Matrix.one_apply]
  map_star' A := by simp only [Matrix.star_eq_conjTranspose,Matrix.fromBlocks_conjTranspose,Matrix.conjTranspose_zero]; rfl

theorem join_norm {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ) : ‖Matrix.fromBlocks A 0 0 B‖ ≤ max ‖A‖ ‖B‖ :=
  NonUnitalStarAlgHom.norm_apply_le joinEmbedding (A,B)

theorem scalar_norm (a : ℂ) : ‖Matrix.scalar (Fin 1) a‖=‖a‖ := by
  simp only [Matrix.scalar_apply,Matrix.l2_opNorm_diagonal]
  exact pi_norm_const a

theorem raw_norm (M N : Matrix (Fin 3) (Fin 3) ℂ) (a b : ℂ) :
    ‖raw M N a b‖ ≤ max ‖M‖ (max ‖a‖ (max ‖b‖ ‖N‖)) := by
  unfold raw
  apply (join_norm _ _).trans
  apply max_le_max (le_refl _) ((join_norm _ _).trans ?_)
  rw [scalar_norm]
  apply max_le_max (le_refl _) ((join_norm _ _).trans ?_)
  rw [scalar_norm]

theorem splice_norm (M N : Matrix (Fin 3) (Fin 3) ℂ) (a b : ℂ) :
    ‖splice M N a b‖ ≤ max ‖M‖ (max ‖a‖ (max ‖b‖ ‖N‖)) := by
  unfold splice
  rw [Finite.reindex_norm]
  exact raw_norm M N a b

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
