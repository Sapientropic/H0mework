import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.Algebra
import Mathlib.Analysis.CStarAlgebra.Hom

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def blockEmbedding (label : ι → κ) :
    (∀ k, Matrix {i // label i = k} {i // label i = k} ℂ) →⋆ₐ[ℂ]
      Matrix (Σ k, {i // label i = k}) (Σ k, {i // label i = k}) ℂ where
  toFun := Matrix.blockDiagonal'
  map_zero' := Matrix.blockDiagonal'_zero
  map_one' := Matrix.blockDiagonal'_one
  map_add' := Matrix.blockDiagonal'_add
  map_mul' := Matrix.blockDiagonal'_mul
  commutes' c := by simp [Algebra.algebraMap_eq_smul_one]
  map_star' A := by
    simp only [Matrix.star_eq_conjTranspose, Matrix.blockDiagonal'_conjTranspose]
    rfl

def regroupStarEquiv (label : ι → κ) : Matrix ι ι ℂ ≃⋆ₐ[ℂ]
    Matrix (Σ k, {i // label i = k}) (Σ k, {i // label i = k}) ℂ :=
  { Matrix.reindexAlgEquiv ℂ ℂ (Equiv.sigmaFiberEquiv label).symm with
    map_star' := by intro A; rfl
    map_smul' := by intro c A; rfl }

theorem norm_eq_block_norm {label : ι → κ} {A : Matrix ι ι ℂ} (kept : Preserves label A) :
    ‖A‖ = ‖fun k => restrict label k A‖ := by
  calc
    _ = ‖regroupStarEquiv label A‖ := (StarAlgEquiv.norm_map _ _).symm
    _ = ‖blockEmbedding label (fun k => restrict label k A)‖ := by
      congr 1
      exact regroup_eq_blocks kept
    _ = _ := NonUnitalStarAlgHom.norm_map (blockEmbedding label) Matrix.blockDiagonal'_injective _

theorem norm_le_iff_block_norm_le {label : ι → κ} {A : Matrix ι ι ℂ}
    (kept : Preserves label A) (r : ℝ) (nonnegative : 0 ≤ r) :
    ‖A‖ ≤ r ↔ ∀ k, ‖restrict label k A‖ ≤ r := by
  rw [norm_eq_block_norm kept]
  exact pi_norm_le_iff_of_nonneg nonnegative

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
