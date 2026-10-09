import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot.Restriction

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot.Full
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def assemble (label : ι → κ) (family : ∀ k, Matrix {i // label i=k} {i // label i=k} ℂ) : Matrix ι ι ℂ :=
  (regroupStarEquiv label).symm (blockEmbedding label family)

theorem assemble_error (label : ι → κ) (A : Matrix ι ι ℂ) (kept : Preserves label A)
    (family : ∀ k, Matrix {i // label i=k} {i // label i=k} ℂ) (d : ℝ) (dpos : 0 ≤ d)
    (paid : ∀ k, ‖restrict label k A-family k‖ ≤ d) : ‖A-assemble label family‖ ≤ d := by
  have represented : regroupStarEquiv label A=blockEmbedding label (fun k => restrict label k A) := regroup_eq_blocks kept
  calc
    ‖A-assemble label family‖ = ‖regroupStarEquiv label (A-assemble label family)‖ := (StarAlgEquiv.norm_map _ _).symm
    _ = ‖blockEmbedding label (fun k => restrict label k A-family k)‖ := by
      rw [map_sub,represented]
      change ‖blockEmbedding label (fun k => restrict label k A)-
        regroupStarEquiv label ((regroupStarEquiv label).symm (blockEmbedding label family))‖ = _
      rw [StarAlgEquiv.apply_symm_apply,← map_sub]
      rfl
    _ ≤ ‖fun k => restrict label k A-family k‖ := NonUnitalStarAlgHom.norm_apply_le (blockEmbedding label) _
    _ ≤ d := (pi_norm_le_iff_of_nonneg dpos).mpr paid

theorem lifted_error (e : κ ≃ ι) (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ)
    (d : ℝ) (paid : ‖A.submatrix e e-B‖ ≤ d) : ‖A-B.submatrix e.symm e.symm‖ ≤ d := by
  have same : A-B.submatrix e.symm e.symm=(A.submatrix e e-B).submatrix e.symm e.symm := by
    ext i j
    change A i j-B (e.symm i) (e.symm j)=A (e (e.symm i)) (e (e.symm j))-B (e.symm i) (e.symm j)
    simp only [Equiv.apply_symm_apply]
  rw [same,Finite.reindex_norm]
  exact paid

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot.Full
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
