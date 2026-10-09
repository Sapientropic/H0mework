import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Post.Frame

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Post
open Collision
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem reframe_blocks (W U V : Matrix.unitaryGroup ι ℂ) :
    (Actions.reframeUnitary (blockUnitary W W) (blockUnitary U V) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ)=
      Matrix.fromBlocks (Quantum.conjugation W (U : Matrix ι ι ℂ)) 0 0 (Quantum.conjugation W (V : Matrix ι ι ℂ)) := by
  rw [Actions.reframe_value]
  change (blockUnitary W W : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ)*Matrix.fromBlocks (U : Matrix ι ι ℂ) 0 0 (V : Matrix ι ι ℂ)*
    star (blockUnitary W W : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ)=_
  rw [blockUnitary_conjugation_blocks]
  simp [Quantum.conjugation_apply]

theorem reframe_phase (W V : Matrix.unitaryGroup ι ℂ) (phase : unitary ℂ) :
    Quantum.conjugation W ((phase • V : Matrix.unitaryGroup ι ℂ) : Matrix ι ι ℂ)=
      (phase : ℂ) • Quantum.conjugation W (V : Matrix ι ι ℂ) := by
  change Quantum.conjugation W ((phase : ℂ) • (V : Matrix ι ι ℂ))=_
  rw [map_smul]

theorem phase_matrix_error [Nonempty ι] (phase : unitary ℂ) (scalar : ℂ) (U : Matrix.unitaryGroup ι ℂ)
    (A : Matrix ι ι ℂ) (d e : ℝ) (matrixError : ‖(U : Matrix ι ι ℂ)-A‖ ≤ d) (phaseError : ‖(phase : ℂ)-scalar‖ ≤ e) :
    ‖(phase : ℂ) • (U : Matrix ι ι ℂ)-scalar • A‖ ≤ d+(1+d)*e := by
  have split : (phase : ℂ) • (U : Matrix ι ι ℂ)-scalar • A=
      (phase : ℂ) • ((U : Matrix ι ι ℂ)-A)+((phase : ℂ)-scalar) • A := by module
  rw [split]
  apply (norm_add_le _ _).trans
  simp only [norm_smul,CStarRing.norm_coe_unitary,one_mul]
  have normA := Input.approximated_unitary_norm U A d matrixError
  have bound := mul_le_mul phaseError normA (norm_nonneg A) (le_trans (norm_nonneg _) phaseError)
  nlinarith

theorem blocks_error (A B C D : Matrix ι ι ℂ) :
    ‖Matrix.fromBlocks A 0 0 B-Matrix.fromBlocks C 0 0 D‖ ≤ max ‖A-C‖ ‖B-D‖ := by
  have split : Matrix.fromBlocks A 0 0 B-Matrix.fromBlocks C 0 0 D=Matrix.fromBlocks (A-C) 0 0 (B-D) := by
    ext i j
    cases i <;> cases j <;> simp
  rw [split]
  exact two_block_norm _ _

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Post
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
