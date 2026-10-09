import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Post.Instrument

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Post
open Collision Load.Source
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

theorem raw_pullback_covariance {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) (A B : Matrix ι ι ℂ) :
    Quantum.conjugation U (star A*B*A)=
      star (Quantum.conjugation U A)*Quantum.conjugation U B*Quantum.conjugation U A := by
  let phi := Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) U
  change phi (star A*B*A)=star (phi A)*phi B*phi A
  rw [map_mul,map_mul,map_star]

theorem corner_conjugation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) (A : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) :
    Quantum.conjugation U (Prepared.pointerReadout A)=Prepared.pointerReadout (Quantum.conjugation (blockUnitary U U) A) := by
  change (U : Matrix ι ι ℂ)*A.toBlocks₁₁*star (U : Matrix ι ι ℂ)=
    ((blockUnitary U U : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ)*A*star (blockUnitary U U : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ)).toBlocks₁₁
  rw [blockUnitary_conjugation_blocks]
  rfl

theorem raw_sandwich_change {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B O : Matrix ι ι ℂ) :
    ‖star A*O*A-star B*O*B‖ ≤ (‖A‖+‖B‖)*‖O‖*‖A-B‖ := by
  have split : star A*O*A-star B*O*B=star (A-B)*O*A+star B*O*(A-B) := by rw [star_sub]; noncomm_ring
  rw [split]
  apply (norm_add_le _ _).trans
  have left := (norm_mul_le (star (A-B)*O) A).trans
    (mul_le_mul_of_nonneg_right (norm_mul_le (star (A-B)) O) (norm_nonneg A))
  have right := (norm_mul_le (star B*O) (A-B)).trans
    (mul_le_mul_of_nonneg_right (norm_mul_le (star B) O) (norm_nonneg (A-B)))
  have paid := add_le_add left right
  simp only [norm_star] at paid
  convert paid using 1
  ring

theorem donor_slice_hermitian (O : Current.FullJoint) (hermitian : O.IsHermitian) : (Supply.donorSlice O).IsHermitian :=
  hermitian.submatrix _

theorem donor_slice_norm (O : Current.FullJoint) (hermitian : O.IsHermitian) : ‖Supply.donorSlice O‖ ≤ ‖O‖ :=
  Prepared.principal_norm (fun i : PairController × Fin 2 => ((i.1,Supply.donorIndex),i.2))
    (fun _ _ same => congrArg (fun p : Current.FullIndex => (p.1.1,p.2)) same) O hermitian

theorem donor_slice_sub (A B : Current.FullJoint) : Supply.donorSlice (A-B)=Supply.donorSlice A-Supply.donorSlice B := rfl

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Post
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
