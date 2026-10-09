import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.Roots
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.Load

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open scoped Matrix

variable {ι κ : Type*} [DecidableEq κ]

def assembleQ (label : ι → κ) (family : ∀ k, MatrixQ {i // label i=k} {i // label i=k}) : MatrixQ ι ι :=
  fun i j => Matrix.blockDiagonal' family ⟨label i,⟨i,rfl⟩⟩ ⟨label j,⟨j,rfl⟩⟩

theorem qvalue_assemble [Fintype ι] [DecidableEq ι] [Fintype κ]
    (label : ι → κ) (family : ∀ k, MatrixQ {i // label i=k} {i // label i=k}) :
    qvalue (assembleQ label family)=SquareRoot.Full.assemble label (fun k => qvalue (family k)) := by
  ext i j
  change Scalar.value (Matrix.blockDiagonal' family ⟨label i,⟨i,rfl⟩⟩ ⟨label j,⟨j,rfl⟩⟩)=
    Matrix.blockDiagonal' (fun k => qvalue (family k)) ⟨label i,⟨i,rfl⟩⟩ ⟨label j,⟨j,rfl⟩⟩
  by_cases same : label i=label j
  · simp only [Matrix.blockDiagonal',Matrix.of_apply,same,dif_pos,qvalue]
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ same,Matrix.blockDiagonal'_apply_ne _ _ _ same]
    simp [Scalar.value]

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
