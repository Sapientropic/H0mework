import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot.Full.Whole

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Contraction
open Propagation.Interface Load.Source
open scoped Matrix
noncomputable section

theorem assemble_preserves {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (label : ι → κ) (family : ∀ k, Matrix {i // label i=k} {i // label i=k} ℂ) :
    Preserves label (SquareRoot.Full.assemble label family) := by
  intro i j separated
  change Matrix.blockDiagonal' family ⟨label i,⟨i,rfl⟩⟩ ⟨label j,⟨j,rfl⟩⟩=0
  exact Matrix.blockDiagonal'_apply_ne family _ _ separated

theorem assemble_restriction {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (label : ι → κ) (family : ∀ k, Matrix {i // label i=k} {i // label i=k} ℂ) (k : κ) :
    restrict label k (SquareRoot.Full.assemble label family)=family k := by
  ext i j
  change Matrix.blockDiagonal' family ⟨label i.val,⟨i.val,rfl⟩⟩ ⟨label j.val,⟨j.val,rfl⟩⟩=family k i j
  have left : (⟨label i.val,⟨i.val,rfl⟩⟩ : Σ k, {x // label x=k})=⟨k,i⟩ := by rcases i with ⟨x,hx⟩; cases hx; rfl
  have right : (⟨label j.val,⟨j.val,rfl⟩⟩ : Σ k, {x // label x=k})=⟨k,j⟩ := by rcases j with ⟨x,hx⟩; cases hx; rfl
  rw [left,right,Matrix.blockDiagonal'_apply_eq]

local instance : Fintype (Sym2 Basis) := Fintype.ofFinite _

theorem finite_root_preserves : Preserves pceOrbit SquareRoot.Full.sourceRoot :=
  assemble_preserves pceOrbit _

theorem finite_complement_preserves : Preserves pceOrbit SquareRoot.Full.sourceComplement :=
  assemble_preserves pceOrbit _

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Contraction
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
