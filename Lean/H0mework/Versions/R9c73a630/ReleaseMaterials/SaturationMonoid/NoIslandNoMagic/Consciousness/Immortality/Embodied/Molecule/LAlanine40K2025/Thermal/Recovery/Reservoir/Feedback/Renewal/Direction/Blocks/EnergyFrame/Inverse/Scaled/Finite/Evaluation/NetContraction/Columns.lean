import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Coordinates
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Contraction.Injection

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction
open Propagation.Interface Load.Source Collision Contraction
open scoped Matrix
noncomputable section
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

omit [Fintype β] in
theorem column_pullback (A O : Matrix α α ℂ) (f : β → α) :
    (star A*O*A).submatrix f f=
      (A.submatrix id f).conjTranspose*O*A.submatrix id f := by
  rw [← Matrix.submatrix_mul_equiv _ _ f (Equiv.refl α) f,
    ← Matrix.submatrix_mul_equiv _ _ f (Equiv.refl α) (Equiv.refl α)]
  rfl

omit [Fintype γ] in
theorem rectangular_pullback (A : Matrix α β ℂ) (B : Matrix β γ ℂ) (O : Matrix α α ℂ) :
    B.conjTranspose*(A.conjTranspose*O*A)*B=(A*B).conjTranspose*O*(A*B) := by
  simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]

omit [Fintype β] in
theorem rectangular_net (A B : Matrix α α ℂ) (O : Matrix α α ℂ) (X : Matrix α β ℂ) :
    X.conjTranspose*(star A*O*A-star B*O*B)*X=
      (A*X).conjTranspose*O*(A*X)-(B*X).conjTranspose*O*(B*X) := by
  rw [Matrix.mul_sub,Matrix.sub_mul]
  simp only [Matrix.star_eq_conjTranspose,rectangular_pullback]

theorem input_pullback (A O : Matrix β β ℂ) (ρ : Matrix β β ℂ) :
    Collision.energy O (A*ρ*star A)=Collision.energy (star A*O*A) ρ := by
  unfold Collision.energy
  congr 1
  rw [← Matrix.mul_assoc O (A*ρ) (star A),Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
