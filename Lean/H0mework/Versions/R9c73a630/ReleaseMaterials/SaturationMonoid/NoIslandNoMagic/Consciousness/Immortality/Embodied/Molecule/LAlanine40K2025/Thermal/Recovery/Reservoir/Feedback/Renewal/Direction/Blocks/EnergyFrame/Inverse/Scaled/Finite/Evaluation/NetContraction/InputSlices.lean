import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Charged
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Contraction.Injection

set_option autoImplicit false
set_option maxRecDepth 4096
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction
open Propagation.Interface Load.Source Collision Contraction
open scoped Matrix
noncomputable section
open Powered.Dynamics
attribute [local irreducible] InputProducts.pair Prepared.finiteEnvironment

def pairAddress (a b : Basis) (o : Fin 2) : Basis × Basis := if o=0 then (a,b) else (b,a)

def originalPairBlock (a b : Basis) : Matrix (Fin 2) (Fin 2) ℂ :=
  InputProducts.pair.submatrix (pairAddress a b) (pairAddress a b)

theorem body_input_ordinary (a b : Basis) (distinct : a ≠ b) :
    (localBodyInput s(a,b)).submatrix (Scaled.Order.offDiagonalPCEEquiv a b distinct) (Scaled.Order.offDiagonalPCEEquiv a b distinct)=
      Matrix.kronecker (chargedInput (originalPairBlock a b)) Prepared.finiteEnvironment := by
  ext ⟨⟨o,c⟩,e⟩ ⟨⟨p,d⟩,f⟩
  rfl

theorem body_input_diagonal (a : Basis) :
    (localBodyInput s(a,a)).submatrix (Scaled.Order.diagonalPCEEquiv a) (Scaled.Order.diagonalPCEEquiv a)=
      Matrix.kronecker (InputProducts.pair (a,a) (a,a) • excitedController) Prepared.finiteEnvironment := by
  ext ⟨c,e⟩ ⟨d,f⟩
  rfl

variable {α β γ : Type*} [Fintype α]

theorem rectangular_corner (A : Matrix α β ℂ) (O : Matrix α α ℂ) (f : γ → β) :
    (A.conjTranspose*O*A).submatrix f f=(A.submatrix id f).conjTranspose*O*A.submatrix id f := by
  rw [← Matrix.submatrix_mul_equiv _ _ f (Equiv.refl α) f,
    ← Matrix.submatrix_mul_equiv _ _ f (Equiv.refl α) (Equiv.refl α)]
  rfl

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
