import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Order.DiagonalSource

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Order
open Propagation.Interface Load.Source
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

theorem diagonal_avoids_donor (a : Fin 97) (c : Fin 2) :
    ((a.castSucc,a.castSucc),c) ≠ ((Donor.calculatedTop,Donor.calculatedTop),(1 : Fin 2)) := by
  intro same
  have first := congrArg (fun p : PairController => p.1.1.val) same
  change a.val=97 at first
  have bound := a.isLt
  omega

private theorem diagonal_left_zero {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (d : ι → ℂ) (M : Matrix ι ι ℂ) (f : κ → ι) (zero : ∀ i, d (f i)=0) :
    (Matrix.diagonal d*M).submatrix f f=0 := by
  ext i j
  simp only [Matrix.submatrix_apply,Matrix.diagonal_mul,zero,zero_mul,Matrix.zero_apply]

private theorem diagonal_right_zero {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (d : ι → ℂ) (M : Matrix ι ι ℂ) (f : κ → ι) (zero : ∀ i, d (f i)=0) :
    (M*Matrix.diagonal d).submatrix f f=0 := by
  ext i j
  simp only [Matrix.submatrix_apply,Matrix.mul_diagonal,zero,mul_zero,Matrix.zero_apply]

theorem diagonal_left_block (a : Fin 97) (M : LoadedJoint) :
    (numericProjector*M).submatrix (diagonalPCE a.castSucc) (diagonalPCE a.castSucc)=0 := by
  rw [projector_diagonal]
  exact diagonal_left_zero _ M (diagonalPCE a.castSucc) (by
    intro i
    simp only [diagonalPCE,diagonal_avoids_donor a i.1,ite_false])

theorem diagonal_right_block (a : Fin 97) (M : LoadedJoint) :
    (M*numericProjector).submatrix (diagonalPCE a.castSucc) (diagonalPCE a.castSucc)=0 := by
  rw [projector_diagonal]
  exact diagonal_right_zero _ M (diagonalPCE a.castSucc) (by
    intro i
    simp only [diagonalPCE,diagonal_avoids_donor a i.1,ite_false])

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Order
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
