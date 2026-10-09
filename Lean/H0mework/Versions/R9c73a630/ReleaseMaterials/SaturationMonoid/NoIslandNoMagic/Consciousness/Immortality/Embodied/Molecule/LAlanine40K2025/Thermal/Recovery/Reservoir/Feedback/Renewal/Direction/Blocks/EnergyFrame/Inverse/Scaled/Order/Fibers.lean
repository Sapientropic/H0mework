import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Order.Support

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Order
open Propagation.Interface Load.Source
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def pceFiberEquiv (k : Sym2 Basis) : {p : PairController × Fin 2 // pceOrbit p=k} ≃
    {p : PairController // pcOrbit p=k} × Fin 2 where
  toFun p := (⟨p.val.1,p.property⟩,p.val.2)
  invFun p := ⟨(p.1.val,p.2),p.1.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def offDiagonalPCEEquiv (a b : Basis) (distinct : a ≠ b) :
    (Fin 2 × Fin 2) × Fin 2 ≃ {p : PairController × Fin 2 // pceOrbit p=s(a,b)} :=
  (Equiv.prodCongr (offDiagonalEquiv a b distinct) (Equiv.refl (Fin 2))).trans (pceFiberEquiv s(a,b)).symm

def diagonalPCEEquiv (a : Basis) : Fin 2 × Fin 2 ≃ {p : PairController × Fin 2 // pceOrbit p=s(a,a)} :=
  (Equiv.prodCongr (diagonalEquiv a) (Equiv.refl (Fin 2))).trans (pceFiberEquiv s(a,a)).symm

private theorem reindex_norm {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : κ ≃ ι) (M : Matrix ι ι ℂ) : ‖M.submatrix e e‖=‖M‖ := by
  let morphism : Matrix ι ι ℂ ≃⋆ₐ[ℂ] Matrix κ κ ℂ :=
    { Matrix.reindexAlgEquiv ℂ ℂ e.symm with
      map_star' := by intro A; rfl
      map_smul' := by intro c A; rfl }
  exact StarAlgEquiv.norm_map morphism M

theorem offDiagonal_fiber_norm (a b : Basis) (distinct : a ≠ b) :
    ‖restrict pceOrbit s(a,b) rationalCore‖=‖rationalCore.submatrix (orbitPCE a b) (orbitPCE a b)‖ := by
  have same := reindex_norm (offDiagonalPCEEquiv a b distinct) (restrict pceOrbit s(a,b) rationalCore)
  exact same.symm

theorem diagonal_fiber_norm (a : Basis) :
    ‖restrict pceOrbit s(a,a) rationalCore‖=‖rationalCore.submatrix (diagonalPCE a) (diagonalPCE a)‖ := by
  have same := reindex_norm (diagonalPCEEquiv a) (restrict pceOrbit s(a,a) rationalCore)
  exact same.symm

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Order
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
