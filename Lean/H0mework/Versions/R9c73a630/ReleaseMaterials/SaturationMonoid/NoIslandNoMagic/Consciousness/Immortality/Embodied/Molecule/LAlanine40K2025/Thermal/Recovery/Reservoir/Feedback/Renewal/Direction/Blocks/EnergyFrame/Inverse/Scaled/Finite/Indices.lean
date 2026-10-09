import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Donor

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite
open Propagation.Interface Load.Source Scaled.Order
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def tripleIndex : ((Fin 2 × Fin 2) × Fin 2) ≃ Fin 8 :=
  (Equiv.prodCongr (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4) (Equiv.refl (Fin 2))).trans finProdFinEquiv

theorem reindex_norm {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : κ ≃ ι) (M : Matrix ι ι ℂ) : ‖M.submatrix e e‖=‖M‖ := by
  let morphism : Matrix ι ι ℂ ≃⋆ₐ[ℂ] Matrix κ κ ℂ :=
    { Matrix.reindexAlgEquiv ℂ ℂ e.symm with
      map_star' := by intro A; rfl
      map_smul' := by intro c A; rfl }
  exact StarAlgEquiv.norm_map morphism M

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
