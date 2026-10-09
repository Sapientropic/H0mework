import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Order.Energies

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Order
open Propagation.Interface Load.Source
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

theorem source_E_diagonal : E=Matrix.diagonal (fun i : Basis => (Donor.calculatedEnergy i : ℂ)) := by
  unfold E Donor.calculatedEnergy
  congr 1
  funext i
  push_cast
  rfl

theorem numeric_hpc_block (a b : Basis) (distinct : a ≠ b) :
    (sourcePCH E).submatrix (orbitPC a b) (orbitPC a b)=scalarHpc (Donor.calculatedEnergy a) (Donor.calculatedEnergy b) := by
  rw [source_E_diagonal]
  exact hpc_scalar_block Donor.calculatedEnergy a b distinct

theorem scalar_monotone (x y a b : ℝ) (first : a ≤ x) (second : b ≤ y) :
    scalarHpc a b ≤ scalarHpc x y := by
  have packed := Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr (packed_monotone x y a b first second))
  have restricted := packed.submatrix (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4)
  apply sub_nonneg.mp
  exact restricted.nonneg

theorem numeric_hpc_envelope (a b : Basis) (ordered : a < b) :
    (sourcePCH E).submatrix (orbitPC 0 1) (orbitPC 0 1) ≤
      (sourcePCH E).submatrix (orbitPC a b) (orbitPC a b) ∧
    (sourcePCH E).submatrix (orbitPC a b) (orbitPC a b) ≤
      (sourcePCH E).submatrix (orbitPC 96 97) (orbitPC 96 97) := by
  rw [numeric_hpc_block 0 1 (by decide),numeric_hpc_block a b ordered.ne,
    numeric_hpc_block 96 97 (by decide)]
  have bounds := ordered_source_limits a b ordered
  exact ⟨scalar_monotone _ _ _ _ bounds.1 bounds.2.1,scalar_monotone _ _ _ _ bounds.2.2.1 bounds.2.2.2⟩

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Order
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
