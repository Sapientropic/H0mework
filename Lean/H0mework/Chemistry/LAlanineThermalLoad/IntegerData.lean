import H0mework.Chemistry.LAlaninePropagation.BoundElectronicPropagation

/-! # Source-owned integer square blocks for the original Hamiltonian norm -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Load.Producer.StrictThermal

noncomputable section

def sourceSquaredMagnitude : ℤ :=
  ∑ i : Propagation.Interface.Basis, ∑ j : Propagation.Interface.Basis,
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource i j ^ 2

def sourceSquaredBlock (block : Fin 7) : ℤ :=
  ∑ offset : Fin 14, ∑ j : Propagation.Interface.Basis,
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource
      (finProdFinEquiv (block, offset)) j ^ 2

theorem sourceSquaredMagnitude_blocks : sourceSquaredMagnitude = ∑ block, sourceSquaredBlock block := by
  unfold sourceSquaredMagnitude sourceSquaredBlock
  have reindex := Equiv.sum_comp (finProdFinEquiv : Fin 7 × Fin 14 ≃ Fin 98)
    (fun i => ∑ j : Propagation.Interface.Basis,
      Propagation.Interface.activeNumerator Propagation.Source.electronicSource i j ^ 2)
  simpa only [Fintype.sum_prod_type] using reindex.symm

end

end LAlanine40K2025.Thermal.Load.Producer.StrictThermal
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
