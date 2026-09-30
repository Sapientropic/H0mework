import H0mework.Chemistry.LAlaninePropagation.BoundElectronicPropagation

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.SourcePrimitive

open Propagation.Interface Propagation.Source

noncomputable def sourceFieldSquaredBlock (block : Fin 7) : ℤ :=
  ∑ offset : Fin 14, ∑ j : Basis,
    symmetricEntry electronicSource.zQ (finProdFinEquiv (block, offset)) j ^ 2

noncomputable def sourceFieldSquaredMagnitude : ℤ :=
  ∑ i : Basis, ∑ j : Basis, symmetricEntry electronicSource.zQ i j ^ 2


set_option maxRecDepth 4096 in
set_option maxHeartbeats 600000 in
theorem sourceFieldSquaredBlock0 : sourceFieldSquaredBlock 0 ≤ 4 * 10 ^ 27 := by decide

end LAlanine40K2025.Thermal.Recovery.SourcePrimitive
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
