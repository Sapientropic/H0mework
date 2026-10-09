import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.DiagonalMaterial
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Scalars.B384
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Scalars.B390
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Scalars.D004

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.DiagonalAddresses
open Propagation.Interface

theorem energy96_0 : Scalars.energy9216=diagonalScalarEnergy (96 : Basis) 0 := by decide +kernel
def component96_0 : ScalarMaterial (diagonalScalarEnergy (96 : Basis) 0) := energy96_0 ▸ Scalars.material9216
theorem energy96_1 : Scalars.energyD96=diagonalScalarEnergy (96 : Basis) 1 := by decide +kernel
def component96_1 : ScalarMaterial (diagonalScalarEnergy (96 : Basis) 1) := energy96_1 ▸ Scalars.materialD96
def material96 : DiagonalMaterial (96 : Basis)
  | ⟨0,_⟩ => component96_0
  | ⟨1,_⟩ => component96_1
  | ⟨n+2,h⟩ => False.elim (by omega)

theorem energy97_0 : Scalars.energy9340=diagonalScalarEnergy (97 : Basis) 0 := by decide +kernel
def component97_0 : ScalarMaterial (diagonalScalarEnergy (97 : Basis) 0) := energy97_0 ▸ Scalars.material9340
theorem energy97_1 : Scalars.energyD97=diagonalScalarEnergy (97 : Basis) 1 := by decide +kernel
def component97_1 : ScalarMaterial (diagonalScalarEnergy (97 : Basis) 1) := energy97_1 ▸ Scalars.materialD97
def material97 : DiagonalMaterial (97 : Basis)
  | ⟨0,_⟩ => component97_0
  | ⟨1,_⟩ => component97_1
  | ⟨n+2,h⟩ => False.elim (by omega)

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.DiagonalAddresses
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
