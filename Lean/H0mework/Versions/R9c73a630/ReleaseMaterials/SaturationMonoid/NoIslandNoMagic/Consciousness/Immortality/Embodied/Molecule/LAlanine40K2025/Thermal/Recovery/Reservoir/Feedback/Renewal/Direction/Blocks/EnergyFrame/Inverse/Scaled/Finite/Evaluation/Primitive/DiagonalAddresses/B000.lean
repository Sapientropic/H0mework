import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.DiagonalMaterial
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Scalars.B000
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Scalars.B001
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Scalars.B005
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Scalars.B006
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Scalars.B066
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Scalars.B073
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Scalars.B079
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Scalars.B082
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Scalars.B089
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Scalars.B090
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Scalars.D000

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.DiagonalAddresses
open Propagation.Interface

theorem energy0_0 : Scalars.energy1=diagonalScalarEnergy (0 : Basis) 0 := by decide +kernel
def component0_0 : ScalarMaterial (diagonalScalarEnergy (0 : Basis) 0) := energy0_0 ▸ Scalars.material1
theorem energy0_1 : Scalars.energyD0=diagonalScalarEnergy (0 : Basis) 1 := by decide +kernel
def component0_1 : ScalarMaterial (diagonalScalarEnergy (0 : Basis) 1) := energy0_1 ▸ Scalars.materialD0
def material0 : DiagonalMaterial (0 : Basis)
  | ⟨0,_⟩ => component0_0
  | ⟨1,_⟩ => component0_1
  | ⟨n+2,h⟩ => False.elim (by omega)

theorem energy1_0 : Scalars.energy2=diagonalScalarEnergy (1 : Basis) 0 := by decide +kernel
def component1_0 : ScalarMaterial (diagonalScalarEnergy (1 : Basis) 0) := energy1_0 ▸ Scalars.material2
theorem energy1_1 : Scalars.energyD1=diagonalScalarEnergy (1 : Basis) 1 := by decide +kernel
def component1_1 : ScalarMaterial (diagonalScalarEnergy (1 : Basis) 1) := energy1_1 ▸ Scalars.materialD1
def material1 : DiagonalMaterial (1 : Basis)
  | ⟨0,_⟩ => component1_0
  | ⟨1,_⟩ => component1_1
  | ⟨n+2,h⟩ => False.elim (by omega)

theorem energy2_0 : Scalars.energy14=diagonalScalarEnergy (2 : Basis) 0 := by decide +kernel
def component2_0 : ScalarMaterial (diagonalScalarEnergy (2 : Basis) 0) := energy2_0 ▸ Scalars.material14
theorem energy2_1 : Scalars.energyD2=diagonalScalarEnergy (2 : Basis) 1 := by decide +kernel
def component2_1 : ScalarMaterial (diagonalScalarEnergy (2 : Basis) 1) := energy2_1 ▸ Scalars.materialD2
def material2 : DiagonalMaterial (2 : Basis)
  | ⟨0,_⟩ => component2_0
  | ⟨1,_⟩ => component2_1
  | ⟨n+2,h⟩ => False.elim (by omega)

theorem energy3_0 : Scalars.energy114=diagonalScalarEnergy (3 : Basis) 0 := by decide +kernel
def component3_0 : ScalarMaterial (diagonalScalarEnergy (3 : Basis) 0) := energy3_0 ▸ Scalars.material114
theorem energy3_1 : Scalars.energyD3=diagonalScalarEnergy (3 : Basis) 1 := by decide +kernel
def component3_1 : ScalarMaterial (diagonalScalarEnergy (3 : Basis) 1) := energy3_1 ▸ Scalars.materialD3
def material3 : DiagonalMaterial (3 : Basis)
  | ⟨0,_⟩ => component3_0
  | ⟨1,_⟩ => component3_1
  | ⟨n+2,h⟩ => False.elim (by omega)

theorem energy4_0 : Scalars.energy116=diagonalScalarEnergy (4 : Basis) 0 := by decide +kernel
def component4_0 : ScalarMaterial (diagonalScalarEnergy (4 : Basis) 0) := energy4_0 ▸ Scalars.material116
theorem energy4_1 : Scalars.energyD4=diagonalScalarEnergy (4 : Basis) 1 := by decide +kernel
def component4_1 : ScalarMaterial (diagonalScalarEnergy (4 : Basis) 1) := energy4_1 ▸ Scalars.materialD4
def material4 : DiagonalMaterial (4 : Basis)
  | ⟨0,_⟩ => component4_0
  | ⟨1,_⟩ => component4_1
  | ⟨n+2,h⟩ => False.elim (by omega)

theorem energy5_0 : Scalars.energy124=diagonalScalarEnergy (5 : Basis) 0 := by decide +kernel
def component5_0 : ScalarMaterial (diagonalScalarEnergy (5 : Basis) 0) := energy5_0 ▸ Scalars.material124
theorem energy5_1 : Scalars.energyD5=diagonalScalarEnergy (5 : Basis) 1 := by decide +kernel
def component5_1 : ScalarMaterial (diagonalScalarEnergy (5 : Basis) 1) := energy5_1 ▸ Scalars.materialD5
def material5 : DiagonalMaterial (5 : Basis)
  | ⟨0,_⟩ => component5_0
  | ⟨1,_⟩ => component5_1
  | ⟨n+2,h⟩ => False.elim (by omega)

theorem energy6_0 : Scalars.energy1569=diagonalScalarEnergy (6 : Basis) 0 := by decide +kernel
def component6_0 : ScalarMaterial (diagonalScalarEnergy (6 : Basis) 0) := energy6_0 ▸ Scalars.material1569
theorem energy6_1 : Scalars.energyD6=diagonalScalarEnergy (6 : Basis) 1 := by decide +kernel
def component6_1 : ScalarMaterial (diagonalScalarEnergy (6 : Basis) 1) := energy6_1 ▸ Scalars.materialD6
def material6 : DiagonalMaterial (6 : Basis)
  | ⟨0,_⟩ => component6_0
  | ⟨1,_⟩ => component6_1
  | ⟨n+2,h⟩ => False.elim (by omega)

theorem energy7_0 : Scalars.energy1747=diagonalScalarEnergy (7 : Basis) 0 := by decide +kernel
def component7_0 : ScalarMaterial (diagonalScalarEnergy (7 : Basis) 0) := energy7_0 ▸ Scalars.material1747
theorem energy7_1 : Scalars.energyD7=diagonalScalarEnergy (7 : Basis) 1 := by decide +kernel
def component7_1 : ScalarMaterial (diagonalScalarEnergy (7 : Basis) 1) := energy7_1 ▸ Scalars.materialD7
def material7 : DiagonalMaterial (7 : Basis)
  | ⟨0,_⟩ => component7_0
  | ⟨1,_⟩ => component7_1
  | ⟨n+2,h⟩ => False.elim (by omega)

theorem energy8_0 : Scalars.energy1884=diagonalScalarEnergy (8 : Basis) 0 := by decide +kernel
def component8_0 : ScalarMaterial (diagonalScalarEnergy (8 : Basis) 0) := energy8_0 ▸ Scalars.material1884
theorem energy8_1 : Scalars.energyD8=diagonalScalarEnergy (8 : Basis) 1 := by decide +kernel
def component8_1 : ScalarMaterial (diagonalScalarEnergy (8 : Basis) 1) := energy8_1 ▸ Scalars.materialD8
def material8 : DiagonalMaterial (8 : Basis)
  | ⟨0,_⟩ => component8_0
  | ⟨1,_⟩ => component8_1
  | ⟨n+2,h⟩ => False.elim (by omega)

theorem energy9_0 : Scalars.energy1958=diagonalScalarEnergy (9 : Basis) 0 := by decide +kernel
def component9_0 : ScalarMaterial (diagonalScalarEnergy (9 : Basis) 0) := energy9_0 ▸ Scalars.material1958
theorem energy9_1 : Scalars.energyD9=diagonalScalarEnergy (9 : Basis) 1 := by decide +kernel
def component9_1 : ScalarMaterial (diagonalScalarEnergy (9 : Basis) 1) := energy9_1 ▸ Scalars.materialD9
def material9 : DiagonalMaterial (9 : Basis)
  | ⟨0,_⟩ => component9_0
  | ⟨1,_⟩ => component9_1
  | ⟨n+2,h⟩ => False.elim (by omega)

theorem energy10_0 : Scalars.energy2120=diagonalScalarEnergy (10 : Basis) 0 := by decide +kernel
def component10_0 : ScalarMaterial (diagonalScalarEnergy (10 : Basis) 0) := energy10_0 ▸ Scalars.material2120
theorem energy10_1 : Scalars.energyD10=diagonalScalarEnergy (10 : Basis) 1 := by decide +kernel
def component10_1 : ScalarMaterial (diagonalScalarEnergy (10 : Basis) 1) := energy10_1 ▸ Scalars.materialD10
def material10 : DiagonalMaterial (10 : Basis)
  | ⟨0,_⟩ => component10_0
  | ⟨1,_⟩ => component10_1
  | ⟨n+2,h⟩ => False.elim (by omega)

theorem energy11_0 : Scalars.energy2158=diagonalScalarEnergy (11 : Basis) 0 := by decide +kernel
def component11_0 : ScalarMaterial (diagonalScalarEnergy (11 : Basis) 0) := energy11_0 ▸ Scalars.material2158
theorem energy11_1 : Scalars.energyD11=diagonalScalarEnergy (11 : Basis) 1 := by decide +kernel
def component11_1 : ScalarMaterial (diagonalScalarEnergy (11 : Basis) 1) := energy11_1 ▸ Scalars.materialD11
def material11 : DiagonalMaterial (11 : Basis)
  | ⟨0,_⟩ => component11_0
  | ⟨1,_⟩ => component11_1
  | ⟨n+2,h⟩ => False.elim (by omega)

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.DiagonalAddresses
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
