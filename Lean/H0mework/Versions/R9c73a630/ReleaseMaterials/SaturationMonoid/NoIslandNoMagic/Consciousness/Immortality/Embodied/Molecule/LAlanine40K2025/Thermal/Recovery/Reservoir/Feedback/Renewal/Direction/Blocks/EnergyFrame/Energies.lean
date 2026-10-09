import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Data.ResidualColumns
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.ListBounds

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
open Spectral Propagation.Interface

theorem energies_length : energies.length = 98 := by rfl

theorem energies_bound_checked : (energies.map abs).all (· ≤ 19*10^15) = true := by decide +kernel

theorem energy_bound (i : Basis) : |energies[i.val]!| ≤ 19*10^15 :=
  all_abs_bound energies energies_length _ energies_bound_checked i

theorem energy_gap (i : Fin 97) : energies[i.val]!+2*10^12 < energies[i.val+1]! := by
  fin_cases i <;> decide +kernel

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
