import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot.Material

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot.Full
open Propagation.Interface Load.Source
noncomputable section

def energy (a : Basis) : ℚ := (energies[a.val]! : ℚ)/10^15
def sine : ℚ := 5159036077299825028754003256706566453832054196327789174851498796483/5159036557536119877776629905638357765734764157265289174851498796483
def cosine : ℚ := 61470244787000579804813269287923546875000000000/142464535914740306008052890816182477027450624746541
def donorEnergy : ℚ := 2*energy 97+3

theorem energy_cast (a : Basis) : (energy a : ℝ)=Donor.calculatedEnergy a := by
  simp only [energy,Donor.calculatedEnergy,Rat.cast_div,Rat.cast_intCast,Rat.cast_pow,Rat.cast_ofNat]
theorem sine_cast : (sine : ℝ)=sineHat := by rw [sine_hat_exact]; norm_num [sine]
theorem cosine_cast : (cosine : ℝ)=cosineHat := by rw [cosine_hat_exact]; norm_num [cosine]
theorem donor_cast : (donorEnergy : ℝ)=numericDonorEnergy := by
  simp only [donorEnergy,numericDonorEnergy,Donor.calculatedTop,Rat.cast_add,Rat.cast_mul,Rat.cast_ofNat,energy_cast]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot.Full
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
