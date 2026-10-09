import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SIWork.Source

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SIWork
open Inertia.SourceParsing
noncomputable section

def engineLengthResidual : ℝ := lengthMeter-(engineBohrAngstromQ : ℝ)/10^10

theorem engine_energy_rounding_nonzero : engineEnergyResidual ≠ 0 := by
  norm_num [engineEnergyResidual,energyJoule,hbarJouleSecond,massKilogram,lengthMeter,
    engineHartreeJouleQ,hbarJouleSecondQ,massKilogramQ,lengthMeterQ,rationalRead]

theorem engine_energy_rounding_bound : |engineEnergyResidual| < (1 : ℝ)/10^32 := by
  norm_num [engineEnergyResidual,energyJoule,hbarJouleSecond,massKilogram,lengthMeter,
    engineHartreeJouleQ,hbarJouleSecondQ,massKilogramQ,lengthMeterQ,rationalRead]

theorem engine_length_rounding_bound : |engineLengthResidual| < (1 : ℝ)/10^25 := by
  norm_num [engineLengthResidual,lengthMeter,lengthMeterQ,engineBohrAngstromQ,rationalRead]

theorem energy_coordinate_residual (atomicEnergy : ℝ) :
    (engineHartreeJouleQ : ℝ)*atomicEnergy=energyJoule*atomicEnergy+engineEnergyResidual*atomicEnergy := by
  rw [engine_energy_account]
  ring

theorem length_coordinate_residual (atomicLength : ℝ) :
    lengthMeter*atomicLength=((engineBohrAngstromQ : ℝ)/10^10)*atomicLength+engineLengthResidual*atomicLength := by
  unfold engineLengthResidual
  ring

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SIWork
