import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.SecondEnergyStage
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.UniformGainConsumer

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source

theorem literal_second_gain_exact :
    stagedSecondGainNumeratorInt = 384740080297673072456313 := by decide +kernel

theorem source_second_gain_exact :
    sourceOrdinaryGainNumeratorInt (0 : Basis) (2 : Basis) (by decide) =
      384740080297673072456313 := by
  rw [← staged_second_gain_original]
  exact literal_second_gain_exact

theorem source_second_integer_gain_margin :
    (3/10^7 : ℝ) <
      (sourceOrdinaryGainIntQ (0 : Basis) (2 : Basis) (by decide) : ℝ) := by
  rw [sourceOrdinaryGainIntQ,source_second_gain_exact]
  norm_num [scale]

theorem source_second_original_gain_positive :
    0 < smallGainQ (s((0 : Basis),2)) := by
  have bound := source_ordinary_integer_gain_error 0 2 (by decide)
  have margin := source_second_integer_gain_margin
  have positive : (0 : ℝ) < (smallGainQ (s((0 : Basis),2)) : ℝ) := by
    have sides := (abs_le.mp bound).2
    linarith
  exact_mod_cast positive

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
