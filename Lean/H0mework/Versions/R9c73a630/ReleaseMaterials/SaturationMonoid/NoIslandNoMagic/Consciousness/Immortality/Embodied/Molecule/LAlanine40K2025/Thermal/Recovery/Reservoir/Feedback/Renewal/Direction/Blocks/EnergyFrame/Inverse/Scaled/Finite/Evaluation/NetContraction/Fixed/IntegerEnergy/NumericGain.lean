import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.QuadraticConsumer
set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open scoped BigOperators

def literalFirstGainNumeratorInt : Int :=
  ∑ i : Fin 2 × Fin 2,
    (multiply literalFirstNetInt
      (fromTable literalFirstBodyTable pairFin pairFin)).re i i

theorem literal_first_gain_original :
    literalFirstGainNumeratorInt=sourceFirstGainNumeratorInt := by
  simp [literalFirstGainNumeratorInt,sourceFirstGainNumeratorInt,
    sourceFirstEnergyProductInt,literal_first_net_original,literal_first_body_original]

theorem literal_first_gain_exact :
    literalFirstGainNumeratorInt=865472606752044193520814 := by decide +kernel

theorem source_first_gain_exact :
    sourceFirstGainNumeratorInt=865472606752044193520814 := by
  rw [← literal_first_gain_original]
  exact literal_first_gain_exact

theorem source_first_integer_gain_positive : 0 < sourceFirstGainIntQ := by
  rw [sourceFirstGainIntQ,source_first_gain_exact]
  norm_num [scale]

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
