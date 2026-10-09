import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.SecondNineCertificate

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source

def secondWeakPulseTable : IntTable 64 64 :=
  toTable (sourceOrdinaryWeakPulseInt (0 : Basis) (2 : Basis) (by decide))
    pointerFin pointerFin

def stagedSecondWeakTable : IntTable 64 8 :=
  applyActionTable secondWeakPulseTable literalSecondNineTable

theorem staged_second_weak_original :
    fromTable stagedSecondWeakTable pointerFin nativeFin =
      sourceOrdinaryAfterWeakInt (0 : Basis) (2 : Basis) (by decide) := by
  rw [stagedSecondWeakTable,apply_action_table_original,
    secondWeakPulseTable,from_to_table,literal_second_nine_original]
  rfl

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
