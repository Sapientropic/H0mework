import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.SecondFreeLiteral
set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface

theorem second_free_re :
    (toTable (sourceOrdinaryFreeInt (0 : Basis) (2 : Basis) (by decide))
      nativeFin nativeFin).re=literalSecondFreeRe := by
  decide +kernel

theorem second_free_im :
    (toTable (sourceOrdinaryFreeInt (0 : Basis) (2 : Basis) (by decide))
      nativeFin nativeFin).im=literalSecondFreeIm := by
  decide +kernel

theorem second_free_original :
    fromTable literalSecondFree nativeFin nativeFin=
      sourceOrdinaryFreeInt (0 : Basis) (2 : Basis) (by decide) := by
  have h : toTable (sourceOrdinaryFreeInt (0 : Basis) (2 : Basis)
      (by decide)) nativeFin nativeFin=literalSecondFree :=
    int_table_ext second_free_re second_free_im
  rw [← h]
  exact from_to_table _ _ _

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
