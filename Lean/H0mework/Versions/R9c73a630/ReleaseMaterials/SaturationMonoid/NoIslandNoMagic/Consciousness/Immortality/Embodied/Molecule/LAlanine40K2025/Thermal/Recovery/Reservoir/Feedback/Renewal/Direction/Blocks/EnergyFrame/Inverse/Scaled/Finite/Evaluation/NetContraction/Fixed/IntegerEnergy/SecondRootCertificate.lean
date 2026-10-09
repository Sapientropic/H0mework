import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.SecondRootLiteral
set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface

theorem second_root_plus_re :
    (toTable (sourceOrdinaryRootInt (0 : Basis) (2 : Basis) (by decide))
      nativeFin nativeFin).re=literalSecondRootPlusRe := by
  decide +kernel

theorem second_root_plus_im :
    (toTable (sourceOrdinaryRootInt (0 : Basis) (2 : Basis) (by decide))
      nativeFin nativeFin).im=literalSecondRootPlusIm := by
  decide +kernel

theorem second_root_minus_re :
    (toTable (sourceOrdinaryComplementInt (0 : Basis) (2 : Basis) (by decide))
      nativeFin nativeFin).re=literalSecondRootMinusRe := by
  decide +kernel

theorem second_root_minus_im :
    (toTable (sourceOrdinaryComplementInt (0 : Basis) (2 : Basis) (by decide))
      nativeFin nativeFin).im=literalSecondRootMinusIm := by
  decide +kernel

theorem second_roots_original :
    fromTable literalSecondRootPlus nativeFin nativeFin =
      sourceOrdinaryRootInt (0 : Basis) (2 : Basis) (by decide) ∧
    fromTable literalSecondRootMinus nativeFin nativeFin =
      sourceOrdinaryComplementInt (0 : Basis) (2 : Basis) (by decide) := by
  have plus : toTable (sourceOrdinaryRootInt (0 : Basis) (2 : Basis)
      (by decide)) nativeFin nativeFin=literalSecondRootPlus :=
    int_table_ext second_root_plus_re second_root_plus_im
  have minus : toTable (sourceOrdinaryComplementInt (0 : Basis) (2 : Basis)
      (by decide)) nativeFin nativeFin=literalSecondRootMinus :=
    int_table_ext second_root_minus_re second_root_minus_im
  constructor
  · rw [← plus]
    exact from_to_table _ _ _
  · rw [← minus]
    exact from_to_table _ _ _

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
