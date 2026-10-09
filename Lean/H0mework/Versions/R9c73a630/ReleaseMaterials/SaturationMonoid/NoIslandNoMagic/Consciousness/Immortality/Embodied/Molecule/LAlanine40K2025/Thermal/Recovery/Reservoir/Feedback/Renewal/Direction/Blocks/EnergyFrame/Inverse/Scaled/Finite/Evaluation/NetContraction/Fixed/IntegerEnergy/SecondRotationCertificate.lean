import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.SecondRotationLiteral
set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface

private def secondRotatedPlusInt : MatrixInt LoadPrimitive.NativeIndex
    LoadPrimitive.NativeIndex :=
  rotateInt (fromTable literalSecondFree nativeFin nativeFin)
    (fromTable literalSecondRootPlus nativeFin nativeFin)

private def secondRotatedMinusInt : MatrixInt LoadPrimitive.NativeIndex
    LoadPrimitive.NativeIndex :=
  rotateInt (fromTable literalSecondFree nativeFin nativeFin)
    (fromTable literalSecondRootMinus nativeFin nativeFin)

theorem second_rotated_plus_re :
    (toTable secondRotatedPlusInt nativeFin nativeFin).re=
      literalSecondRotatedPlusRe := by
  decide +kernel

theorem second_rotated_plus_im :
    (toTable secondRotatedPlusInt nativeFin nativeFin).im=
      literalSecondRotatedPlusIm := by
  decide +kernel

theorem second_rotated_minus_re :
    (toTable secondRotatedMinusInt nativeFin nativeFin).re=
      literalSecondRotatedMinusRe := by
  decide +kernel

theorem second_rotated_minus_im :
    (toTable secondRotatedMinusInt nativeFin nativeFin).im=
      literalSecondRotatedMinusIm := by
  decide +kernel

theorem second_rotated_original :
    fromTable literalSecondRotatedPlus nativeFin nativeFin=
      sourceOrdinaryRootRotatedInt (0 : Basis) (2 : Basis) (by decide) ∧
    fromTable literalSecondRotatedMinus nativeFin nativeFin=
      sourceOrdinaryComplementRotatedInt (0 : Basis) (2 : Basis) (by decide) := by
  have plus : toTable secondRotatedPlusInt nativeFin nativeFin=
      literalSecondRotatedPlus :=
    int_table_ext second_rotated_plus_re second_rotated_plus_im
  have minus : toTable secondRotatedMinusInt nativeFin nativeFin=
      literalSecondRotatedMinus :=
    int_table_ext second_rotated_minus_re second_rotated_minus_im
  constructor
  · rw [← plus,from_to_table,secondRotatedPlusInt,second_free_original,
      second_roots_original.1]
    rfl
  · rw [← minus,from_to_table,secondRotatedMinusInt,second_free_original,
      second_roots_original.2]
    rfl

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
