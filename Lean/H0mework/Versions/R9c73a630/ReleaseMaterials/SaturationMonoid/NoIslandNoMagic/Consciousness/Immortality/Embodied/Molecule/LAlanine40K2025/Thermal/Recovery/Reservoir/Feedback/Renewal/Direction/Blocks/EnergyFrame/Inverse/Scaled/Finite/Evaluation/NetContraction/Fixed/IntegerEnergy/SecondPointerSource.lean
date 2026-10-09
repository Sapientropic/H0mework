import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.SecondRotationConsumer
set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Contraction
noncomputable section

def secondLiteralRootRoleInt : MatrixInt OrdinaryFull OrdinaryFull :=
  roleBlocksInt
    (bodyLiftIdentityInt (fromTable literalSecondRotatedPlus nativeFin nativeFin))
    (donorLiftIdentityInt sourceDonorRootRotatedInt)

def secondLiteralComplementRoleInt : MatrixInt OrdinaryFull OrdinaryFull :=
  roleBlocksInt
    (bodyLiftIdentityInt (fromTable literalSecondRotatedMinus nativeFin nativeFin))
    (donorLiftIdentityInt sourceDonorComplementRotatedInt)

def secondLiteralPointerInt : MatrixInt (OrdinaryFull ⊕ OrdinaryFull)
    (OrdinaryFull ⊕ OrdinaryFull) :=
  intFourBlocks secondLiteralRootRoleInt (intNeg secondLiteralComplementRoleInt)
    secondLiteralComplementRoleInt secondLiteralRootRoleInt

theorem second_pointer_original :
    secondLiteralPointerInt=sourceOrdinaryPointerInt
      (0 : Basis) (2 : Basis) (by decide) := by
  rw [secondLiteralPointerInt,secondLiteralRootRoleInt,
    secondLiteralComplementRoleInt,second_rotated_original.1,
    second_rotated_original.2]
  rfl

def secondLiteralColumnsInt : MatrixInt (OrdinaryFull ⊕ OrdinaryFull)
    LoadPrimitive.NativeIndex :=
  multiply (submatrix secondLiteralPointerInt id Sum.inl)
    (sourceOrdinarySupplyChargedInt (0 : Basis) (2 : Basis) (by decide))

theorem second_columns_original :
    secondLiteralColumnsInt=sourceOrdinaryColumnsInt
      (0 : Basis) (2 : Basis) (by decide) := by
  rw [secondLiteralColumnsInt,second_pointer_original]
  rfl

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
