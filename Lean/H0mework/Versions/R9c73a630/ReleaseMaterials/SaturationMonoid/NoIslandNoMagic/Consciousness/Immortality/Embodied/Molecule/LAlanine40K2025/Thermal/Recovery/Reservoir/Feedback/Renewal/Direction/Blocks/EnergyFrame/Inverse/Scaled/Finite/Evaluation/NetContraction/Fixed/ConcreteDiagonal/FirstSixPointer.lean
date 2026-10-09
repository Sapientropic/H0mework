import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.ConcreteDiagonal.Roots

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Contraction Evaluate
open scoped Matrix BigOperators

def firstSixBasis (a : Fin 6) : Basis := ⟨a.val,by omega⟩

theorem first_six_different (a : Fin 6) : firstSixBasis a ≠ 97 := by
  intro h
  have equal : a.val = 97 := congrArg Fin.val h
  have limit := a.isLt
  omega

def firstSixRootRotatedQ (a : Fin 6) : MatrixQ (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  rotateQ (qkron (oneDiagonalQ (firstSixBasis a)) freeEnvironmentQ)
    (firstSixRootQ a)
def firstSixComplementRotatedQ (a : Fin 6) :
    MatrixQ (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  rotateQ (qkron (oneDiagonalQ (firstSixBasis a)) freeEnvironmentQ)
    (firstSixComplementQ a)
def literalDonorRootRotatedQ : MatrixQ (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  rotateQ (qkron (oneDiagonalQ 97) freeEnvironmentQ) literalDonorRootQ
def literalDonorComplementRotatedQ : MatrixQ (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  rotateQ (qkron (oneDiagonalQ 97) freeEnvironmentQ) literalDonorComplementQ

def firstSixRootRoleQ (a : Fin 6) : MatrixQ DiagonalFull DiagonalFull :=
  roleBlocksQ
    (bodyLiftQ (firstSixRootRotatedQ a) (qidentity (Fin 2)))
    (donorLiftQ literalDonorRootRotatedQ (qidentity (Fin 2)))
def firstSixComplementRoleQ (a : Fin 6) : MatrixQ DiagonalFull DiagonalFull :=
  roleBlocksQ
    (bodyLiftQ (firstSixComplementRotatedQ a) (qidentity (Fin 2)))
    (donorLiftQ literalDonorComplementRotatedQ (qidentity (Fin 2)))

def firstSixPointerQ (a : Fin 6) :
    MatrixQ (DiagonalFull ⊕ DiagonalFull) (DiagonalFull ⊕ DiagonalFull) :=
  Matrix.fromBlocks (firstSixRootRoleQ a) (-(firstSixComplementRoleQ a))
    (firstSixComplementRoleQ a) (firstSixRootRoleQ a)

theorem first_six_pointer_source (a : Fin 6) :
    diagonalPointerQ (firstSixBasis a) (first_six_different a) =
      firstSixPointerQ a := by
  fin_cases a <;> rfl

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
