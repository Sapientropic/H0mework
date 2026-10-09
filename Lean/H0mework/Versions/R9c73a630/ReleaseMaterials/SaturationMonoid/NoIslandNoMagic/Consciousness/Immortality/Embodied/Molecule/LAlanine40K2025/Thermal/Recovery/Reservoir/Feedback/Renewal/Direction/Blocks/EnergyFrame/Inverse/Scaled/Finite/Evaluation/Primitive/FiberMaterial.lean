import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.RecoveryMaterial
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.DiagonalReverse

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive
open Propagation.Interface Load.Source
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

abbrev PCFiber (k : Sym2 Basis) := {p : PairController // pcOrbit p=k}

structure FiberMaterial (k : Sym2 Basis) where
  one : Matrix (PCFiber k) (PCFiber k) ℂ
  two : Matrix (PCFiber k) (PCFiber k) ℂ
  three : Matrix (PCFiber k) (PCFiber k) ℂ
  one_error : ‖restrict pcOrbit k Phase.pcPolynomial-one‖ ≤ (4/10^24 : ℝ)
  two_error : ‖restrict pcOrbit k Actions.parentPCPolynomial-two‖ ≤ (4/10^24 : ℝ)
  three_error : ‖restrict pcOrbit k Actions.recoveryPCPolynomial-three‖ ≤ (4/10^24 : ℝ)

def ordinaryFiberMaterial (a b : Basis) (distinct : a ≠ b) (M : PCMaterial a b) : FiberMaterial s(a,b) where
  one := (materialPCOne a b M).submatrix (offDiagonalEquiv a b distinct).symm (offDiagonalEquiv a b distinct).symm
  two := (materialPCTwo a b M).submatrix (offDiagonalEquiv a b distinct).symm (offDiagonalEquiv a b distinct).symm
  three := (materialRecoveryPC a b M).submatrix (offDiagonalEquiv a b distinct).symm (offDiagonalEquiv a b distinct).symm
  one_error := SquareRoot.Full.lifted_error (offDiagonalEquiv a b distinct) _ _ _ (material_pc_one_error a b distinct M)
  two_error := SquareRoot.Full.lifted_error (offDiagonalEquiv a b distinct) _ _ _ (material_pc_two_error a b distinct M)
  three_error := SquareRoot.Full.lifted_error (offDiagonalEquiv a b distinct) _ _ _ (material_recovery_pc_error a b distinct M)

def diagonalFiberMaterial (a : Basis) (M : DiagonalMaterial a) : FiberMaterial s(a,a) where
  one := (diagonalMaterialOne a M).submatrix (diagonalEquiv a).symm (diagonalEquiv a).symm
  two := (diagonalMaterialTwo a M).submatrix (diagonalEquiv a).symm (diagonalEquiv a).symm
  three := (diagonalMaterialThree a M).submatrix (diagonalEquiv a).symm (diagonalEquiv a).symm
  one_error := (SquareRoot.Full.lifted_error (diagonalEquiv a) (restrict pcOrbit s(a,a) Phase.pcPolynomial) (diagonalMaterialOne a M) (1/10^24) (diagonal_material_one_error a M)).trans (by norm_num)
  two_error := (SquareRoot.Full.lifted_error (diagonalEquiv a) (restrict pcOrbit s(a,a) Actions.parentPCPolynomial) (diagonalMaterialTwo a M) (1/10^24) (diagonal_material_two_error a M)).trans (by norm_num)
  three_error := (SquareRoot.Full.lifted_error (diagonalEquiv a) (restrict pcOrbit s(a,a) Actions.recoveryPCPolynomial) (diagonalMaterialThree a M) (1/10^24) (diagonal_material_three_error a M)).trans (by norm_num)

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
