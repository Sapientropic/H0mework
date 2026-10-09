import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot.Full.Assembly
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot.Full.OrdinaryPair
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot.Full.DiagonalPair

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot.Full
open Propagation.Interface Load.Source Scaled.Order
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

abbrev SourceFiber (k : Sym2 Basis) := {p : PairController × Fin 2 // pceOrbit p=k}

structure FiberRoots (k : Sym2 Basis) where
  root : Matrix (SourceFiber k) (SourceFiber k) ℂ
  complement : Matrix (SourceFiber k) (SourceFiber k) ℂ
  root_error : ‖restrict pceOrbit k (CFC.sqrt finiteEffect)-root‖ ≤ (2/10^7 : ℝ)
  complement_error : ‖restrict pceOrbit k (CFC.sqrt (1-finiteEffect))-complement‖ ≤ (2/10^7 : ℝ)

def offFiber (a b : Basis) (distinct : a ≠ b) (G : OrdinaryPair a b) : FiberRoots s(a,b) where
  root := (G.1.value.submatrix tripleIndex tripleIndex).submatrix
    (offDiagonalPCEEquiv a b distinct).symm (offDiagonalPCEEquiv a b distinct).symm
  complement := (G.2.value.submatrix tripleIndex tripleIndex).submatrix
    (offDiagonalPCEEquiv a b distinct).symm (offDiagonalPCEEquiv a b distinct).symm
  root_error := lifted_error (offDiagonalPCEEquiv a b distinct) _ _ _ (G.source_bounds distinct).1
  complement_error := lifted_error (offDiagonalPCEEquiv a b distinct) _ _ _ (G.source_bounds distinct).2

def diagonalFiber (a : Fin 97) (G : DiagonalPair a) : FiberRoots s(a.castSucc,a.castSucc) where
  root := (G.1.value.submatrix pairIndex pairIndex).submatrix
    (diagonalPCEEquiv a.castSucc).symm (diagonalPCEEquiv a.castSucc).symm
  complement := (G.2.value.submatrix pairIndex pairIndex).submatrix
    (diagonalPCEEquiv a.castSucc).symm (diagonalPCEEquiv a.castSucc).symm
  root_error := lifted_error (diagonalPCEEquiv a.castSucc) _ _ _ G.source_bounds.1
  complement_error := lifted_error (diagonalPCEEquiv a.castSucc) _ _ _ G.source_bounds.2

def donorFiber (G : DonorPair) : FiberRoots s(97,97) where
  root := (G.1.value.submatrix pairIndex pairIndex).submatrix (diagonalPCEEquiv 97).symm (diagonalPCEEquiv 97).symm
  complement := (G.2.value.submatrix pairIndex pairIndex).submatrix (diagonalPCEEquiv 97).symm (diagonalPCEEquiv 97).symm
  root_error := lifted_error (diagonalPCEEquiv 97) _ _ _ G.source_bounds.1
  complement_error := lifted_error (diagonalPCEEquiv 97) _ _ _ G.source_bounds.2

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot.Full
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
