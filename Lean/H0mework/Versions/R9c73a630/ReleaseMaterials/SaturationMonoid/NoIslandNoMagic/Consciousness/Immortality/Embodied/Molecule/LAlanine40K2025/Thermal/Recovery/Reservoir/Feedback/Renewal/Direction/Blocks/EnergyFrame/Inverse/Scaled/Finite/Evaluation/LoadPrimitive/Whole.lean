import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Ordinary
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.MatrixError
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadDiagonal.All
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadDiagonal.MatrixError

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive
open Propagation.Interface Load.Source
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
local instance : Fintype (Sym2 Basis) := Fintype.ofFinite _

abbrev LoadFiber (k : Sym2 Basis) := {p : PairController × Fin 2 // pceOrbit p=k}

structure FiberMaterial (k : Sym2 Basis) where
  matrix : Matrix (LoadFiber k) (LoadFiber k) ℂ
  error : ‖restrict pceOrbit k Actions.loadPolynomial-matrix‖ ≤ (2/10^24 : ℝ)

def ordinaryFiber (a b : Basis) (distinct : a ≠ b) (M : Material a b) : FiberMaterial s(a,b) where
  matrix := (numericLoad a b M).submatrix (Scaled.Order.offDiagonalPCEEquiv a b distinct).symm
    (Scaled.Order.offDiagonalPCEEquiv a b distinct).symm
  error := SquareRoot.Full.lifted_error (Scaled.Order.offDiagonalPCEEquiv a b distinct) _ _ _
    (original_material_load_error a b distinct M)

def diagonalFiber (a : Basis) (M : LoadDiagonal.Material a) : FiberMaterial s(a,a) where
  matrix := (LoadDiagonal.numericLoad a M).submatrix (Scaled.Order.diagonalPCEEquiv a).symm
    (Scaled.Order.diagonalPCEEquiv a).symm
  error := SquareRoot.Full.lifted_error (Scaled.Order.diagonalPCEEquiv a) _ _ _
    (LoadDiagonal.original_material_load_error a M)

def sourceLoadFamily (k : Sym2 Basis) : FiberMaterial k := by
  let pair := Sym2.sortEquiv k
  have source : s(pair.val.1,pair.val.2)=k := Sym2.sortEquiv.symm_apply_apply k
  have material : FiberMaterial s(pair.val.1,pair.val.2) := by
    by_cases same : pair.val.1=pair.val.2
    · rw [← same]
      exact diagonalFiber pair.val.1 (LoadDiagonal.allDiagonal pair.val.1)
    · exact ordinaryFiber pair.val.1 pair.val.2 same
        (allOrdinary pair.val.1 pair.val.2 (lt_of_le_of_ne pair.property same))
  exact source ▸ material

def computedLoad : LoadedJoint := SquareRoot.Full.assemble pceOrbit (fun k => (sourceLoadFamily k).matrix)

theorem original_computed_load_error : ‖Actions.loadPolynomial-computedLoad‖ ≤ (2/10^24 : ℝ) :=
  SquareRoot.Full.assemble_error pceOrbit _ Contraction.load_polynomial_preserves _ _ (by norm_num)
    (fun k => (sourceLoadFamily k).error)

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
