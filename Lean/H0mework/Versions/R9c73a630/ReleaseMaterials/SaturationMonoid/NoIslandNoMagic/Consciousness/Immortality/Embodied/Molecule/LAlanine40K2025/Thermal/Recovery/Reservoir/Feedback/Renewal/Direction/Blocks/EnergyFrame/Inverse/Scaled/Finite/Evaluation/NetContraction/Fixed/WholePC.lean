import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.Assemble
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.PC

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction
open scoped Matrix

structure PCFamilyQ (k : Sym2 Basis) where
  one : MatrixQ (Primitive.PCFiber k) (Primitive.PCFiber k)
  two : MatrixQ (Primitive.PCFiber k) (Primitive.PCFiber k)
  three : MatrixQ (Primitive.PCFiber k) (Primitive.PCFiber k)
  one_source : qvalue one=(Primitive.sourcePCFamily k).one
  two_source : qvalue two=(Primitive.sourcePCFamily k).two
  three_source : qvalue three=(Primitive.sourcePCFamily k).three

def ordinaryPCFamilyQ (a b : Basis) (ordered : a < b) : PCFamilyQ s(a,b) where
  one := (onePCQ a b ordered).submatrix (offDiagonalEquiv a b ordered.ne).symm (offDiagonalEquiv a b ordered.ne).symm
  two := (twoPCQ a b ordered).submatrix (offDiagonalEquiv a b ordered.ne).symm (offDiagonalEquiv a b ordered.ne).symm
  three := (threePCQ a b ordered).submatrix (offDiagonalEquiv a b ordered.ne).symm (offDiagonalEquiv a b ordered.ne).symm
  one_source := by rw [qvalue_submatrix,onePCQ_value,pc_one_ordinary a b ordered,pc_family_ordinary a b ordered]; rfl
  two_source := by rw [qvalue_submatrix,twoPCQ_value,pc_two_ordinary a b ordered,pc_family_ordinary a b ordered]; rfl
  three_source := by rw [qvalue_submatrix,threePCQ_value,pc_three_ordinary a b ordered,pc_family_ordinary a b ordered]; rfl

def diagonalPCFamilyQ (a : Basis) : PCFamilyQ s(a,a) where
  one := (oneDiagonalQ a).submatrix (diagonalEquiv a).symm (diagonalEquiv a).symm
  two := (twoDiagonalQ a).submatrix (diagonalEquiv a).symm (diagonalEquiv a).symm
  three := (threeDiagonalQ a).submatrix (diagonalEquiv a).symm (diagonalEquiv a).symm
  one_source := by rw [qvalue_submatrix,oneDiagonalQ_value,pc_one_diagonal,pc_family_diagonal]; rfl
  two_source := by rw [qvalue_submatrix,twoDiagonalQ_value,pc_two_diagonal,pc_family_diagonal]; rfl
  three_source := by rw [qvalue_submatrix,threeDiagonalQ_value,pc_three_diagonal,pc_family_diagonal]; rfl

def pcFamilyQ (k : Sym2 Basis) : PCFamilyQ k := by
  let p := Sym2.sortEquiv k
  have same : s(p.val.1,p.val.2)=k := Sym2.sortEquiv.symm_apply_apply k
  have material : PCFamilyQ s(p.val.1,p.val.2) := by
    by_cases eq : p.val.1=p.val.2
    · rw [← eq]
      exact diagonalPCFamilyQ p.val.1
    · exact ordinaryPCFamilyQ p.val.1 p.val.2 (lt_of_le_of_ne p.property eq)
  exact same ▸ material

def computedPCQ : MatrixQ Load.Source.PairController Load.Source.PairController := assembleQ pcOrbit (fun k => (pcFamilyQ k).one)
def computedParentPCQ : MatrixQ Load.Source.PairController Load.Source.PairController := assembleQ pcOrbit (fun k => (pcFamilyQ k).two)
def computedRecoveryPCQ : MatrixQ Load.Source.PairController Load.Source.PairController := assembleQ pcOrbit (fun k => (pcFamilyQ k).three)

noncomputable section
local instance : Fintype (Sym2 Basis) := Fintype.ofFinite _

theorem computedPCQ_value : qvalue computedPCQ=Primitive.computedPC := by
  rw [computedPCQ,qvalue_assemble]
  exact congrArg (SquareRoot.Full.assemble pcOrbit) (funext (fun k => (pcFamilyQ k).one_source))

theorem computedParentPCQ_value : qvalue computedParentPCQ=Primitive.computedParentPC := by
  rw [computedParentPCQ,qvalue_assemble]
  exact congrArg (SquareRoot.Full.assemble pcOrbit) (funext (fun k => (pcFamilyQ k).two_source))

theorem computedRecoveryPCQ_value : qvalue computedRecoveryPCQ=Primitive.computedRecoveryPC := by
  rw [computedRecoveryPCQ,qvalue_assemble]
  exact congrArg (SquareRoot.Full.assemble pcOrbit) (funext (fun k => (pcFamilyQ k).three_source))

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
