import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.Quantize
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.RootSlices

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface
open scoped Matrix BigOperators Matrix.Norms.L2Operator

variable {α : Type*} [Fintype α]

def rootGramQ {A B : Matrix α α ℚ} (G : SquareRoot.RootGram A B) : MatrixQ α α :=
  qmultiply (fun i j => (G.realPart i j,G.imagPart i j))
    (qadjoint (fun i j => (G.realPart i j,G.imagPart i j)))

theorem rootGramQ_value {A B : Matrix α α ℚ} (G : SquareRoot.RootGram A B) :
    qvalue (rootGramQ G)=G.value := by
  let F : MatrixQ α α := fun i j => (G.realPart i j,G.imagPart i j)
  have first := qvalue_multiply F (qadjoint F)
  have second := congrArg (fun B : Matrix α α ℂ => qvalue F*B) (qvalue_adjoint F)
  exact first.trans second

noncomputable def rootOrdinaryQ (a b : Basis) (ordered : a < b) : MatrixQ ((Fin 2 × Fin 2) × Fin 2) ((Fin 2 × Fin 2) × Fin 2) :=
  (rootGramQ (SquareRoot.Full.allOrdinary a b ordered).1).submatrix tripleIndex tripleIndex

theorem rootOrdinaryQ_value (a b : Basis) (ordered : a < b) :
    qvalue (rootOrdinaryQ a b ordered)=SquareRoot.Full.sourceRoot.submatrix (Scaled.Order.orbitPCE a b) (Scaled.Order.orbitPCE a b) := by
  rw [root_ordinary a b ordered,rootOrdinaryQ,qvalue_submatrix,rootGramQ_value]

noncomputable def rootDiagonalQ (a : Fin 97) : MatrixQ (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  (rootGramQ (SquareRoot.Full.allDiagonal a).1).submatrix SquareRoot.Full.pairIndex SquareRoot.Full.pairIndex

theorem rootDiagonalQ_value (a : Fin 97) :
    qvalue (rootDiagonalQ a)=SquareRoot.Full.sourceRoot.submatrix (Scaled.Order.diagonalPCE a.castSucc) (Scaled.Order.diagonalPCE a.castSucc) := by
  rw [root_diagonal a,rootDiagonalQ,qvalue_submatrix,rootGramQ_value]

noncomputable def rootDonorQ : MatrixQ (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  (rootGramQ SquareRoot.Full.paidDonor.1).submatrix SquareRoot.Full.pairIndex SquareRoot.Full.pairIndex

theorem rootDonorQ_value : qvalue rootDonorQ=SquareRoot.Full.sourceRoot.submatrix (Scaled.Order.diagonalPCE 97) (Scaled.Order.diagonalPCE 97) := by
  rw [root_donor,rootDonorQ,qvalue_submatrix,rootGramQ_value]

noncomputable def complementOrdinaryQ (a b : Basis) (ordered : a < b) : MatrixQ ((Fin 2 × Fin 2) × Fin 2) ((Fin 2 × Fin 2) × Fin 2) :=
  (rootGramQ (SquareRoot.Full.allOrdinary a b ordered).2).submatrix tripleIndex tripleIndex

theorem complementOrdinaryQ_value (a b : Basis) (ordered : a < b) :
    qvalue (complementOrdinaryQ a b ordered)=SquareRoot.Full.sourceComplement.submatrix (Scaled.Order.orbitPCE a b) (Scaled.Order.orbitPCE a b) := by
  rw [complement_ordinary a b ordered,complementOrdinaryQ,qvalue_submatrix,rootGramQ_value]

noncomputable def complementDiagonalQ (a : Fin 97) : MatrixQ (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  (rootGramQ (SquareRoot.Full.allDiagonal a).2).submatrix SquareRoot.Full.pairIndex SquareRoot.Full.pairIndex

theorem complementDiagonalQ_value (a : Fin 97) :
    qvalue (complementDiagonalQ a)=SquareRoot.Full.sourceComplement.submatrix (Scaled.Order.diagonalPCE a.castSucc) (Scaled.Order.diagonalPCE a.castSucc) := by
  rw [complement_diagonal a,complementDiagonalQ,qvalue_submatrix,rootGramQ_value]

noncomputable def complementDonorQ : MatrixQ (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  (rootGramQ SquareRoot.Full.paidDonor.2).submatrix SquareRoot.Full.pairIndex SquareRoot.Full.pairIndex

theorem complementDonorQ_value : qvalue complementDonorQ=SquareRoot.Full.sourceComplement.submatrix (Scaled.Order.diagonalPCE 97) (Scaled.Order.diagonalPCE 97) := by
  rw [complement_donor,complementDonorQ,qvalue_submatrix,rootGramQ_value]

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
