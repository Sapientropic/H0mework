import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.Quantize
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.SourceSlices

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Propagation.Producer
open scoped Matrix BigOperators Matrix.Norms.L2Operator

def pcQ (f : Fin 4 → Scalar.QComplex) : MatrixQ (Fin 4) (Fin 4) :=
  fun i j => ∑ n, (Primitive.pcProjectionQ n i j) • f n

theorem pcQ_value (f : Fin 4 → Scalar.QComplex) : qvalue (pcQ f)=Primitive.pcAssembly (fun n => Scalar.value (f n)) := by
  ext i j
  simp only [pcQ,qvalue,value_sum,Scalar.value_smul,Primitive.pcAssembly,Matrix.sum_apply,Matrix.smul_apply,
    Primitive.pcProjection,Primitive.rationalMatrix,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro k _
  ring

def onePCQ (a b : Basis) (ordered : a < b) : MatrixQ (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  (pcQ (fun n => (Primitive.allOrdinary a b ordered n).one)).submatrix finProdFinEquiv finProdFinEquiv

def twoPCQ (a b : Basis) (ordered : a < b) : MatrixQ (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  (pcQ (fun n => (Primitive.allOrdinary a b ordered n).two)).submatrix finProdFinEquiv finProdFinEquiv

def signPCQ : MatrixQ (Fin 2 × Fin 2) (Fin 2 × Fin 2) := qreal
  (Matrix.diagonal (fun p : Fin 2 × Fin 2 => if p.2=0 then 1 else -1))

def threePCQ (a b : Basis) (ordered : a < b) : MatrixQ (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  let raw := (pcQ (fun n => (Primitive.allOrdinary a b ordered n).three)).submatrix finProdFinEquiv finProdFinEquiv
  qmultiply (qmultiply signPCQ raw) signPCQ

theorem signPCQ_value : qvalue signPCQ=Primitive.smallControllerSign := by
  ext ⟨p,c⟩ ⟨q,d⟩
  fin_cases p <;> fin_cases c <;> fin_cases q <;> fin_cases d <;>
    norm_num [signPCQ,qvalue,qreal,Scalar.value,Primitive.smallControllerSign,Primitive.controllerSign,
      Matrix.diagonal_apply,Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.one_apply]

theorem onePCQ_value (a b : Basis) (ordered : a < b) :
    qvalue (onePCQ a b ordered)=Primitive.computedPC.submatrix (orbitPC a b) (orbitPC a b) := by
  rw [pc_one_ordinary a b ordered,onePCQ,qvalue_submatrix,pcQ_value]
  rfl

theorem twoPCQ_value (a b : Basis) (ordered : a < b) :
    qvalue (twoPCQ a b ordered)=Primitive.computedParentPC.submatrix (orbitPC a b) (orbitPC a b) := by
  rw [pc_two_ordinary a b ordered,twoPCQ,qvalue_submatrix,pcQ_value]
  rfl

theorem threePCQ_value (a b : Basis) (ordered : a < b) :
    qvalue (threePCQ a b ordered)=Primitive.computedRecoveryPC.submatrix (orbitPC a b) (orbitPC a b) := by
  rw [pc_three_ordinary a b ordered,threePCQ,qvalue_multiply,qvalue_multiply,signPCQ_value,qvalue_submatrix,pcQ_value]
  rfl

def diagonalQ (f : Fin 2 → Scalar.QComplex) : MatrixQ (Fin 2) (Fin 2) := fun i j => if i=j then f i else (0,0)

theorem diagonalQ_value (f : Fin 2 → Scalar.QComplex) : qvalue (diagonalQ f)=Matrix.diagonal (fun i => Scalar.value (f i)) := by
  ext i j
  by_cases same : i=j <;> simp [qvalue,diagonalQ,same,Scalar.value]

def oneDiagonalQ (a : Basis) : MatrixQ (Fin 2) (Fin 2) := diagonalQ (fun n => (Primitive.allDiagonal a n).one)

theorem oneDiagonalQ_value (a : Basis) : qvalue (oneDiagonalQ a)=
    Primitive.computedPC.submatrix (fun c => ((a,a),c)) (fun c => ((a,a),c)) := by
  rw [pc_one_diagonal,oneDiagonalQ,diagonalQ_value]
  rfl

def twoDiagonalQ (a : Basis) : MatrixQ (Fin 2) (Fin 2) := diagonalQ (fun n => (Primitive.allDiagonal a n).two)

theorem twoDiagonalQ_value (a : Basis) : qvalue (twoDiagonalQ a)=
    Primitive.computedParentPC.submatrix (fun c => ((a,a),c)) (fun c => ((a,a),c)) := by
  rw [pc_two_diagonal,twoDiagonalQ,diagonalQ_value]
  rfl

def threeDiagonalQ (a : Basis) : MatrixQ (Fin 2) (Fin 2) := diagonalQ (fun n => (Primitive.allDiagonal a n).three)

theorem threeDiagonalQ_value (a : Basis) : qvalue (threeDiagonalQ a)=
    Primitive.computedRecoveryPC.submatrix (fun c => ((a,a),c)) (fun c => ((a,a),c)) := by
  rw [pc_three_diagonal,threeDiagonalQ,diagonalQ_value]
  rfl

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
