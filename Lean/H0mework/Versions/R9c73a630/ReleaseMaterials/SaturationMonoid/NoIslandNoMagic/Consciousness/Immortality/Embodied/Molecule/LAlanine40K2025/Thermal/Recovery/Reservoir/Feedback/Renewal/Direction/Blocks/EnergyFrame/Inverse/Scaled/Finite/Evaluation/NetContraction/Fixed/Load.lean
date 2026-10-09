import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.LoadAlgebra

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface
open scoped Matrix BigOperators

def loadBlockQ (a b : Basis) (M : LoadPrimitive.Material a b) : MatrixQ (Fin 8) (Fin 8) :=
  spliceLoadQ (starAssemblyQ (LoadPrimitive.sourceDelta a b) M.plus)
    (starAssemblyQ (LoadPrimitive.sourceDelta a b) M.minus) M.upper M.lower

theorem loadBlockQ_value (a b : Basis) (M : LoadPrimitive.Material a b) :
    qvalue (loadBlockQ a b M)=LoadPrimitive.numericBlock a b M := by
  simp only [loadBlockQ,spliceLoadQ_value,starAssemblyQ_value,LoadPrimitive.numericBlock]

def loadMaterialQ (a b : Basis) (M : LoadPrimitive.Material a b) : MatrixQ LoadPrimitive.NativeIndex LoadPrimitive.NativeIndex :=
  (qmultiply (qmultiply (qreal LoadPrimitive.basisQ) (loadBlockQ a b M)) (qreal LoadPrimitive.inverseQ)).submatrix
    LoadPrimitive.flatten LoadPrimitive.flatten

theorem loadMaterialQ_value (a b : Basis) (M : LoadPrimitive.Material a b) :
    qvalue (loadMaterialQ a b M)=LoadPrimitive.numericLoad a b M := by
  rw [loadMaterialQ,qvalue_submatrix,qvalue_multiply,qvalue_multiply,loadBlockQ_value,qvalue_real,qvalue_real]
  rfl

def ordinaryLoadQ (a b : Basis) (ordered : a < b) : MatrixQ LoadPrimitive.NativeIndex LoadPrimitive.NativeIndex :=
  loadMaterialQ a b (LoadPrimitive.allOrdinary a b ordered)

theorem ordinaryLoadQ_value (a b : Basis) (ordered : a < b) :
    qvalue (ordinaryLoadQ a b ordered)=LoadPrimitive.computedLoad.submatrix (Scaled.Order.orbitPCE a b) (Scaled.Order.orbitPCE a b) := by
  rw [load_ordinary a b ordered]
  exact loadMaterialQ_value _ _ _

def middleLoadQ (f : Fin 3 → Scalar.QComplex) : MatrixQ (Fin 2) (Fin 2) :=
  !![f 0+f 2,f 1; f 1,f 0+f 2]

theorem middleLoadQ_value (f : Fin 3 → Scalar.QComplex) :
    qvalue (middleLoadQ f)=LoadDiagonal.middle (fun n => Scalar.value (f n)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [middleLoadQ,qvalue,Scalar.value_add,LoadDiagonal.middle]

def rawDiagonalQ (a : Basis) (M : LoadDiagonal.Material a) : MatrixQ LoadDiagonal.RawIndex LoadDiagonal.RawIndex :=
  Matrix.fromBlocks (qscalar (Fin 1) M.lower) 0 0
    (Matrix.fromBlocks (middleLoadQ ![M.centre,M.beta,M.gamma]) 0 0 (qscalar (Fin 1) M.upper))

theorem rawDiagonalQ_value (a : Basis) (M : LoadDiagonal.Material a) :
    qvalue (rawDiagonalQ a M)=LoadDiagonal.numericRaw a M := by
  simp only [rawDiagonalQ,qvalue_blocks,qvalue_scalar,middleLoadQ_value,LoadDiagonal.numericRaw,LoadDiagonal.raw,LoadDiagonal.numericMiddle]
  rfl

def diagonalLoadQ (a : Basis) : MatrixQ (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  (rawDiagonalQ a (LoadDiagonal.allDiagonal a)).submatrix LoadDiagonal.toNative.symm LoadDiagonal.toNative.symm

theorem diagonalLoadQ_value (a : Basis) :
    qvalue (diagonalLoadQ a)=LoadPrimitive.computedLoad.submatrix (Scaled.Order.diagonalPCE a) (Scaled.Order.diagonalPCE a) := by
  rw [load_diagonal,diagonalLoadQ,qvalue_submatrix,rawDiagonalQ_value]
  rfl

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
