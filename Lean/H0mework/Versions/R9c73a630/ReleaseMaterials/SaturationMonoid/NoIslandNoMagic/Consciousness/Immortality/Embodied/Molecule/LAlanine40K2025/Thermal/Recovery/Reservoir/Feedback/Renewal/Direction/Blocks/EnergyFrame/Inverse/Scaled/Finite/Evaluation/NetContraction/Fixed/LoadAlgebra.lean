import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.Algebra
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.SourceSlices

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface
open scoped Matrix BigOperators

def starCoreQ (d : ℚ) : MatrixQ (Fin 3) (Fin 3) := qreal !![0,0,d; 0,0,1; d,1,0]

def starBasisQ (d : ℚ) : Fin 3 → MatrixQ (Fin 3) (Fin 3) :=
  ![qidentity (Fin 3),starCoreQ d,qmultiply (starCoreQ d) (starCoreQ d)]

def starAssemblyQ (d : ℚ) (f : Fin 3 → Scalar.QComplex) : MatrixQ (Fin 3) (Fin 3) :=
  ∑ n, qscale (f n) (starBasisQ d n)

theorem starCoreQ_value (d : ℚ) : qvalue (starCoreQ d)=LoadPrimitive.starCore (d : ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [starCoreQ,qvalue,qreal,Scalar.value,LoadPrimitive.starCore]

theorem starBasisQ_value (d : ℚ) (n : Fin 3) : qvalue (starBasisQ d n)=LoadPrimitive.starBasis (d : ℂ) n := by
  fin_cases n <;> simp [starBasisQ,LoadPrimitive.starBasis,qvalue_identity,starCoreQ_value,qvalue_multiply,pow_two]

theorem starAssemblyQ_value (d : ℚ) (f : Fin 3 → Scalar.QComplex) :
    qvalue (starAssemblyQ d f)=LoadPrimitive.starAssembly (d : ℂ) (fun n => Scalar.value (f n)) := by
  simp only [starAssemblyQ,qvalue_sum,qvalue_scale,starBasisQ_value,LoadPrimitive.starAssembly]

def rawLoadQ (M N : MatrixQ (Fin 3) (Fin 3)) (a b : Scalar.QComplex) : MatrixQ LoadPrimitive.RawIndex LoadPrimitive.RawIndex :=
  Matrix.fromBlocks M 0 0 (Matrix.fromBlocks (qscalar (Fin 1) a) 0 0 (Matrix.fromBlocks (qscalar (Fin 1) b) 0 0 N))

theorem rawLoadQ_value (M N : MatrixQ (Fin 3) (Fin 3)) (a b : Scalar.QComplex) :
    qvalue (rawLoadQ M N a b)=LoadPrimitive.raw (qvalue M) (qvalue N) (Scalar.value a) (Scalar.value b) := by
  simp only [rawLoadQ,qvalue_blocks,qvalue_scalar,LoadPrimitive.raw]

def spliceLoadQ (M N : MatrixQ (Fin 3) (Fin 3)) (a b : Scalar.QComplex) : MatrixQ (Fin 8) (Fin 8) :=
  (rawLoadQ M N a b).submatrix LoadPrimitive.joinEquiv.symm LoadPrimitive.joinEquiv.symm

theorem spliceLoadQ_value (M N : MatrixQ (Fin 3) (Fin 3)) (a b : Scalar.QComplex) :
    qvalue (spliceLoadQ M N a b)=LoadPrimitive.splice (qvalue M) (qvalue N) (Scalar.value a) (Scalar.value b) := by
  rw [spliceLoadQ,qvalue_submatrix,rawLoadQ_value]
  rfl

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
