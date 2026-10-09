import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Evaluate.Exchange

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Evaluate
open Propagation.Interface Load.Source Fixed Contraction
open scoped Matrix

variable {α : Type*} [Fintype α]

theorem body_product (k : Sym2 Basis) (e : α ≃ BodyFiber k)
    (A B : MatrixQ (PairController × Fin 2) (PairController × Fin 2)) (kept : Preserves pceOrbit (qvalue A)) :
    (qmultiply A B).submatrix (fun i => (e i).val) (fun i => (e i).val)=
      qmultiply (A.submatrix (fun i => (e i).val) (fun i => (e i).val))
        (B.submatrix (fun i => (e i).val) (fun i => (e i).val)) := by
  apply qvalue_injective
  rw [qvalue_submatrix,qvalue_multiply,qvalue_multiply,qvalue_submatrix,qvalue_submatrix]
  exact Fixed.source_product k e (qvalue A) (qvalue B) kept

omit [Fintype α] in
theorem qadjoint_submatrix (A : MatrixQ (PairController × Fin 2) (PairController × Fin 2)) (f : α → PairController × Fin 2) :
    (qadjoint A).submatrix f f=qadjoint (A.submatrix f f) := rfl

def rotateQ {ι : Type*} [Fintype ι] (U R : MatrixQ ι ι) : MatrixQ ι ι :=
  qmultiply (qmultiply U R) (qadjoint U)

theorem rotateQ_source (k : Sym2 Basis) (e : α ≃ BodyFiber k)
    (R : MatrixQ (PairController × Fin 2) (PairController × Fin 2)) (kept : Preserves pceOrbit (qvalue R)) :
    (Spec.rotatedRoot R).submatrix (fun i => (e i).val) (fun i => (e i).val)=
      rotateQ (Spec.free.submatrix (fun i => (e i).val) (fun i => (e i).val))
        (R.submatrix (fun i => (e i).val) (fun i => (e i).val)) := by
  have free : Preserves pceOrbit (qvalue Spec.free) := by rw [Spec.free_value]; exact free_preserves
  have composed : Preserves pceOrbit (qvalue (qmultiply Spec.free R)) := by
    rw [qvalue_multiply]
    exact preserves_mul free kept
  rw [Spec.rotatedRoot,body_product k e _ _ composed,body_product k e _ _ free,qadjoint_submatrix]
  rfl

theorem ordinary_free_restriction (a b : Basis) (ordered : a < b) :
    Spec.free.submatrix (Scaled.Order.orbitPCE a b) (Scaled.Order.orbitPCE a b)=
      qkron (onePCQ a b ordered) freeEnvironmentQ := by
  apply qvalue_injective
  rw [qvalue_submatrix,Spec.free_value,qvalue_kron,onePCQ_value,freeEnvironmentQ_value]
  exact tensor_slice Primitive.computedPC Phase.environmentPolynomial (orbitPC a b)

theorem diagonal_free_restriction (a : Basis) :
    Spec.free.submatrix (Scaled.Order.diagonalPCE a) (Scaled.Order.diagonalPCE a)=
      qkron (oneDiagonalQ a) freeEnvironmentQ := by
  apply qvalue_injective
  rw [qvalue_submatrix,Spec.free_value,qvalue_kron,oneDiagonalQ_value,freeEnvironmentQ_value]
  exact tensor_slice Primitive.computedPC Phase.environmentPolynomial (fun c => ((a,a),c))

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Evaluate
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
