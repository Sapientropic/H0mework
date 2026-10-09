import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.Phase
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.Load
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.Roots

set_option autoImplicit false
set_option maxRecDepth 4096
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Contraction
open scoped Matrix BigOperators

variable {α : Type*}

def liftedAddress (f : α → PairController) (i : α × Fin 2) : PairController × Fin 2 := (f i.1,i.2)

theorem tensor_slice (A : Matrix PairController PairController ℂ) (E : Matrix (Fin 2) (Fin 2) ℂ) (f : α → PairController) :
    (Matrix.kronecker A E).submatrix (liftedAddress f) (liftedAddress f)=Matrix.kronecker (A.submatrix f f) E := rfl

theorem source_product [Fintype α] (k : Sym2 Basis) (e : α ≃ BodyFiber k) (A B : LoadedJoint)
    (left : Preserves pceOrbit A) :
    (A*B).submatrix (fun i => (e i).val) (fun i => (e i).val)=
      A.submatrix (fun i => (e i).val) (fun i => (e i).val)*B.submatrix (fun i => (e i).val) (fun i => (e i).val) := by
  have full := congrArg (fun M : Matrix (BodyFiber k) (BodyFiber k) ℂ => M.submatrix e e) (restrict_mul left B k)
  have rearranged := Matrix.submatrix_mul_equiv (restrict pceOrbit k A) (restrict pceOrbit k B) e e e
  have answer := full.trans rearranged.symm
  simpa only [restrict,Matrix.submatrix_submatrix,Function.comp_def] using answer

def receivedQ {ι : Type*} [Fintype ι]
    (recovery parent : MatrixQ ι ι) (load : MatrixQ (ι × Fin 2) (ι × Fin 2)) : MatrixQ (ι × Fin 2) (ι × Fin 2) :=
  qmultiply (qmultiply (qkron recovery recoveryEnvironmentQ) load) (qkron parent (qidentity (Fin 2)))

theorem receivedQ_value {ι : Type*} [Fintype ι]
    (recovery parent : MatrixQ ι ι) (load : MatrixQ (ι × Fin 2) (ι × Fin 2)) :
    qvalue (receivedQ recovery parent load)=
      Matrix.kronecker (qvalue recovery) Actions.recoveryEnvironmentPolynomial*qvalue load*
        Matrix.kronecker (qvalue parent) (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  simp only [receivedQ,qvalue_multiply,qvalue_kron,recoveryEnvironmentQ_value,qvalue_identity]

def ordinaryReceivedQ (a b : Basis) (ordered : a < b) : MatrixQ LoadPrimitive.NativeIndex LoadPrimitive.NativeIndex :=
  receivedQ (threePCQ a b ordered) (twoPCQ a b ordered) (ordinaryLoadQ a b ordered)

def diagonalReceivedQ (a : Basis) : MatrixQ (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  receivedQ (threeDiagonalQ a) (twoDiagonalQ a) (diagonalLoadQ a)

theorem ordinary_received_source (a b : Basis) (ordered : a < b) :
    LoadExecution.receivedWord.submatrix (Scaled.Order.orbitPCE a b) (Scaled.Order.orbitPCE a b)=
      Matrix.kronecker (Primitive.computedRecoveryPC.submatrix (orbitPC a b) (orbitPC a b)) Actions.recoveryEnvironmentPolynomial*
        LoadPrimitive.computedLoad.submatrix (Scaled.Order.orbitPCE a b) (Scaled.Order.orbitPCE a b)*
        Matrix.kronecker (Primitive.computedParentPC.submatrix (orbitPC a b) (orbitPC a b)) (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have first := source_product s(a,b) (Scaled.Order.offDiagonalPCEEquiv a b ordered.ne)
    (PCExecution.recovery*LoadPrimitive.computedLoad) PCExecution.parent (preserves_mul recovery_preserves load_preserves)
  have second := source_product s(a,b) (Scaled.Order.offDiagonalPCEEquiv a b ordered.ne)
    PCExecution.recovery LoadPrimitive.computedLoad recovery_preserves
  have address : (fun i => (Scaled.Order.offDiagonalPCEEquiv a b ordered.ne i).val)=liftedAddress (orbitPC a b) := rfl
  rw [address] at first second
  change (PCExecution.recovery*LoadPrimitive.computedLoad*PCExecution.parent).submatrix (liftedAddress (orbitPC a b)) (liftedAddress (orbitPC a b))=_
  rw [first,second]
  rw [PCExecution.recovery,PCExecution.parent,tensor_slice,tensor_slice]
  rw [show liftedAddress (orbitPC a b)=Scaled.Order.orbitPCE a b from rfl]

theorem ordinaryReceivedQ_value (a b : Basis) (ordered : a < b) :
    qvalue (ordinaryReceivedQ a b ordered)=LoadExecution.receivedWord.submatrix (Scaled.Order.orbitPCE a b) (Scaled.Order.orbitPCE a b) := by
  rw [ordinary_received_source a b ordered,ordinaryReceivedQ,receivedQ_value,threePCQ_value,twoPCQ_value,ordinaryLoadQ_value]

theorem diagonal_received_source (a : Basis) :
    LoadExecution.receivedWord.submatrix (Scaled.Order.diagonalPCE a) (Scaled.Order.diagonalPCE a)=
      Matrix.kronecker (Primitive.computedRecoveryPC.submatrix (fun c => ((a,a),c)) (fun c => ((a,a),c))) Actions.recoveryEnvironmentPolynomial*
        LoadPrimitive.computedLoad.submatrix (Scaled.Order.diagonalPCE a) (Scaled.Order.diagonalPCE a)*
        Matrix.kronecker (Primitive.computedParentPC.submatrix (fun c => ((a,a),c)) (fun c => ((a,a),c))) (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have first := source_product s(a,a) (Scaled.Order.diagonalPCEEquiv a)
    (PCExecution.recovery*LoadPrimitive.computedLoad) PCExecution.parent (preserves_mul recovery_preserves load_preserves)
  have second := source_product s(a,a) (Scaled.Order.diagonalPCEEquiv a)
    PCExecution.recovery LoadPrimitive.computedLoad recovery_preserves
  have address : (fun i => (Scaled.Order.diagonalPCEEquiv a i).val)=liftedAddress (fun c => ((a,a),c)) := rfl
  rw [address] at first second
  change (PCExecution.recovery*LoadPrimitive.computedLoad*PCExecution.parent).submatrix (liftedAddress (fun c => ((a,a),c))) (liftedAddress (fun c => ((a,a),c)))=_
  rw [first,second]
  rw [PCExecution.recovery,PCExecution.parent,tensor_slice,tensor_slice]
  rw [show liftedAddress (fun c => ((a,a),c))=Scaled.Order.diagonalPCE a from rfl]

theorem diagonalReceivedQ_value (a : Basis) :
    qvalue (diagonalReceivedQ a)=LoadExecution.receivedWord.submatrix (Scaled.Order.diagonalPCE a) (Scaled.Order.diagonalPCE a) := by
  rw [diagonal_received_source a,diagonalReceivedQ,receivedQ_value,threeDiagonalQ_value,twoDiagonalQ_value,diagonalLoadQ_value]

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
