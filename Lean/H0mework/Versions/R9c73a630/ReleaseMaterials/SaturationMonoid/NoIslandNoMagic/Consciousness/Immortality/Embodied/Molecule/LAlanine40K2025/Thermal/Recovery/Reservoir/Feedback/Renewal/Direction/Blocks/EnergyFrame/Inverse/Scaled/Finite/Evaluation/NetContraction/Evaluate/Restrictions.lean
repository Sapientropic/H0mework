import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.SpecNet
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.Received

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Evaluate
open Propagation.Interface Load.Source Fixed
open scoped Matrix

theorem qvalue_injective {α β : Type*} : Function.Injective (qvalue : MatrixQ α β → Matrix α β ℂ) := by
  intro A B same
  funext i j
  exact LoadPrimitive.scalar_value_injective (congrFun (congrFun same i) j)

theorem ordinary_pc_one_restriction (a b : Basis) (ordered : a < b) :
    computedPCQ.submatrix (orbitPC a b) (orbitPC a b)=onePCQ a b ordered := by
  apply qvalue_injective
  rw [qvalue_submatrix,computedPCQ_value,onePCQ_value a b ordered]

theorem ordinary_pc_two_restriction (a b : Basis) (ordered : a < b) :
    computedParentPCQ.submatrix (orbitPC a b) (orbitPC a b)=twoPCQ a b ordered := by
  apply qvalue_injective
  rw [qvalue_submatrix,computedParentPCQ_value,twoPCQ_value a b ordered]

theorem ordinary_pc_three_restriction (a b : Basis) (ordered : a < b) :
    computedRecoveryPCQ.submatrix (orbitPC a b) (orbitPC a b)=threePCQ a b ordered := by
  apply qvalue_injective
  rw [qvalue_submatrix,computedRecoveryPCQ_value,threePCQ_value a b ordered]

theorem ordinary_load_restriction (a b : Basis) (ordered : a < b) :
    computedLoadQ.submatrix (Scaled.Order.orbitPCE a b) (Scaled.Order.orbitPCE a b)=ordinaryLoadQ a b ordered := by
  apply qvalue_injective
  rw [qvalue_submatrix,computedLoadQ_value,ordinaryLoadQ_value a b ordered]

theorem ordinary_root_restriction (a b : Basis) (ordered : a < b) :
    computedRootQ.submatrix (Scaled.Order.orbitPCE a b) (Scaled.Order.orbitPCE a b)=rootOrdinaryQ a b ordered := by
  apply qvalue_injective
  rw [qvalue_submatrix,computedRootQ_value,rootOrdinaryQ_value a b ordered]

theorem ordinary_complement_restriction (a b : Basis) (ordered : a < b) :
    computedComplementQ.submatrix (Scaled.Order.orbitPCE a b) (Scaled.Order.orbitPCE a b)=complementOrdinaryQ a b ordered := by
  apply qvalue_injective
  rw [qvalue_submatrix,computedComplementQ_value,complementOrdinaryQ_value a b ordered]

theorem ordinary_received_restriction (a b : Basis) (ordered : a < b) :
    Spec.receivedWord.submatrix (Scaled.Order.orbitPCE a b) (Scaled.Order.orbitPCE a b)=ordinaryReceivedQ a b ordered := by
  apply qvalue_injective
  rw [qvalue_submatrix,Spec.receivedWord_value,ordinaryReceivedQ_value a b ordered]

theorem diagonal_pc_one_restriction (a : Basis) :
    computedPCQ.submatrix (fun c => ((a,a),c)) (fun c => ((a,a),c))=oneDiagonalQ a := by
  apply qvalue_injective
  rw [qvalue_submatrix,computedPCQ_value,oneDiagonalQ_value a]

theorem diagonal_pc_two_restriction (a : Basis) :
    computedParentPCQ.submatrix (fun c => ((a,a),c)) (fun c => ((a,a),c))=twoDiagonalQ a := by
  apply qvalue_injective
  rw [qvalue_submatrix,computedParentPCQ_value,twoDiagonalQ_value a]

theorem diagonal_pc_three_restriction (a : Basis) :
    computedRecoveryPCQ.submatrix (fun c => ((a,a),c)) (fun c => ((a,a),c))=threeDiagonalQ a := by
  apply qvalue_injective
  rw [qvalue_submatrix,computedRecoveryPCQ_value,threeDiagonalQ_value a]

theorem diagonal_load_restriction (a : Basis) :
    computedLoadQ.submatrix (Scaled.Order.diagonalPCE a) (Scaled.Order.diagonalPCE a)=diagonalLoadQ a := by
  apply qvalue_injective
  rw [qvalue_submatrix,computedLoadQ_value,diagonalLoadQ_value a]

theorem diagonal_received_restriction (a : Basis) :
    Spec.receivedWord.submatrix (Scaled.Order.diagonalPCE a) (Scaled.Order.diagonalPCE a)=diagonalReceivedQ a := by
  apply qvalue_injective
  rw [qvalue_submatrix,Spec.receivedWord_value,diagonalReceivedQ_value a]

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Evaluate
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
