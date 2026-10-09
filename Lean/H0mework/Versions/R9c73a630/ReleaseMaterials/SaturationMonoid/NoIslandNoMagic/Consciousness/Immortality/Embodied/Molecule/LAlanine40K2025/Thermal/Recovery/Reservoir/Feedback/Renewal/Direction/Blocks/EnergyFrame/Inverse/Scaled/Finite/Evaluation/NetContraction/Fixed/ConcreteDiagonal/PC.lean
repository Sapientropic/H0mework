import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.ConcreteOrdinary.PC
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.HeadMass.DiagonalProgram

set_option autoImplicit false
set_option maxRecDepth 4096
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Collision Contraction Evaluate
open scoped Matrix BigOperators
noncomputable section

private theorem pc_lift_as_local_diagonal : Spec.pcLift =
    localMatrixQ (qkron hamiltonianQ (qidentity (Fin 2))) (qidentity PairController) := by
  apply Evaluate.qvalue_injective
  rw [Spec.pcLift_value,localMatrixQ_value,qvalue_kron,qvalue_identity,
    hamiltonianQ_value,qvalue_identity]
  ext ⟨⟨i,j⟩,e⟩ ⟨⟨k,l⟩,f⟩
  simp only [Post.pcLift,Post.localMatrix,Matrix.submatrix_apply,Matrix.kronecker,
    Matrix.kroneckerMap_apply,Incidence.bodyReservoir,Equiv.coe_fn_mk]
  ring

private theorem diagonal_hamiltonian_restriction (a : Basis) :
    hamiltonianQ.submatrix (fun c => ((a,a),c)) (fun c => ((a,a),c)) =
      diagonalHQ a := by
  apply Evaluate.qvalue_injective
  rw [qvalue_submatrix,hamiltonianQ_value]
  exact (diagonalHQ_value a).symm

/-- The source PC action on one diagonal body sector and the original donor. -/
def diagonalPCFullQ (a : Basis) : MatrixQ DiagonalFull DiagonalFull :=
  roleBlocksQ
    (bodyLiftQ (qkron (diagonalHQ a) (qidentity (Fin 2))) (qidentity (Fin 2)))
    (donorLiftQ (qkron (diagonalHQ 97) (qidentity (Fin 2)))
      (qidentity (Fin 2)))

theorem diagonal_pc_full_source (a : Basis) (different : a ≠ 97) :
    Spec.pcLift.submatrix (fun i => (diagonalFullEquiv a different i).val)
      (fun i => (diagonalFullEquiv a different i).val) = diagonalPCFullQ a := by
  have kept : Preserves pceOrbit
      (qvalue (qkron hamiltonianQ (qidentity (Fin 2)))) := by
    rw [qvalue_kron,hamiltonianQ_value,qvalue_identity]
    exact preserves_tensor_left numeric_pc_preserves _
  have source := local_role_restriction (fun c : Fin 2 => ((a,a),c))
    donorPCAddress s(a,a) (pcOrbit Supply.donorIndex)
    (diagonal_ne_donor a different) (fun _ => rfl) donorPC_label
    (qkron hamiltonianQ (qidentity (Fin 2))) (qidentity PairController) kept
  rw [diagonal_full_address,pc_lift_as_local_diagonal] at *
  have tensorBody : (qkron hamiltonianQ (qidentity (Fin 2))).submatrix
      (liftedAddress (fun c : Fin 2 => ((a,a),c)))
      (liftedAddress (fun c : Fin 2 => ((a,a),c))) =
        qkron (diagonalHQ a) (qidentity (Fin 2)) := by
    change qkron (hamiltonianQ.submatrix (fun c => ((a,a),c))
      (fun c => ((a,a),c))) (qidentity (Fin 2)) = _
    rw [diagonal_hamiltonian_restriction a]
  have tensorDonor : (qkron hamiltonianQ (qidentity (Fin 2))).submatrix
      (liftedAddress donorPCAddress) (liftedAddress donorPCAddress) =
        qkron (diagonalHQ 97) (qidentity (Fin 2)) := by
    change qkron (hamiltonianQ.submatrix (fun c => (((97 : Basis),97),c))
      (fun c => (((97 : Basis),97),c))) (qidentity (Fin 2)) = _
    rw [diagonal_hamiltonian_restriction 97]
  have bodyId : (qidentity PairController).submatrix donorPCAddress donorPCAddress =
      qidentity (Fin 2) :=
    source_identity_restrict donorPCAddress (by intro i j h; exact Prod.mk.inj h |>.2)
  have donorId : (qidentity PairController).submatrix
      (fun c : Fin 2 => ((a,a),c)) (fun c : Fin 2 => ((a,a),c)) =
      qidentity (Fin 2) :=
    source_identity_restrict _ (by intro i j h; exact Prod.mk.inj h |>.2)
  rw [tensorBody,tensorDonor,bodyId,donorId] at source
  exact source

def diagonalPCPointerQ (a : Basis) :
    MatrixQ (DiagonalFull ⊕ DiagonalFull) (DiagonalFull ⊕ DiagonalFull) :=
  Matrix.fromBlocks (diagonalPCFullQ a) 0 0 (diagonalPCFullQ a)

def diagonalPointerAddress (a : Basis) (different : a ≠ 97) :
    DiagonalFull ⊕ DiagonalFull → PointerIndex :=
  fun i => (coordinatePointer (s(a,a)) (diagonalFullEquiv a different) i).val

theorem diagonal_pc_pointer_source (a : Basis) (different : a ≠ 97) :
    Spec.pcObservable.submatrix (diagonalPointerAddress a different)
      (diagonalPointerAddress a different) = diagonalPCPointerQ a := by
  funext i j
  rcases i with i | i <;> rcases j with j | j
  all_goals simp only [diagonalPointerAddress,diagonalPCPointerQ,
    Spec.pcObservable,Matrix.submatrix_apply,Matrix.fromBlocks]
  · exact congrFun (congrFun (diagonal_pc_full_source a different) i) j
  · rfl
  · rfl
  · exact congrFun (congrFun (diagonal_pc_full_source a different) i) j

theorem source_diagonal_pc_concrete (a : Basis) (different : a ≠ 97) :
    sourceDiagonalPCInt a different = quantize (diagonalPCPointerQ a) := by
  change quantize (Spec.pcObservable.submatrix (diagonalPointerAddress a different)
    (diagonalPointerAddress a different)) = _
  rw [diagonal_pc_pointer_source a different]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
