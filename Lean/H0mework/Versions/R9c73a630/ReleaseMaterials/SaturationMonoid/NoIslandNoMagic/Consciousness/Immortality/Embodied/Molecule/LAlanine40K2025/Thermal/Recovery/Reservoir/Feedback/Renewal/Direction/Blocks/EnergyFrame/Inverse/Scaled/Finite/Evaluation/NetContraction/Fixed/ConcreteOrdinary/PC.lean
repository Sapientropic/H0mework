import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.ConcreteOrdinary.Pulse
set_option autoImplicit false
set_option maxRecDepth 4096
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Collision Contraction Evaluate
open scoped Matrix BigOperators
noncomputable section

private theorem pc_lift_as_local : Spec.pcLift =
    localMatrixQ (qkron hamiltonianQ (qidentity (Fin 2))) (qidentity PairController) := by
  apply Evaluate.qvalue_injective
  rw [Spec.pcLift_value,localMatrixQ_value,qvalue_kron,qvalue_identity,
    hamiltonianQ_value,qvalue_identity]
  ext ⟨⟨i,j⟩,e⟩ ⟨⟨k,l⟩,f⟩
  simp only [Post.pcLift,Post.localMatrix,Matrix.submatrix_apply,Matrix.kronecker,
    Matrix.kroneckerMap_apply,Incidence.bodyReservoir,Equiv.coe_fn_mk]
  ring

private theorem ordinary_hamiltonian_restriction (a b : Basis) (_ordered : a < b) :
    hamiltonianQ.submatrix (orbitPC a b) (orbitPC a b)=ordinaryHQ a b := by
  apply Evaluate.qvalue_injective
  rw [qvalue_submatrix,hamiltonianQ_value,ordinaryHQ_value a b _ordered.ne]

private theorem donor_hamiltonian_restriction :
    hamiltonianQ.submatrix donorPCAddress donorPCAddress=diagonalHQ 97 := by
  apply Evaluate.qvalue_injective
  rw [qvalue_submatrix,hamiltonianQ_value]
  exact (diagonalHQ_value 97).symm

def ordinaryPCFullQ (a b : Basis) :
    MatrixQ OrdinaryFull OrdinaryFull :=
  roleBlocksQ
    (bodyLiftQ (qkron (ordinaryHQ a b) (qidentity (Fin 2))) (qidentity (Fin 2)))
    (donorLiftQ (qkron (diagonalHQ 97) (qidentity (Fin 2)))
      (qidentity (Fin 2 × Fin 2)))

theorem ordinary_pc_full_source (a b : Basis) (ordered : a < b) :
    Spec.pcLift.submatrix (fun i => (ordinaryFullEquiv a b ordered.ne i).val)
      (fun i => (ordinaryFullEquiv a b ordered.ne i).val)=
      ordinaryPCFullQ a b := by
  have kept : Preserves pceOrbit
      (qvalue (qkron hamiltonianQ (qidentity (Fin 2)))) := by
    rw [qvalue_kron,hamiltonianQ_value,qvalue_identity]
    exact preserves_tensor_left numeric_pc_preserves _
  have source := local_role_restriction (orbitPC a b) donorPCAddress s(a,b)
    (pcOrbit Supply.donorIndex) (ordinary_ne_donor a b ordered.ne)
    (ordinary_PC_label a b ordered.ne) donorPC_label
    (qkron hamiltonianQ (qidentity (Fin 2))) (qidentity PairController) kept
  rw [ordinary_full_address,pc_lift_as_local] at *
  have tensorBody : (qkron hamiltonianQ (qidentity (Fin 2))).submatrix
      (liftedAddress (orbitPC a b)) (liftedAddress (orbitPC a b)) =
      qkron (ordinaryHQ a b) (qidentity (Fin 2)) := by
    change qkron (hamiltonianQ.submatrix (orbitPC a b) (orbitPC a b))
      (qidentity (Fin 2)) = _
    rw [ordinary_hamiltonian_restriction a b ordered]
  have tensorDonor : (qkron hamiltonianQ (qidentity (Fin 2))).submatrix
      (liftedAddress donorPCAddress) (liftedAddress donorPCAddress) =
      qkron (diagonalHQ 97) (qidentity (Fin 2)) := by
    change qkron (hamiltonianQ.submatrix donorPCAddress donorPCAddress)
      (qidentity (Fin 2)) = _
    rw [donor_hamiltonian_restriction]
  have bodyId : (qidentity PairController).submatrix donorPCAddress donorPCAddress=
      qidentity (Fin 2) := source_identity_restrict donorPCAddress (by intro i j h; exact Prod.mk.inj h |>.2)
  have donorId : (qidentity PairController).submatrix (orbitPC a b) (orbitPC a b)=
      qidentity (Fin 2 × Fin 2) := source_identity_restrict (orbitPC a b) (by
        intro i j h
        exact (offDiagonalEquiv a b ordered.ne).injective (Subtype.ext h))
  rw [tensorBody,tensorDonor,bodyId,donorId] at source
  exact source

def ordinaryPCPointerQ (a b : Basis) :
    MatrixQ (OrdinaryFull ⊕ OrdinaryFull) (OrdinaryFull ⊕ OrdinaryFull) :=
  Matrix.fromBlocks (ordinaryPCFullQ a b) 0 0 (ordinaryPCFullQ a b)

theorem ordinary_pc_pointer_source (a b : Basis) (ordered : a < b) :
    Spec.pcObservable.submatrix (ordinaryPointerAddress a b ordered)
      (ordinaryPointerAddress a b ordered)=ordinaryPCPointerQ a b := by
  funext i j
  rcases i with (i | i) <;> rcases j with (j | j)
  all_goals simp only [ordinaryPointerAddress,ordinaryPCPointerQ,Spec.pcObservable,
    Matrix.submatrix_apply,Matrix.fromBlocks]
  · exact congrFun (congrFun (ordinary_pc_full_source a b ordered) i) j
  · rfl
  · rfl
  · exact congrFun (congrFun (ordinary_pc_full_source a b ordered) i) j

theorem ordinary_pc_pointer_value (a b : Basis) (ordered : a < b) :
    qvalue (ordinaryPCPointerQ a b)=
      (localPC (s(a,b))).submatrix
        (coordinatePointer (s(a,b)) (ordinaryFullEquiv a b ordered.ne))
        (coordinatePointer (s(a,b)) (ordinaryFullEquiv a b ordered.ne)) := by
  rw [← ordinary_pc_pointer_source a b ordered,qvalue_submatrix,Spec.pcObservable_value]
  rfl


end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
