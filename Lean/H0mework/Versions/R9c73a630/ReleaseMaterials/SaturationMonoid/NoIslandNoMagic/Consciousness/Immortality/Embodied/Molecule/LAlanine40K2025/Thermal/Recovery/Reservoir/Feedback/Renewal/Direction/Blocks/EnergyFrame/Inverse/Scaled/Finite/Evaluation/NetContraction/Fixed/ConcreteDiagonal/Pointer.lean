import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.ConcreteDiagonal.Pulse

set_option autoImplicit false
set_option maxRecDepth 4096
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Collision Contraction Evaluate
open scoped Matrix BigOperators
noncomputable section

def diagonalNonDonor (a : Basis) (different : a ≠ 97) : Fin 97 :=
  ⟨a.val, by
    have less := a.isLt
    have notLast : a.val ≠ 97 := by
      intro h
      exact different (Fin.ext h)
    omega⟩

theorem diagonal_non_donor_cast (a : Basis) (different : a ≠ 97) :
    (diagonalNonDonor a different).castSucc = a := Fin.ext rfl

def diagonalRootRoleQ (a : Basis) (different : a ≠ 97) :
    MatrixQ DiagonalFull DiagonalFull :=
  roleBlocksQ
    (bodyLiftQ (diagonalRootRotatedQ (diagonalNonDonor a different))
      (qidentity (Fin 2)))
    (donorLiftQ donorRootRotatedQ (qidentity (Fin 2)))

def diagonalComplementRoleQ (a : Basis) (different : a ≠ 97) :
    MatrixQ DiagonalFull DiagonalFull :=
  roleBlocksQ
    (bodyLiftQ (diagonalComplementRotatedQ (diagonalNonDonor a different))
      (qidentity (Fin 2)))
    (donorLiftQ donorComplementRotatedQ (qidentity (Fin 2)))

theorem diagonal_root_role_source (a : Basis) (different : a ≠ 97) :
    (Spec.bodyObservable (Spec.rotatedRoot computedRootQ)).submatrix
      (fun i => (diagonalFullEquiv a different i).val)
      (fun i => (diagonalFullEquiv a different i).val) =
        diagonalRootRoleQ a different := by
  have kept : Preserves pceOrbit (qvalue (Spec.rotatedRoot computedRootQ)) := by
    rw [Spec.rotatedRoot_value,computedRootQ_value]
    exact rotated_preserves _ finite_root_preserves
  have root := local_role_restriction (fun c : Fin 2 => ((a,a),c))
    donorPCAddress s(a,a) (pcOrbit Supply.donorIndex)
    (diagonal_ne_donor a different) (fun _ => rfl) donorPC_label
    (Spec.rotatedRoot computedRootQ) (qidentity PairController) kept
  rw [diagonal_full_address,Spec.bodyObservable] at *
  have body : (Spec.rotatedRoot computedRootQ).submatrix
      (liftedAddress (fun c : Fin 2 => ((a,a),c)))
      (liftedAddress (fun c : Fin 2 => ((a,a),c))) =
        diagonalRootRotatedQ (diagonalNonDonor a different) := by
    rw [diagonal_lifted_address]
    simpa only [diagonal_non_donor_cast a different] using
      diagonal_root_rotated (diagonalNonDonor a different)
  rw [body,donor_lifted_address,donor_root_rotated] at root
  have bodyId : (qidentity PairController).submatrix donorPCAddress donorPCAddress =
      qidentity (Fin 2) :=
    source_identity_restrict donorPCAddress (by intro i j h; exact Prod.mk.inj h |>.2)
  have donorId : (qidentity PairController).submatrix
      (fun c : Fin 2 => ((a,a),c)) (fun c : Fin 2 => ((a,a),c)) =
      qidentity (Fin 2) :=
    source_identity_restrict _ (by intro i j h; exact Prod.mk.inj h |>.2)
  rw [bodyId,donorId] at root
  exact root

theorem diagonal_complement_role_source (a : Basis) (different : a ≠ 97) :
    (Spec.bodyObservable (Spec.rotatedRoot computedComplementQ)).submatrix
      (fun i => (diagonalFullEquiv a different i).val)
      (fun i => (diagonalFullEquiv a different i).val) =
        diagonalComplementRoleQ a different := by
  have kept : Preserves pceOrbit (qvalue (Spec.rotatedRoot computedComplementQ)) := by
    rw [Spec.rotatedRoot_value,computedComplementQ_value]
    exact rotated_preserves _ finite_complement_preserves
  have root := local_role_restriction (fun c : Fin 2 => ((a,a),c))
    donorPCAddress s(a,a) (pcOrbit Supply.donorIndex)
    (diagonal_ne_donor a different) (fun _ => rfl) donorPC_label
    (Spec.rotatedRoot computedComplementQ) (qidentity PairController) kept
  rw [diagonal_full_address,Spec.bodyObservable] at *
  have body : (Spec.rotatedRoot computedComplementQ).submatrix
      (liftedAddress (fun c : Fin 2 => ((a,a),c)))
      (liftedAddress (fun c : Fin 2 => ((a,a),c))) =
        diagonalComplementRotatedQ (diagonalNonDonor a different) := by
    rw [diagonal_lifted_address]
    simpa only [diagonal_non_donor_cast a different] using
      diagonal_complement_rotated (diagonalNonDonor a different)
  rw [body,donor_lifted_address,donor_complement_rotated] at root
  have bodyId : (qidentity PairController).submatrix donorPCAddress donorPCAddress =
      qidentity (Fin 2) :=
    source_identity_restrict donorPCAddress (by intro i j h; exact Prod.mk.inj h |>.2)
  have donorId : (qidentity PairController).submatrix
      (fun c : Fin 2 => ((a,a),c)) (fun c : Fin 2 => ((a,a),c)) =
      qidentity (Fin 2) :=
    source_identity_restrict _ (by intro i j h; exact Prod.mk.inj h |>.2)
  rw [bodyId,donorId] at root
  exact root

def diagonalPointerQ (a : Basis) (different : a ≠ 97) :
    MatrixQ (DiagonalFull ⊕ DiagonalFull) (DiagonalFull ⊕ DiagonalFull) :=
  Matrix.fromBlocks (diagonalRootRoleQ a different)
    (-(diagonalComplementRoleQ a different))
    (diagonalComplementRoleQ a different) (diagonalRootRoleQ a different)

theorem diagonal_pointer_source (a : Basis) (different : a ≠ 97) :
    Spec.pointer.submatrix (diagonalPointerAddress a different)
      (diagonalPointerAddress a different) = diagonalPointerQ a different := by
  funext i j
  rcases i with i | i <;> rcases j with j | j
  all_goals simp only [diagonalPointerAddress,diagonalPointerQ,Spec.pointer,
    Matrix.submatrix_apply,Matrix.fromBlocks]
  · exact congrFun (congrFun (diagonal_root_role_source a different) i) j
  · exact congrArg Neg.neg (congrFun (congrFun
      (diagonal_complement_role_source a different) i) j)
  · exact congrFun (congrFun (diagonal_complement_role_source a different) i) j
  · exact congrFun (congrFun (diagonal_root_role_source a different) i) j

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
