import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.CompactQ.Consumer
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Evaluate.Source
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Evaluate.Consumer
set_option autoImplicit false
set_option maxRecDepth 4096
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Collision Contraction Evaluate
open scoped Matrix BigOperators
noncomputable section

theorem source_identity_restrict {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (f : β → α) (injective : Function.Injective f) :
    (qidentity α).submatrix f f=qidentity β := by
  apply Evaluate.qvalue_injective
  rw [qvalue_submatrix,qvalue_identity,qvalue_identity]
  exact Matrix.submatrix_one _ injective

def ordinaryRootRoleQ (a b : Basis) (ordered : a < b) :
    MatrixQ OrdinaryFull OrdinaryFull :=
  roleBlocksQ
    (bodyLiftQ (ordinaryRootRotatedQ a b ordered) (qidentity (Fin 2)))
    (donorLiftQ donorRootRotatedQ (qidentity (Fin 2 × Fin 2)))

def ordinaryComplementRoleQ (a b : Basis) (ordered : a < b) :
    MatrixQ OrdinaryFull OrdinaryFull :=
  roleBlocksQ
    (bodyLiftQ (ordinaryComplementRotatedQ a b ordered) (qidentity (Fin 2)))
    (donorLiftQ donorComplementRotatedQ (qidentity (Fin 2 × Fin 2)))

theorem ordinary_root_role_source (a b : Basis) (ordered : a < b) :
    (Spec.bodyObservable (Spec.rotatedRoot computedRootQ)).submatrix
      (fun i => (ordinaryFullEquiv a b ordered.ne i).val)
      (fun i => (ordinaryFullEquiv a b ordered.ne i).val)=
      ordinaryRootRoleQ a b ordered := by
  have kept : Preserves pceOrbit (qvalue (Spec.rotatedRoot computedRootQ)) := by
    rw [Spec.rotatedRoot_value,computedRootQ_value]
    exact rotated_preserves _ finite_root_preserves
  have root := local_role_restriction (orbitPC a b) donorPCAddress s(a,b)
    (pcOrbit Supply.donorIndex) (ordinary_ne_donor a b ordered.ne)
    (ordinary_PC_label a b ordered.ne) donorPC_label
    (Spec.rotatedRoot computedRootQ) (qidentity PairController) kept
  rw [ordinary_full_address,Spec.bodyObservable] at *
  rw [ordinary_lifted_address,donor_lifted_address,ordinary_root_rotated,
    donor_root_rotated] at root
  have bodyId : (qidentity PairController).submatrix donorPCAddress donorPCAddress=
      qidentity (Fin 2) := source_identity_restrict donorPCAddress (by intro i j h; exact Prod.mk.inj h |>.2)
  have donorId : (qidentity PairController).submatrix (orbitPC a b) (orbitPC a b)=
      qidentity (Fin 2 × Fin 2) := source_identity_restrict (orbitPC a b) (by
        intro i j h
        exact (offDiagonalEquiv a b ordered.ne).injective (Subtype.ext h))
  rw [bodyId,donorId] at root
  exact root

theorem ordinary_complement_role_source (a b : Basis) (ordered : a < b) :
    (Spec.bodyObservable (Spec.rotatedRoot computedComplementQ)).submatrix
      (fun i => (ordinaryFullEquiv a b ordered.ne i).val)
      (fun i => (ordinaryFullEquiv a b ordered.ne i).val)=
      ordinaryComplementRoleQ a b ordered := by
  have kept : Preserves pceOrbit (qvalue (Spec.rotatedRoot computedComplementQ)) := by
    rw [Spec.rotatedRoot_value,computedComplementQ_value]
    exact rotated_preserves _ finite_complement_preserves
  have root := local_role_restriction (orbitPC a b) donorPCAddress s(a,b)
    (pcOrbit Supply.donorIndex) (ordinary_ne_donor a b ordered.ne)
    (ordinary_PC_label a b ordered.ne) donorPC_label
    (Spec.rotatedRoot computedComplementQ) (qidentity PairController) kept
  rw [ordinary_full_address,Spec.bodyObservable] at *
  rw [ordinary_lifted_address,donor_lifted_address,ordinary_complement_rotated,
    donor_complement_rotated] at root
  have bodyId : (qidentity PairController).submatrix donorPCAddress donorPCAddress=
      qidentity (Fin 2) := source_identity_restrict donorPCAddress (by intro i j h; exact Prod.mk.inj h |>.2)
  have donorId : (qidentity PairController).submatrix (orbitPC a b) (orbitPC a b)=
      qidentity (Fin 2 × Fin 2) := source_identity_restrict (orbitPC a b) (by
        intro i j h
        exact (offDiagonalEquiv a b ordered.ne).injective (Subtype.ext h))
  rw [bodyId,donorId] at root
  exact root

def ordinaryPointerQ (a b : Basis) (ordered : a < b) :
    MatrixQ (OrdinaryFull ⊕ OrdinaryFull) (OrdinaryFull ⊕ OrdinaryFull) :=
  Matrix.fromBlocks (ordinaryRootRoleQ a b ordered) (-(ordinaryComplementRoleQ a b ordered))
    (ordinaryComplementRoleQ a b ordered) (ordinaryRootRoleQ a b ordered)

def ordinaryPointerAddress (a b : Basis) (ordered : a < b) :
    OrdinaryFull ⊕ OrdinaryFull → PointerIndex :=
  fun i => (coordinatePointer (s(a,b)) (ordinaryFullEquiv a b ordered.ne) i).val

theorem ordinary_pointer_source (a b : Basis) (ordered : a < b) :
    Spec.pointer.submatrix (ordinaryPointerAddress a b ordered)
      (ordinaryPointerAddress a b ordered)=ordinaryPointerQ a b ordered := by
  funext i j
  rcases i with (i | i) <;> rcases j with (j | j)
  all_goals
    simp only [ordinaryPointerAddress,ordinaryPointerQ,Spec.pointer,Matrix.submatrix_apply,
      Matrix.fromBlocks]
  · exact congrFun (congrFun (ordinary_root_role_source a b ordered) i) j
  · exact congrArg Neg.neg (congrFun (congrFun
      (ordinary_complement_role_source a b ordered) i) j)
  · exact congrFun (congrFun (ordinary_complement_role_source a b ordered) i) j
  · exact congrFun (congrFun (ordinary_root_role_source a b ordered) i) j

theorem ordinary_pointer_value (a b : Basis) (ordered : a < b) :
    qvalue (ordinaryPointerQ a b ordered)=
      (localPointer (s(a,b))).submatrix
        (coordinatePointer (s(a,b)) (ordinaryFullEquiv a b ordered.ne))
        (coordinatePointer (s(a,b)) (ordinaryFullEquiv a b ordered.ne)) := by
  rw [← ordinary_pointer_source,qvalue_submatrix,Spec.pointer_value]
  rfl

def ordinarySupplyQ (a b : Basis) (ordered : a < b) :
    MatrixQ OrdinaryFull OrdinaryFull :=
  roleMixQ SquareRoot.Full.cosine SquareRoot.Full.sine
    (qkron (qkron (onePCQ a b ordered) (oneDiagonalQ 97)) freeEnvironmentQ)

theorem ordinary_supply_value (a b : Basis) (ordered : a < b) :
    qvalue (ordinarySupplyQ a b ordered)=
      (localSupply (s(a,b))).submatrix (ordinaryFullEquiv a b ordered.ne)
        (ordinaryFullEquiv a b ordered.ne) := by
  exact (ordinary_local_supply_value a b ordered).symm

def ordinarySourceColumnsQ (a b : Basis) (ordered : a < b) :
    MatrixQ (OrdinaryFull ⊕ OrdinaryFull) ((Fin 2 × Fin 2) × Fin 2) :=
  qmultiply
    ((ordinaryPointerQ a b ordered).submatrix id Sum.inl)
    ((ordinarySupplyQ a b ordered).submatrix id ordinaryInjection)

theorem ordinary_source_columns_value (a b : Basis) (ordered : a < b) :
    qvalue (ordinarySourceColumnsQ a b ordered)=
      sourceColumns (s(a,b)) (ordinaryFullEquiv a b ordered.ne) ordinaryInjection := by
  simp only [ordinarySourceColumnsQ,qvalue_multiply,qvalue_submatrix,
    ordinary_pointer_value,ordinary_supply_value]
  rfl


end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
