import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerPointer.Rotation
set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Load.Producer.StrictThermal Contraction Evaluate
open scoped Matrix BigOperators Matrix.Norms.L2Operator

theorem body_lift_entry_error {τ σ : Type*} [Fintype τ] [DecidableEq τ]
    [Fintype σ] [DecidableEq σ] (RI : MatrixInt (τ × Fin 2) (τ × Fin 2))
    (R : MatrixQ (τ × Fin 2) (τ × Fin 2)) (eps : ℝ)
    (paid : ‖value RI-qvalue R‖ ≤ eps) (i j : Leg τ σ) :
    ‖value (bodyLiftIdentityInt RI) i j-qvalue (bodyLiftQ R (qidentity σ)) i j‖ ≤ eps := by
  by_cases same : i.1.2=j.1.2
  · have left : value (bodyLiftIdentityInt RI) i j =
        value RI (i.1.1,i.2) (j.1.1,j.2) := by
      simp only [value,raw,bodyLiftIdentityInt,Matrix.smul_apply,
        smul_eq_mul,same,if_pos]
    have right : qvalue (bodyLiftQ R (qidentity σ)) i j =
        qvalue R (i.1.1,i.2) (j.1.1,j.2) := by
      simp [qvalue,bodyLiftQ,qidentity,Matrix.scalar_apply,same,Scalar.value,Scalar.multiply]
    rw [left,right]
    exact (matrix_entry_norm_le (value RI-qvalue R) _ _).trans paid
  · have left : value (bodyLiftIdentityInt RI) i j=0 := by
      simp [value,raw,bodyLiftIdentityInt,same]
    have right : qvalue (bodyLiftQ R (qidentity σ)) i j=0 := by
      simp [qvalue,bodyLiftQ,qidentity,Matrix.scalar_apply,same,Scalar.value,Scalar.multiply]
    simpa [left,right] using (le_trans (norm_nonneg (value RI-qvalue R)) paid)

theorem donor_lift_entry_error {τ σ : Type*} [Fintype τ] [DecidableEq τ]
    [Fintype σ] [DecidableEq σ] (RI : MatrixInt (σ × Fin 2) (σ × Fin 2))
    (R : MatrixQ (σ × Fin 2) (σ × Fin 2)) (eps : ℝ)
    (paid : ‖value RI-qvalue R‖ ≤ eps) (i j : Leg τ σ) :
    ‖value (donorLiftIdentityInt RI) i j-qvalue (donorLiftQ R (qidentity τ)) i j‖ ≤ eps := by
  by_cases same : i.1.1=j.1.1
  · have left : value (donorLiftIdentityInt RI) i j =
        value RI (i.1.2,i.2) (j.1.2,j.2) := by
      simp only [value,raw,donorLiftIdentityInt,Matrix.smul_apply,
        smul_eq_mul,same,if_pos]
    have right : qvalue (donorLiftQ R (qidentity τ)) i j =
        qvalue R (i.1.2,i.2) (j.1.2,j.2) := by
      simp [qvalue,donorLiftQ,qidentity,Matrix.scalar_apply,same,Scalar.value,Scalar.multiply]
    rw [left,right]
    exact (matrix_entry_norm_le (value RI-qvalue R) _ _).trans paid
  · have left : value (donorLiftIdentityInt RI) i j=0 := by
      simp [value,raw,donorLiftIdentityInt,same]
    have right : qvalue (donorLiftQ R (qidentity τ)) i j=0 := by
      simp [qvalue,donorLiftQ,qidentity,Matrix.scalar_apply,same,Scalar.value,Scalar.multiply]
    simpa [left,right] using (le_trans (norm_nonneg (value RI-qvalue R)) paid)

theorem source_first_root_role_entry_error (i j : OrdinaryFull) :
    ‖value sourceFirstRootRoleInt i j-
      qvalue (ordinaryRootRoleQ (0 : Basis) (1 : Basis) (by decide)) i j‖ ≤
      (1/10^18 : ℝ) := by
  rcases i with ⟨x,e⟩
  rcases j with ⟨y,f⟩
  rcases x with (x | x) <;> rcases y with (y | y)
  · simpa only [sourceFirstRootRoleInt,ordinaryRootRoleQ,roleBlocksInt,roleBlocksQ,
      value,raw,qvalue,Matrix.smul_apply,smul_eq_mul] using
      body_lift_entry_error sourceFirstRootRotatedInt
        (ordinaryRootRotatedQ (0 : Basis) (1 : Basis) (by decide))
        (1/10^18) source_first_root_rotated_error (x,e) (y,f)
  · norm_num [sourceFirstRootRoleInt,ordinaryRootRoleQ,roleBlocksInt,roleBlocksQ,value,raw,qvalue,Scalar.value]
  · norm_num [sourceFirstRootRoleInt,ordinaryRootRoleQ,roleBlocksInt,roleBlocksQ,value,raw,qvalue,Scalar.value]
  · simpa only [sourceFirstRootRoleInt,ordinaryRootRoleQ,roleBlocksInt,roleBlocksQ,
      value,raw,qvalue,Matrix.smul_apply,smul_eq_mul] using
      donor_lift_entry_error sourceDonorRootRotatedInt donorRootRotatedQ
        (1/10^18) source_donor_root_rotated_error (x,e) (y,f)

theorem source_first_complement_role_entry_error (i j : OrdinaryFull) :
    ‖value sourceFirstComplementRoleInt i j-
      qvalue (ordinaryComplementRoleQ (0 : Basis) (1 : Basis) (by decide)) i j‖ ≤
      (1/10^18 : ℝ) := by
  rcases i with ⟨x,e⟩
  rcases j with ⟨y,f⟩
  rcases x with (x | x) <;> rcases y with (y | y)
  · simpa only [sourceFirstComplementRoleInt,ordinaryComplementRoleQ,roleBlocksInt,roleBlocksQ,
      value,raw,qvalue,Matrix.smul_apply,smul_eq_mul] using
      body_lift_entry_error sourceFirstComplementRotatedInt
        (ordinaryComplementRotatedQ (0 : Basis) (1 : Basis) (by decide))
        (1/10^18) source_first_complement_rotated_error (x,e) (y,f)
  · norm_num [sourceFirstComplementRoleInt,ordinaryComplementRoleQ,roleBlocksInt,roleBlocksQ,
      value,raw,qvalue,Scalar.value]
  · norm_num [sourceFirstComplementRoleInt,ordinaryComplementRoleQ,roleBlocksInt,roleBlocksQ,
      value,raw,qvalue,Scalar.value]
  · simpa only [sourceFirstComplementRoleInt,ordinaryComplementRoleQ,roleBlocksInt,roleBlocksQ,
      value,raw,qvalue,Matrix.smul_apply,smul_eq_mul] using
      donor_lift_entry_error sourceDonorComplementRotatedInt donorComplementRotatedQ
        (1/10^18) source_donor_complement_rotated_error (x,e) (y,f)

theorem value_int_neg (A : MatrixInt OrdinaryFull OrdinaryFull) :
    value (intNeg A)=-value A := by
  ext i j
  simp [value,raw,intNeg]
  ring

theorem source_first_pointer_entry_error (i j : OrdinaryFull ⊕ OrdinaryFull) :
    ‖value sourceFirstPointerInt i j-
      qvalue (ordinaryPointerQ (0 : Basis) (1 : Basis) (by decide)) i j‖ ≤
      (1/10^18 : ℝ) := by
  rcases i with (i | i) <;> rcases j with (j | j)
  · simpa [sourceFirstPointerInt,ordinaryPointerQ,intFourBlocks,
      Matrix.fromBlocks,value,raw,qvalue] using
      source_first_root_role_entry_error i j
  · have h := source_first_complement_role_entry_error i j
    change ‖value (intNeg sourceFirstComplementRoleInt) i j-
      qvalue (-(ordinaryComplementRoleQ (0 : Basis) (1 : Basis) (by decide))) i j‖ ≤ _
    rw [value_int_neg,qvalue_neg]
    simp only [Matrix.neg_apply,neg_sub_neg]
    rw [norm_sub_rev]
    exact h
  · simpa [sourceFirstPointerInt,ordinaryPointerQ,intFourBlocks,
      Matrix.fromBlocks,value,raw,qvalue] using
      source_first_complement_role_entry_error i j
  · simpa [sourceFirstPointerInt,ordinaryPointerQ,intFourBlocks,
      Matrix.fromBlocks,value,raw,qvalue] using
      source_first_root_role_entry_error i j

theorem source_first_pointer_int_error :
    ‖value sourceFirstPointerInt-
      qvalue (ordinaryPointerQ (0 : Basis) (1 : Basis) (by decide))‖ ≤
      (1/10^16 : ℝ) := by
  have card : Fintype.card (OrdinaryFull ⊕ OrdinaryFull) ≤ 64 := by
    norm_num [OrdinaryFull]
  have entries (i j : OrdinaryFull ⊕ OrdinaryFull) :
      ‖(value sourceFirstPointerInt-
        qvalue (ordinaryPointerQ (0 : Basis) (1 : Basis) (by decide))) i j‖ ≤
      (1/10^18 : ℝ) := by
    simpa only [Matrix.sub_apply] using source_first_pointer_entry_error i j
  exact (norm_from_entries _ (1/10^18) (by norm_num) card card entries).trans
    (by norm_num)

theorem source_first_pointer_actual_error :
    ‖value sourceFirstPointerInt-
      PCExecution.pointer.submatrix
        (ordinaryPointerAddress (0 : Basis) (1 : Basis) (by decide))
        (ordinaryPointerAddress (0 : Basis) (1 : Basis) (by decide))‖ ≤
      (1/10^16 : ℝ) := by
  have h := source_first_pointer_int_error
  rw [← ordinary_pointer_source,qvalue_submatrix,Spec.pointer_value] at h
  exact h
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
