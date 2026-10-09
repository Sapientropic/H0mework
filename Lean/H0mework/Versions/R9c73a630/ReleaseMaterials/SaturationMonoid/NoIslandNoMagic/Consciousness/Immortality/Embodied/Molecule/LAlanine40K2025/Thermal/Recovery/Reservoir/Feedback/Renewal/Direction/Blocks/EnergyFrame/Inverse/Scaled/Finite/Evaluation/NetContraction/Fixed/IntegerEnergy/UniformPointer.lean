import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.UniformRotationSource
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerPointer.Consumer
set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Load.Producer.StrictThermal Contraction Evaluate
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

def sourceOrdinaryRootRoleInt (a b : Basis) (ordered : a < b) :
    MatrixInt OrdinaryFull OrdinaryFull :=
  roleBlocksInt (bodyLiftIdentityInt (sourceOrdinaryRootRotatedInt a b ordered))
    (donorLiftIdentityInt sourceDonorRootRotatedInt)

def sourceOrdinaryComplementRoleInt (a b : Basis) (ordered : a < b) :
    MatrixInt OrdinaryFull OrdinaryFull :=
  roleBlocksInt (bodyLiftIdentityInt (sourceOrdinaryComplementRotatedInt a b ordered))
    (donorLiftIdentityInt sourceDonorComplementRotatedInt)

def sourceOrdinaryPointerInt (a b : Basis) (ordered : a < b) :
    MatrixInt (OrdinaryFull ⊕ OrdinaryFull) (OrdinaryFull ⊕ OrdinaryFull) :=
  intFourBlocks (sourceOrdinaryRootRoleInt a b ordered)
    (intNeg (sourceOrdinaryComplementRoleInt a b ordered))
    (sourceOrdinaryComplementRoleInt a b ordered)
    (sourceOrdinaryRootRoleInt a b ordered)

theorem source_ordinary_role_entry_errors (a b : Basis) (ordered : a < b)
    (i j : OrdinaryFull) :
    ‖value (sourceOrdinaryRootRoleInt a b ordered) i j-
      qvalue (ordinaryRootRoleQ a b ordered) i j‖ ≤ (1/10^18 : ℝ) ∧
    ‖value (sourceOrdinaryComplementRoleInt a b ordered) i j-
      qvalue (ordinaryComplementRoleQ a b ordered) i j‖ ≤ (1/10^18 : ℝ) := by
  rcases i with ⟨x,e⟩
  rcases j with ⟨y,f⟩
  have rotated := source_ordinary_rotated_errors a b ordered
  constructor
  · rcases x with (x | x) <;> rcases y with (y | y)
    · simpa only [sourceOrdinaryRootRoleInt,ordinaryRootRoleQ,roleBlocksInt,
        roleBlocksQ,value,raw,qvalue,Matrix.smul_apply,smul_eq_mul] using
        body_lift_entry_error (sourceOrdinaryRootRotatedInt a b ordered)
          (ordinaryRootRotatedQ a b ordered) (1/10^18) rotated.1 (x,e) (y,f)
    · norm_num [sourceOrdinaryRootRoleInt,ordinaryRootRoleQ,roleBlocksInt,
        roleBlocksQ,value,raw,qvalue,Scalar.value]
    · norm_num [sourceOrdinaryRootRoleInt,ordinaryRootRoleQ,roleBlocksInt,
        roleBlocksQ,value,raw,qvalue,Scalar.value]
    · simpa only [sourceOrdinaryRootRoleInt,ordinaryRootRoleQ,roleBlocksInt,
        roleBlocksQ,value,raw,qvalue,Matrix.smul_apply,smul_eq_mul] using
        donor_lift_entry_error sourceDonorRootRotatedInt donorRootRotatedQ
          (1/10^18) source_donor_root_rotated_error (x,e) (y,f)
  · rcases x with (x | x) <;> rcases y with (y | y)
    · simpa only [sourceOrdinaryComplementRoleInt,ordinaryComplementRoleQ,roleBlocksInt,
        roleBlocksQ,value,raw,qvalue,Matrix.smul_apply,smul_eq_mul] using
        body_lift_entry_error (sourceOrdinaryComplementRotatedInt a b ordered)
          (ordinaryComplementRotatedQ a b ordered) (1/10^18) rotated.2 (x,e) (y,f)
    · norm_num [sourceOrdinaryComplementRoleInt,ordinaryComplementRoleQ,roleBlocksInt,
        roleBlocksQ,value,raw,qvalue,Scalar.value]
    · norm_num [sourceOrdinaryComplementRoleInt,ordinaryComplementRoleQ,roleBlocksInt,
        roleBlocksQ,value,raw,qvalue,Scalar.value]
    · simpa only [sourceOrdinaryComplementRoleInt,ordinaryComplementRoleQ,roleBlocksInt,
        roleBlocksQ,value,raw,qvalue,Matrix.smul_apply,smul_eq_mul] using
        donor_lift_entry_error sourceDonorComplementRotatedInt donorComplementRotatedQ
          (1/10^18) source_donor_complement_rotated_error (x,e) (y,f)

theorem source_ordinary_pointer_entry_error (a b : Basis) (ordered : a < b)
    (i j : OrdinaryFull ⊕ OrdinaryFull) :
    ‖value (sourceOrdinaryPointerInt a b ordered) i j-
      qvalue (ordinaryPointerQ a b ordered) i j‖ ≤ (1/10^18 : ℝ) := by
  rcases i with (i | i) <;> rcases j with (j | j)
  · simpa [sourceOrdinaryPointerInt,ordinaryPointerQ,intFourBlocks,
      Matrix.fromBlocks,value,raw,qvalue] using
      (source_ordinary_role_entry_errors a b ordered i j).1
  · have h := (source_ordinary_role_entry_errors a b ordered i j).2
    change ‖value (intNeg (sourceOrdinaryComplementRoleInt a b ordered)) i j-
      qvalue (-(ordinaryComplementRoleQ a b ordered)) i j‖ ≤ _
    rw [value_int_neg,qvalue_neg]
    simp only [Matrix.neg_apply,neg_sub_neg]
    rw [norm_sub_rev]
    exact h
  · simpa [sourceOrdinaryPointerInt,ordinaryPointerQ,intFourBlocks,
      Matrix.fromBlocks,value,raw,qvalue] using
      (source_ordinary_role_entry_errors a b ordered i j).2
  · simpa [sourceOrdinaryPointerInt,ordinaryPointerQ,intFourBlocks,
      Matrix.fromBlocks,value,raw,qvalue] using
      (source_ordinary_role_entry_errors a b ordered i j).1

theorem source_ordinary_pointer_actual_error (a b : Basis) (ordered : a < b) :
    ‖value (sourceOrdinaryPointerInt a b ordered)-
      PCExecution.pointer.submatrix (ordinaryPointerAddress a b ordered)
        (ordinaryPointerAddress a b ordered)‖ ≤ (1/10^16 : ℝ) := by
  have card : Fintype.card (OrdinaryFull ⊕ OrdinaryFull) ≤ 64 := by
    norm_num [OrdinaryFull]
  have entries (i j : OrdinaryFull ⊕ OrdinaryFull) :
      ‖(value (sourceOrdinaryPointerInt a b ordered)-
        qvalue (ordinaryPointerQ a b ordered)) i j‖ ≤ (1/10^18 : ℝ) := by
    simpa only [Matrix.sub_apply] using
      source_ordinary_pointer_entry_error a b ordered i j
  have bound : ‖value (sourceOrdinaryPointerInt a b ordered)-
      qvalue (ordinaryPointerQ a b ordered)‖ ≤ (1/10^16 : ℝ) :=
    (norm_from_entries _ (1/10^18) (by norm_num) card card entries).trans
      (by norm_num)
  rw [← ordinary_pointer_source,qvalue_submatrix,Spec.pointer_value] at bound
  exact bound

theorem source_first_pointer_same :
    sourceOrdinaryPointerInt (0 : Basis) (1 : Basis) (by decide)=
      sourceFirstPointerInt := rfl

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
