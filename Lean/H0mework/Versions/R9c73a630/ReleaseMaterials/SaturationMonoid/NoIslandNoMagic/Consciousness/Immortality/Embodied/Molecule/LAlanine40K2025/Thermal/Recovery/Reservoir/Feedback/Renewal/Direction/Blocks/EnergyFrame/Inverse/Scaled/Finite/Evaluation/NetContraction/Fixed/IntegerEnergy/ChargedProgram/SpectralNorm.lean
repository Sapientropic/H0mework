import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.Energy

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

private theorem integer_entry_norm_sq {α β : Type*} (A : MatrixInt α β) (i : α) (j : β) :
    ‖value A i j‖^2 =
      ((A.re i j : ℝ)^2+(A.im i j : ℝ)^2)/(scale : ℝ)^2 := by
  simp only [value,raw,Matrix.smul_apply,smul_eq_mul]
  rw [norm_mul, mul_pow]
  simp_rw [Complex.sq_norm]
  simp [Complex.normSq_apply,scale,Complex.mul_re,Complex.mul_im]
  ring

theorem integer_operator_norm_bound
    (A : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2))
    (r : Int) (hr : 0 ≤ r)
    (hsq : (∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
      ((A.re i j)^2+(A.im i j)^2)) ≤ r^2) :
    ‖value A‖ ≤ (r : ℝ)/(scale : ℝ) := by
  have mass :
      (∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2, ‖value A i j‖^2) =
        ((∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
          ((A.re i j)^2+(A.im i j)^2) : Int) : ℝ)/(scale : ℝ)^2 := by
    simp_rw [integer_entry_norm_sq]
    simp only [← Finset.sum_div]
    norm_cast
  have hsqR :
      (((∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
        ((A.re i j)^2+(A.im i j)^2) : Int) : ℝ)) ≤ (r : ℝ)^2 := by
    exact_mod_cast hsq
  have hnonneg : 0 ≤ (r : ℝ)/(scale : ℝ) := by
    apply div_nonneg (by exact_mod_cast hr)
    exact_mod_cast (le_of_lt scale_positive)
  calc
    ‖value A‖ ≤ frobenius (value A) := operator_le_frobenius _
    _ = Real.sqrt (∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
        ‖value A i j‖^2) := frobenius_value _
    _ ≤ (r : ℝ)/(scale : ℝ) := by
      apply Real.sqrt_le_iff.mpr
      constructor
      · exact hnonneg
      · rw [mass]
        have h := div_le_div_of_nonneg_right hsqR (sq_nonneg (scale : ℝ))
        simpa only [div_pow] using h

theorem ordinary_pc_hermitian (a b : Basis) (ordered : a < b) :
    (qvalue (ordinaryPCPointerQ a b)).IsHermitian := by
  have h := Post.finite_PC_observable_hermitian.submatrix
    (ordinaryPointerAddress a b ordered)
  rw [← Spec.pcObservable_value, ← qvalue_submatrix,
    ordinary_pc_pointer_source] at h
  exact h

theorem ordinary_qnet_hermitian (a b : Basis) (ordered : a < b) :
    (sourceOrdinaryQNet a b ordered).IsHermitian := by
  rw [sourceOrdinaryQNet]
  have pc := ordinary_pc_hermitian a b ordered
  exact (Matrix.isHermitian_conjTranspose_mul_mul _ pc).sub
    (Matrix.isHermitian_conjTranspose_mul_mul _ pc)

theorem hermitian_lower_from_center
    (A : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (hA : A.IsHermitian) (center radius : ℝ)
    (hnorm : ‖A-center • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤ radius) :
    (center-radius) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤ A := by
  let C := A-center • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
  have hcenter : (center • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)).IsHermitian :=
    Matrix.isHermitian_one.smul (by rfl)
  have hC : C.IsHermitian := hA.sub hcenter
  have hCstar : IsSelfAdjoint C := hC.star_eq
  have hLower : -(‖C‖ • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) ≤ C := by
    simpa only [Algebra.algebraMap_eq_smul_one] using
      IsSelfAdjoint.neg_algebraMap_norm_le_self hCstar
  have hRadius : ‖C‖ ≤ radius := hnorm
  have hsmul : ‖C‖ • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      radius • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := smul_le_smul_of_nonneg_right hRadius (zero_le_one :
        (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤ 1)
  have hbound : -(radius • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) ≤ C :=
    (neg_le_neg hsmul).trans hLower
  have hbound' : -(radius • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) ≤
      A-center • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := hbound
  have hshift : -(radius • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))+
      center • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤ A := by
    calc
      -(radius • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))+
          center • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
          (A-center • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))+
            center • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :=
        add_le_add_left hbound' _
      _ = A := sub_add_cancel _ _
  calc
    (center-radius) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) =
        -(radius • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))+center • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
          rw [sub_smul]
          abel
    _ ≤ A := hshift

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
