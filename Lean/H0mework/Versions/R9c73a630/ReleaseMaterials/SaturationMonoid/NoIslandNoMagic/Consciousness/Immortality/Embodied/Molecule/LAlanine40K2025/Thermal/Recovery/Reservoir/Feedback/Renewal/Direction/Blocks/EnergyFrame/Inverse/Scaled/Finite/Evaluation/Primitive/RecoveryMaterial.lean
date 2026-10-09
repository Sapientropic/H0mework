import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.PCMaterial
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.ReverseFlow

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive
open Propagation.Interface Propagation.Producer Load.Source
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

def materialPCThree (a b : Basis) (M : PCMaterial a b) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  (pcAssembly (fun n => Scalar.value (M n).three)).submatrix finProdFinEquiv finProdFinEquiv

def materialRecoveryPC (a b : Basis) (M : PCMaterial a b) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  smallControllerSign*materialPCThree a b M*smallControllerSign

theorem small_controller_norm : ‖smallControllerSign‖ ≤ 1 := by
  have diagonal : smallControllerSign=Matrix.diagonal (fun p : Fin 2 × Fin 2 => if p.2=0 then (1 : ℂ) else -1) := by
    ext ⟨p,c⟩ ⟨q,d⟩
    fin_cases p <;> fin_cases c <;> fin_cases q <;> fin_cases d <;>
      norm_num [smallControllerSign,controllerSign,Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.diagonal_apply,Matrix.one_apply]
  rw [diagonal,Matrix.l2_opNorm_diagonal]
  apply pi_norm_le_iff_of_nonneg (by norm_num) |>.mpr
  intro p
  split_ifs <;> norm_num

private theorem difference_reindex {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : κ ≃ ι) (A B : Matrix ι ι ℂ) : ‖A.submatrix e e-B.submatrix e e‖=‖A-B‖ := by
  have same : A.submatrix e e-B.submatrix e e=(A-B).submatrix e e := rfl
  rw [same,Finite.reindex_norm]

attribute [local irreducible] ordinaryPCValues Scalar.value Scalar.polynomial scalarSeed scalarEnergy

theorem material_pc_three_error (a b : Basis) (M : PCMaterial a b) :
    ‖sharedOrdinaryPC a b (3*(nativeClockStep : ℝ))-materialPCThree a b M‖ ≤ (4/10^24 : ℝ) := by
  have bound : ‖pcAssembly (ordinaryPCValues a b (3*(nativeClockStep : ℝ)))-pcAssembly (fun n => Scalar.value (M n).three)‖ ≤ (4/10^24 : ℝ) := by
    apply (pc_assembly_error _ _ (1/10^24) (by norm_num) ?_).trans (by norm_num)
    intro n
    have p := material_three_error _ (M n)
    rw [original_scalar_polynomial a b n 3] at p
    norm_num only [Rat.cast_ofNat] at p
    exact p.trans (by norm_num)
  unfold sharedOrdinaryPC materialPCThree
  exact (difference_reindex (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4) _ _).le.trans bound

theorem material_recovery_pc_error (a b : Basis) (distinct : a ≠ b) (M : PCMaterial a b) :
    ‖Actions.recoveryPCPolynomial.submatrix (orbitPC a b) (orbitPC a b)-materialRecoveryPC a b M‖ ≤ (4/10^24 : ℝ) := by
  rw [original_recovery_pc_shared a b distinct,materialRecoveryPC,← Matrix.sub_mul,← Matrix.mul_sub]
  have first := norm_mul_le (smallControllerSign*(sharedOrdinaryPC a b (3*(nativeClockStep : ℝ))-materialPCThree a b M)) smallControllerSign
  have second := norm_mul_le smallControllerSign (sharedOrdinaryPC a b (3*(nativeClockStep : ℝ))-materialPCThree a b M)
  exact first.trans ((mul_le_mul (second.trans (mul_le_mul small_controller_norm (material_pc_three_error a b M)
    (norm_nonneg _) (by norm_num))) small_controller_norm (norm_nonneg _) (by norm_num)).trans (by norm_num))

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
