import H0mework.Chemistry.LAlanineThermalDynamics.FiniteControllerFlow

/-! # Operator and tensor norm bounds for source matrices -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Load.Producer

open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Powered.Dynamics
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator

noncomputable section

namespace StrictThermal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem matrix_norm_le_of_entrySquares (A : Matrix ι ι ℂ) (M : ℝ) (hM : 0 ≤ M)
    (entries : (∑ i, ∑ j, ‖A i j‖ ^ 2) ≤ M ^ 2) : ‖A‖ ≤ M := by
  rw [← Matrix.l2_opNorm_toEuclideanCLM]
  apply ContinuousLinearMap.opNorm_le_bound _ hM
  intro v
  have row (i : ι) :
      ‖∑ j, A i j * v j‖ ^ 2 ≤ (∑ j, ‖A i j‖ ^ 2) * ‖v‖ ^ 2 := by
    have triangle : ‖∑ j, A i j * v j‖ ≤ ∑ j, ‖A i j‖ * ‖v j‖ := by
      simpa only [norm_mul] using norm_sum_le (Finset.univ) (fun j => A i j * v j)
    calc
      _ ≤ (∑ j, ‖A i j‖ * ‖v j‖) ^ 2 := by gcongr
      _ ≤ _ := by
        rw [EuclideanSpace.norm_sq_eq]
        exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have squared : ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A v‖ ^ 2 ≤ M ^ 2 * ‖v‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc
      _ ≤ ∑ i, (∑ j, ‖A i j‖ ^ 2) * ‖v‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => row i
      _ = (∑ i, ∑ j, ‖A i j‖ ^ 2) * ‖v‖ ^ 2 := (Finset.sum_mul _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right entries (sq_nonneg _)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hM (norm_nonneg v))).mp
  simpa only [mul_pow] using squared

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

def tensorLeft : Matrix ι ι ℂ →⋆ₙₐ[ℂ] Matrix (ι × κ) (ι × κ) ℂ where
  toFun A := Matrix.kronecker A 1
  map_zero' := by simp [Matrix.kronecker]
  map_add' A B := by
    ext i j
    simp [Matrix.kronecker, Matrix.kroneckerMap_apply, add_mul]
  map_mul' A B := by simp [Matrix.kronecker, ← Matrix.mul_kronecker_mul]
  map_smul' z A := by
    ext i j
    simp [Matrix.kronecker, Matrix.kroneckerMap_apply, mul_assoc]
  map_star' A := by
    change Matrix.kronecker Aᴴ 1 = (Matrix.kronecker A 1)ᴴ
    simp [Matrix.kronecker, Matrix.conjTranspose_kronecker]

def tensorRight : Matrix κ κ ℂ →⋆ₙₐ[ℂ] Matrix (ι × κ) (ι × κ) ℂ where
  toFun A := Matrix.kronecker 1 A
  map_zero' := by simp [Matrix.kronecker]
  map_add' A B := by
    ext i j
    simp [Matrix.kronecker, Matrix.kroneckerMap_apply, mul_add]
  map_mul' A B := by simp [Matrix.kronecker, ← Matrix.mul_kronecker_mul]
  map_smul' z A := by
    ext i j
    simp [Matrix.kronecker, Matrix.kroneckerMap_apply, mul_left_comm]
  map_star' A := by
    change Matrix.kronecker 1 Aᴴ = (Matrix.kronecker 1 A)ᴴ
    simp [Matrix.kronecker, Matrix.conjTranspose_kronecker]

theorem kronecker_norm_le (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ) :
    ‖Matrix.kronecker A B‖ ≤ ‖A‖ * ‖B‖ := by
  have factor : Matrix.kronecker A B = tensorLeft (κ := κ) A * tensorRight (ι := ι) B := by
    simp [tensorLeft, tensorRight, Matrix.kronecker, ← Matrix.mul_kronecker_mul]
  rw [factor]
  exact (norm_mul_le _ _).trans
    (mul_le_mul (NonUnitalStarAlgHom.norm_apply_le (tensorLeft (κ := κ)) A)
      (NonUnitalStarAlgHom.norm_apply_le (tensorRight (ι := ι)) B)
      (norm_nonneg _) (norm_nonneg _))

end StrictThermal

end

end LAlanine40K2025.Thermal.Load.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
