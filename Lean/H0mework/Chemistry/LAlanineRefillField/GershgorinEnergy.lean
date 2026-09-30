import H0mework.Chemistry.LAlanineThermalLoad.EnergyNorm
import Mathlib.LinearAlgebra.Matrix.Gershgorin

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Gershgorin

open scoped Matrix ComplexOrder
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem hermitian_eigenvalue (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (i : ι) :
    Module.End.HasEigenvalue (Matrix.toLin' A) (hA.eigenvalues i : ℂ) := by
  apply Module.End.hasEigenvalue_of_hasEigenvector (x := fun j => hA.eigenvectorBasis i j)
  constructor
  · apply Module.End.mem_eigenspace_iff.mpr
    change A *ᵥ (fun j => hA.eigenvectorBasis i j) = (hA.eigenvalues i : ℂ) • _
    calc
      _ = (hA.eigenvalues i) • (fun j => hA.eigenvectorBasis i j) := hA.mulVec_eigenvectorBasis i
      _ = _ := by ext j; simp only [Pi.smul_apply, Complex.real_smul, smul_eq_mul]
  · intro zero
    have vectorZero : hA.eigenvectorBasis i = 0 := by
      ext j
      exact congrFun zero j
    have unitNorm := hA.eigenvectorBasis.orthonormal.1 i
    rw [vectorZero, norm_zero] at unitNorm
    norm_num at unitNorm

theorem diagonally_dominant_positive (A : Matrix ι ι ℂ) (hA : A.IsHermitian)
    (dominant : ∀ i, (∑ j ∈ Finset.univ.erase i, ‖A i j‖) ≤ (A i i).re) : A.PosSemidef := by
  apply hA.posSemidef_iff_eigenvalues_nonneg.mpr
  intro i
  change 0 ≤ hA.eigenvalues i
  obtain ⟨k, bound⟩ := eigenvalue_mem_ball (hermitian_eigenvalue A hA i)
  rw [mem_closedBall_iff_norm'] at bound
  have realBound := (Complex.re_le_norm (A k k - (hA.eigenvalues i : ℂ))).trans bound
  simp only [Complex.sub_re, Complex.ofReal_re] at realBound
  linarith [dominant k]

def lowerDiagonal (H : Matrix ι ι ℂ) (i : ι) : ℝ :=
  (H i i).re - ∑ j ∈ Finset.univ.erase i, ‖H i j‖

theorem lowerDiagonal_positive (H : Matrix ι ι ℂ) (hH : H.IsHermitian) :
    (H - Matrix.diagonal (fun i => (lowerDiagonal H i : ℂ))).PosSemidef := by
  apply diagonally_dominant_positive _ (hH.sub (Matrix.isHermitian_diagonal_iff.mpr (by
    intro i
    change star (lowerDiagonal H i : ℂ) = (lowerDiagonal H i : ℂ)
    simp)))
  intro i
  simp only [Matrix.sub_apply, Matrix.diagonal_apply_eq, Complex.sub_re, Complex.ofReal_re]
  have offDiagonal : (∑ j ∈ Finset.univ.erase i,
      ‖H i j - Matrix.diagonal (fun i => (lowerDiagonal H i : ℂ)) i j‖) =
      ∑ j ∈ Finset.univ.erase i, ‖H i j‖ := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Matrix.diagonal_apply_ne _ (Finset.ne_of_mem_erase hj).symm, sub_zero]
  rw [offDiagonal, lowerDiagonal]
  linarith

omit [DecidableEq ι] in
theorem gram_energy_nonnegative (A D : Matrix ι ι ℂ) (positive : A.PosSemidef) :
    0 ≤ Collision.energy A (Preparation.gram D) := by
  have bound := (Complex.nonneg_iff.mp (positive.conjTranspose_mul_mul_same D).trace_nonneg).1
  rw [Matrix.trace_mul_cycle, Matrix.trace_mul_cycle] at bound
  change 0 ≤ (A * (D * D.conjTranspose)).trace.re
  simpa only [Matrix.mul_assoc] using bound

omit [DecidableEq ι] in
theorem normalizedGram_energy_nonnegative (A D : Matrix ι ι ℂ) (positive : A.PosSemidef) :
    0 ≤ Collision.energy A (Preparation.normalizedGram D) := by
  have bound := gram_energy_nonnegative A D positive
  change 0 ≤ (A * Preparation.gram D).trace.re at bound
  change 0 ≤ (A * ((Preparation.gramMass D)⁻¹ • Preparation.gram D)).trace.re
  rw [Matrix.mul_smul, Matrix.trace_smul, Complex.real_smul, Complex.mul_re]
  simpa only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using
    mul_nonneg (inv_nonneg.mpr (Preparation.gramMass_nonnegative D)) bound

omit [DecidableEq ι] in
theorem gram_diagonal (D : Matrix ι ι ℂ) (i : ι) :
    (Preparation.gram D i i).re = ∑ j, ‖D i j‖ ^ 2 := by
  rw [Preparation.gram, Matrix.mul_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j _
  have scalar := congrArg Complex.re (Complex.mul_conj (D i j))
  change ((D i j) * star (D i j)).re = Complex.normSq (D i j) at scalar
  exact scalar.trans (Complex.normSq_eq_norm_sq _)

theorem normalizedGram_diagonal_energy (d : ι → ℝ) (D : Matrix ι ι ℂ) :
    Collision.energy (Matrix.diagonal (fun i => (d i : ℂ))) (Preparation.normalizedGram D) =
      (Preparation.gramMass D)⁻¹ * ∑ i, d i * ∑ j, ‖D i j‖ ^ 2 := by
  simp only [Collision.energy, Preparation.normalizedGram, Matrix.mul_smul,
    Matrix.trace_smul, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  congr 1
  simp only [Matrix.trace, Matrix.diag, Matrix.diagonal_mul, Complex.re_sum,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    gram_diagonal]

theorem normalizedGram_lower (H D : Matrix ι ι ℂ) (hH : H.IsHermitian) :
    (Preparation.gramMass D)⁻¹ * ∑ i, lowerDiagonal H i * ∑ j, ‖D i j‖ ^ 2 ≤
      Collision.energy H (Preparation.normalizedGram D) := by
  have lower := normalizedGram_energy_nonnegative
    (H - Matrix.diagonal (fun i => (lowerDiagonal H i : ℂ))) D (lowerDiagonal_positive H hH)
  rw [← normalizedGram_diagonal_energy]
  simpa only [Collision.energy, Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re, sub_nonneg] using lower

end
end LAlanine40K2025.Thermal.Recovery.Gershgorin
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
