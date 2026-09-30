import H0mework.Chemistry.LAlanineWork.BistochasticMinimum
import H0mework.Chemistry.LAlanineEntropy.SpectralEntropyInvariance
import Mathlib.Data.Fin.Rev

/-! # Source spectra generate an attained minimum on the full unitary orbit -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Work.Capacity

open Quantum Collision Unitary
open scoped Matrix BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable section

def spectralIndex : ι ≃ Fin (Fintype.card ι) :=
  (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι))).symm

def spectralReverse : Equiv.Perm ι :=
  (spectralIndex (ι := ι)).trans (Fin.revPerm.trans spectralIndex.symm)

def permutationUnitary (permutation : Equiv.Perm ι) : Matrix.unitaryGroup ι ℂ := by
  refine ⟨permutation.permMatrix ℂ, ?_⟩
  rw [Unitary.mem_iff]
  change _ᴴ * _ = 1 ∧ _ * _ᴴ = 1
  rw [Matrix.conjTranspose_permMatrix]
  simp only [← Matrix.permMatrix_mul, mul_inv_cancel, inv_mul_cancel, Matrix.permMatrix_one,
    and_self]

theorem permutationUnitary_diagonal (permutation : Equiv.Perm ι) (values : ι → ℂ) :
    conjStarAlgAut ℂ _ (permutationUnitary permutation) (Matrix.diagonal values) =
      Matrix.diagonal (fun i => values (permutation i)) := by
  ext i j
  simp only [conjStarAlgAut_apply, permutationUnitary]
  change ((permutation.permMatrix ℂ * Matrix.diagonal values) *
    (permutation.permMatrix ℂ)ᴴ) i j = _
  rw [Matrix.conjTranspose_permMatrix]
  change (((permutation.toPEquiv.toMatrix : Matrix ι ι ℂ) * Matrix.diagonal values) *
    ((permutation⁻¹).toPEquiv.toMatrix : Matrix ι ι ℂ)) i j = _
  rw [PEquiv.mul_toMatrix_toPEquiv, PEquiv.toMatrix_toPEquiv_mul]
  change Matrix.diagonal values (permutation i) (permutation j) = Matrix.diagonal (fun i => values (permutation i)) i j
  by_cases same : i = j
  · subst j; simp
  · simp [same, permutation.injective.ne same]

theorem energy_unitary_conjugation (H rho : Matrix ι ι ℂ) (U : Matrix.unitaryGroup ι ℂ) :
    energy (conjStarAlgAut ℂ _ U H) (conjStarAlgAut ℂ _ U rho) = energy H rho := by
  unfold energy
  rw [← map_mul]
  exact congrArg Complex.re (unitary_conjugate_trace (H * rho) U)

def passivePopulations (rho : Matrix ι ι ℂ) (hermitian : rho.IsHermitian) : ι → ℝ :=
  fun i => hermitian.eigenvalues (spectralReverse i)

theorem passivePopulations_antivary (H rho : Matrix ι ι ℂ)
    (hH : H.IsHermitian) (hRho : rho.IsHermitian) :
    Antivary hH.eigenvalues (passivePopulations rho hRho) := by
  have increasing : Monotone (fun i : Fin (Fintype.card ι) => hRho.eigenvalues₀ i.rev) := by
    intro i j ordered
    exact hRho.eigenvalues₀_antitone (Fin.rev_le_rev.mpr ordered)
  have opposed := hH.eigenvalues₀_antitone.antivary increasing
  have read (i : ι) : passivePopulations rho hRho i = hRho.eigenvalues₀ (spectralIndex i).rev := by
    simp [passivePopulations, Matrix.IsHermitian.eigenvalues, spectralReverse,
      spectralIndex]
  intro i j ordered
  rw [read, read] at ordered
  exact opposed ordered

def passiveUnitary (H rho : Matrix ι ι ℂ) (hH : H.IsHermitian) (hRho : rho.IsHermitian) :
    Matrix.unitaryGroup ι ℂ :=
  hH.eigenvectorUnitary * permutationUnitary spectralReverse * star hRho.eigenvectorUnitary

def passiveState (H rho : Matrix ι ι ℂ) (hH : H.IsHermitian) (hRho : rho.IsHermitian) :
    Matrix ι ι ℂ :=
  conjStarAlgAut ℂ _ hH.eigenvectorUnitary
    (Matrix.diagonal (fun i => (passivePopulations rho hRho i : ℂ)))

theorem passiveUnitary_generates (H rho : Matrix ι ι ℂ) (hH : H.IsHermitian) (hRho : rho.IsHermitian) :
    conjStarAlgAut ℂ _ (passiveUnitary H rho hH hRho) rho = passiveState H rho hH hRho := by
  rw [passiveUnitary, conjStarAlgAut_mul_apply, conjStarAlgAut_mul_apply,
    hRho.conjStarAlgAut_star_eigenvectorUnitary, permutationUnitary_diagonal]
  simp only [passiveState, passivePopulations, Function.comp_apply, RCLike.ofReal_eq_complex_ofReal]

theorem passiveState_recovers (H rho : Matrix ι ι ℂ) (hH : H.IsHermitian) (hRho : rho.IsHermitian) :
    rho = conjStarAlgAut ℂ _ (star (passiveUnitary H rho hH hRho))
      (passiveState H rho hH hRho) := by
  rw [← passiveUnitary_generates, ← conjStarAlgAut_mul_apply]
  simp

def passiveEnergy (H rho : Matrix ι ι ℂ) (hH : H.IsHermitian) (hRho : rho.IsHermitian) : ℝ :=
  ∑ i, hH.eigenvalues i * passivePopulations rho hRho i

theorem passiveEnergy_attained (H rho : Matrix ι ι ℂ) (hH : H.IsHermitian) (hRho : rho.IsHermitian) :
    energy H (passiveState H rho hH hRho) = passiveEnergy H rho hH hRho := by
  conv_lhs => arg 1; rw [hH.spectral_theorem]
  unfold passiveState
  rw [energy_unitary_conjugation]
  simp only [energy, Matrix.trace, Matrix.diag, Matrix.diagonal_mul, Matrix.diagonal_apply_eq,
    Complex.re_sum, Function.comp_apply, RCLike.ofReal_eq_complex_ofReal,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, passiveEnergy]

theorem passiveEnergy_minimal (H rho : Matrix ι ι ℂ) (hH : H.IsHermitian) (hRho : rho.IsHermitian)
    (U : Matrix.unitaryGroup ι ℂ) :
    passiveEnergy H rho hH hRho ≤ energy H (conjStarAlgAut ℂ _ U rho) := by
  let V := star hH.eigenvectorUnitary * U * star (passiveUnitary H rho hH hRho) * hH.eigenvectorUnitary
  have rotated : conjStarAlgAut ℂ _ V (Matrix.diagonal (fun i => (passivePopulations rho hRho i : ℂ))) =
      conjStarAlgAut ℂ _ (star hH.eigenvectorUnitary) (conjStarAlgAut ℂ _ U rho) := by
    simp only [V, conjStarAlgAut_mul_apply]
    rw [← passiveState, ← passiveState_recovers H rho hH hRho]
  rw [← energy_unitary_conjugation H (conjStarAlgAut ℂ _ U rho) (star hH.eigenvectorUnitary),
    hH.conjStarAlgAut_star_eigenvectorUnitary, ← rotated]
  exact diagonal_passive_energy_minimum hH.eigenvalues (passivePopulations rho hRho)
    (passivePopulations_antivary H rho hH hRho) V

end

end LAlanine40K2025.Thermal.Work.Capacity
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
