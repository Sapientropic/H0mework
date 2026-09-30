import H0mework.Chemistry.LAlanineEntropy.SpectralEntropy
import H0mework.Chemistry.LAlanineThermalDynamics.PartialSwapEnergyPopulation
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Algebra.Order.Rearrangement

/-! # Existing Birkhoff and rearrangement produce the energy minimum -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Work.Capacity

open Quantum Collision
open scoped Matrix BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable section

private def matrixEnergyRead (energies populations : ι → ℝ) : Matrix ι ι ℝ →ₗ[ℝ] ℝ where
  toFun M := ∑ i, energies i * (M *ᵥ populations) i
  map_add' M N := by
    simp [Matrix.add_mulVec, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' scalar M := by
    simp only [Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

theorem antivary_bistochastic_minimum (energies populations : ι → ℝ)
    (opposed : Antivary energies populations) (M : Matrix ι ι ℝ)
    (stochastic : M ∈ doublyStochastic ℝ ι) :
    ∑ i, energies i * populations i ≤ ∑ i, energies i * (M *ᵥ populations) i := by
  obtain ⟨weight, nonnegative, normalized, generated⟩ :=
    exists_eq_sum_perm_of_mem_doublyStochastic stochastic
  let read := matrixEnergyRead energies populations
  have atPermutation (permutation : Equiv.Perm ι) :
      read (permutation.permMatrix ℝ) = ∑ i, energies i * populations (permutation i) := by
    change (∑ i, energies i * (permutation.permMatrix ℝ *ᵥ populations) i) = _
    rw [Matrix.permMatrix_mulVec]
    rfl
  calc
    ∑ i, energies i * populations i =
        ∑ permutation, weight permutation * (∑ i, energies i * populations i) := by
      rw [← Finset.sum_mul, normalized, one_mul]
    _ ≤ ∑ permutation, weight permutation * read (permutation.permMatrix ℝ) := by
      apply Finset.sum_le_sum
      intro permutation _
      apply mul_le_mul_of_nonneg_left _ (nonnegative permutation)
      rw [atPermutation]
      exact opposed.sum_mul_le_sum_mul_comp_perm
    _ = read M := by
      rw [← generated]
      simp only [map_sum, map_smul, smul_eq_mul]

theorem bornWeight_bistochastic (U : Matrix.unitaryGroup ι ℂ) :
    bornWeight U ∈ doublyStochastic ℝ ι := by
  apply mem_doublyStochastic_iff_sum.mpr
  exact ⟨fun i j => bornWeight_nonnegative U i j, bornWeight_row U, bornWeight_column U⟩

theorem diagonal_unitary_energy (energies populations : ι → ℝ)
    (U : Matrix.unitaryGroup ι ℂ) :
    energy (Matrix.diagonal (fun i => (energies i : ℂ)))
      ((U : Matrix ι ι ℂ) * Matrix.diagonal (fun i => (populations i : ℂ)) * star (U : Matrix ι ι ℂ)) =
      ∑ i, energies i * (bornWeight U *ᵥ populations) i := by
  simp only [energy, Matrix.trace, Matrix.diag, Matrix.diagonal_mul, Complex.re_sum,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  apply Finset.sum_congr rfl
  intro i _
  rw [unitary_diagonal_real]
  congr 1
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem diagonal_passive_energy_minimum (energies populations : ι → ℝ)
    (opposed : Antivary energies populations) (U : Matrix.unitaryGroup ι ℂ) :
    (∑ i, energies i * populations i) ≤
      energy (Matrix.diagonal (fun i => (energies i : ℂ)))
        ((U : Matrix ι ι ℂ) * Matrix.diagonal (fun i => (populations i : ℂ)) * star (U : Matrix ι ι ℂ)) := by
  rw [diagonal_unitary_energy]
  exact antivary_bistochastic_minimum energies populations opposed _ (bornWeight_bistochastic U)

end

end LAlanine40K2025.Thermal.Work.Capacity
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
