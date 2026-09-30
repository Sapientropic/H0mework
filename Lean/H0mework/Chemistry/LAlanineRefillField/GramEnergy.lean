import H0mework.Chemistry.LAlanineRefillField.GershgorinEnergy
import H0mework.Chemistry.LAlanineRefillField.PrimitiveBounds
import H0mework.Chemistry.LAlanineRefillRows.RowsWitness

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.SourcePrimitive

open Propagation.Interface Propagation.Source
open scoped Matrix ComplexOrder
noncomputable section

theorem sourceOffDiagonal_radius (i : Basis) :
    (∑ j ∈ Finset.univ.erase i, ‖activeMatrix electronicSource i j‖) =
      ((∑ j : Basis, if i = j then 0 else |activeNumerator electronicSource i j| : ℤ) : ℝ) /
        1000000000000000 := by
  have erased : (∑ j : Basis, if i = j then (0 : ℝ) else ‖activeMatrix electronicSource i j‖) =
      ∑ j ∈ Finset.univ.erase i, ‖activeMatrix electronicSource i j‖ := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    simp only [ite_true, add_zero]
    apply Finset.sum_congr rfl
    intro j hj
    rw [if_neg (Finset.ne_of_mem_erase hj).symm]
  rw [← erased]
  simp only [Int.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs
  · simp
  · norm_num [activeMatrix, norm_div, Complex.norm_intCast, Int.cast_abs]

theorem source_lowerDiagonal (i : Basis) :
    Gershgorin.lowerDiagonal (activeMatrix electronicSource) i =
      (sourceGershDiagonal i : ℝ) / 1000000000000000 := by
  rw [Gershgorin.lowerDiagonal, sourceOffDiagonal_radius]
  simp only [sourceGershDiagonal, Int.cast_sub, activeMatrix, Complex.div_re,
    Complex.intCast_re, Complex.intCast_im]
  norm_num
  ring

theorem source_density_rowNorm (i : Basis) :
    (∑ j : Basis, ‖initialDensityMatrix electronicSource i j‖ ^ 2) =
      (sourceDensityRowMass i : ℝ) / 1000000000000000000000000 := by
  simp only [sourceDensityRowMass, Int.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  norm_num [initialDensityMatrix, norm_div, Complex.norm_intCast, div_pow]

theorem source_gramMass_rowRead :
    Preparation.gramMass (initialDensityMatrix electronicSource) =
      (∑ i : Basis, sourceDensityRowMass i : ℤ) / (1000000000000000000000000 : ℝ) := by
  simp only [Preparation.gramMass, Matrix.trace, Matrix.diag, Complex.re_sum]
  simp only [Gershgorin.gram_diagonal, source_density_rowNorm, Int.cast_sum, Finset.sum_div]

theorem sourceGershRowWeight_shift :
    (∑ i : Basis, Gershgorin.lowerDiagonal (activeMatrix electronicSource) i *
        ∑ j : Basis, ‖initialDensityMatrix electronicSource i j‖ ^ 2) +
      8 * Preparation.gramMass (initialDensityMatrix electronicSource) =
        (sourceGershShiftedNumerator : ℝ) / 1000000000000000000000000000000000000000 := by
  simp only [source_lowerDiagonal, source_density_rowNorm, source_gramMass_rowRead,
    sourceGershShiftedNumerator, Int.cast_sum, Finset.sum_div, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  push_cast
  ring

theorem sourceGramEnergy_gt_neg_eight :
    -8 < Collision.energy (activeMatrix electronicSource)
      (Preparation.normalizedGram (initialDensityMatrix electronicSource)) := by
  have shiftedPositive : (0 : ℝ) <
      (sourceGershShiftedNumerator : ℝ) / 1000000000000000000000000000000000000000 :=
    div_pos (Int.cast_pos.mpr sourceGershShiftedNumerator_positive) (by norm_num)
  rw [← sourceGershRowWeight_shift] at shiftedPositive
  have weighted : -8 < (Preparation.gramMass (initialDensityMatrix electronicSource))⁻¹ *
      ∑ i : Basis, Gershgorin.lowerDiagonal (activeMatrix electronicSource) i *
        ∑ j : Basis, ‖initialDensityMatrix electronicSource i j‖ ^ 2 := by
    rw [mul_comm, ← div_eq_mul_inv]
    apply (lt_div_iff₀ sourceGramMass_positive).mpr
    linarith
  exact weighted.trans_le (Gershgorin.normalizedGram_lower _ _
    (Propagation.Dynamics.activeMatrix_hermitian electronicSource))

end
end LAlanine40K2025.Thermal.Recovery.SourcePrimitive
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
