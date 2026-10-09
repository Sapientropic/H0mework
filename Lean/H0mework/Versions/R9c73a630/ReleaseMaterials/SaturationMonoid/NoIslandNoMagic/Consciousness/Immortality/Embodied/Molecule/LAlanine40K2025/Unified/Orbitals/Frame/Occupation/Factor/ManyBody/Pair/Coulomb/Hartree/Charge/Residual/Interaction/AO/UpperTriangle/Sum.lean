import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

set_option autoImplicit false
open scoped BigOperators

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle

private theorem split_entry {n : ℕ} (f : Fin n → Fin n → ℝ) (i j : Fin n) :
    f i j = (if i = j then f i j else 0) +
      (if i < j then f i j else 0) + (if j < i then f i j else 0) := by
  rcases lt_trichotomy i j with h | h | h
  · simp [h, ne_of_lt h, not_lt_of_gt h]
  · simp [h]
  · simp [h, ne_of_gt h, not_lt_of_gt h]

theorem full_sum_upper_pair {n : ℕ} (f : Fin n → Fin n → ℝ) :
    (∑ i : Fin n, ∑ j : Fin n, f i j) =
      (∑ i : Fin n, f i i) +
        (∑ i : Fin n, ∑ j : Fin n,
          if i < j then f i j + f j i else 0) := by
  let lower : ℝ := ∑ i : Fin n, ∑ j : Fin n, if j < i then f i j else 0
  have lower_eq : lower =
      ∑ i : Fin n, ∑ j : Fin n, if i < j then f j i else 0 := by
    dsimp [lower]
    rw [Finset.sum_comm]
  have diagonal :
      (∑ i : Fin n, ∑ j : Fin n, if i = j then f i j else 0) =
        ∑ i : Fin n, f i i := by simp
  have combine :
      (∑ i : Fin n, ∑ j : Fin n, if i < j then f i j else 0) +
        (∑ i : Fin n, ∑ j : Fin n, if i < j then f j i else 0) =
          (∑ i : Fin n, ∑ j : Fin n,
            if i < j then f i j + f j i else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> ring
  calc
    (∑ i : Fin n, ∑ j : Fin n, f i j) =
        (∑ i : Fin n, ∑ j : Fin n, if i = j then f i j else 0) +
          (∑ i : Fin n, ∑ j : Fin n, if i < j then f i j else 0) + lower := by
      calc
        _ = ∑ i : Fin n, ∑ j : Fin n,
            ((if i = j then f i j else 0) +
              (if i < j then f i j else 0) + (if j < i then f i j else 0)) := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          exact split_entry f i j
        _ = _ := by simp only [Finset.sum_add_distrib,lower]
    _ = _ := by
      rw [diagonal,lower_eq,add_assoc,combine]

theorem full_sum_upper {n : ℕ} (f : Fin n → Fin n → ℝ)
    (symm : ∀ i j, f i j = f j i) :
    (∑ i : Fin n, ∑ j : Fin n, f i j) =
      (∑ i : Fin n, f i i) +
        2 * (∑ i : Fin n, ∑ j : Fin n, if i < j then f i j else 0) := by
  let upper : ℝ := ∑ i : Fin n, ∑ j : Fin n, if i < j then f i j else 0
  let lower : ℝ := ∑ i : Fin n, ∑ j : Fin n, if j < i then f i j else 0
  have lower_eq_upper : lower = upper := by
    dsimp [lower, upper]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    split_ifs with hij
    · exact symm i j
    · rfl
  calc
    (∑ i : Fin n, ∑ j : Fin n, f i j) =
        (∑ i : Fin n, ∑ j : Fin n, if i = j then f i j else 0) + upper + lower := by
      calc
        _ = ∑ i : Fin n, ∑ j : Fin n,
            ((if i = j then f i j else 0) +
              (if i < j then f i j else 0) + (if j < i then f i j else 0)) := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          exact split_entry f i j
        _ = _ := by simp only [Finset.sum_add_distrib,upper,lower]
    _ = _ := by
      simp [lower_eq_upper,upper]
      ring

def sourceUpperPairs : Finset (Fin 98 × Fin 98) :=
  Finset.univ.filter (fun pair => pair.1 ≤ pair.2)

theorem source_upper_pair_count : sourceUpperPairs.card = 4851 := by
  decide +kernel

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle
