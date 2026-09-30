import H0mework.Probability.Information.Lattice
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Interval.Finset.Fin

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceUniformFibreVariance.Separation

open scoped Classical
noncomputable section

private theorem rank_gap {count total : Nat} (embedding : Fin count ↪o Fin total)
    (left right : Fin count) (ordered : left ≤ right) :
    right.val - left.val ≤ (embedding right).val - (embedding left).val := by
  have subset : (Finset.Icc left right).map embedding.toEmbedding ⊆
      Finset.Icc (embedding left) (embedding right) := by
    intro image member
    obtain ⟨point, inside, rfl⟩ := Finset.mem_map.mp member
    exact Finset.mem_Icc.mpr ⟨embedding.monotone (Finset.mem_Icc.mp inside).1,
      embedding.monotone (Finset.mem_Icc.mp inside).2⟩
  have counts := Finset.card_le_card subset
  rw [Finset.card_map, Fin.card_Icc, Fin.card_Icc] at counts
  have mapped := embedding.monotone ordered
  omega

theorem embedded_pair_square {count total : Nat} (embedding : Fin count ↪o Fin total)
    (left right : Fin count) :
    ((right.val : ℝ) - (left.val : ℝ)) ^ 2 ≤
      (((embedding right).val : ℝ) - ((embedding left).val : ℝ)) ^ 2 := by
  have orderedCase (first last : Fin count) (ordered : first ≤ last) :
      ((last.val : ℝ) - (first.val : ℝ)) ^ 2 ≤
        (((embedding last).val : ℝ) - ((embedding first).val : ℝ)) ^ 2 := by
    have rank := rank_gap embedding first last ordered
    have mapped := embedding.monotone ordered
    have castGap : (last.val : ℝ) - (first.val : ℝ) ≤
        ((embedding last).val : ℝ) - ((embedding first).val : ℝ) := by
      have castRank : ((last.val - first.val : Nat) : ℝ) ≤
          (((embedding last).val - (embedding first).val : Nat) : ℝ) := by exact_mod_cast rank
      rw [Nat.cast_sub (show first.val ≤ last.val from ordered),
        Nat.cast_sub (show (embedding first).val ≤ (embedding last).val from mapped)] at castRank
      exact castRank
    have nonnegative : 0 ≤ (last.val : ℝ) - (first.val : ℝ) := by
      exact sub_nonneg.mpr (by exact_mod_cast ordered)
    nlinarith
  rcases le_total left right with ordered | reversed
  · exact orderedCase left right ordered
  · convert orderedCase right left reversed using 1 <;> ring

theorem fibre_pair_square {total : Nat} (indices : Finset (Fin total)) :
    (indices.card : ℝ) ^ 2 * ((indices.card : ℝ) ^ 2 - 1) / 6 ≤
      ∑ left ∈ indices, ∑ right ∈ indices, ((right.val : ℝ) - (left.val : ℝ)) ^ 2 := by
  let embedding := indices.orderEmbOfFin rfl
  have enumerate (value : Fin total → ℝ) :
      (∑ index ∈ indices, value index) = ∑ index : Fin indices.card, value (embedding index) := by
    calc
      _ = ∑ index ∈ Finset.univ.map embedding.toEmbedding, value index :=
        congrArg (fun items : Finset (Fin total) => ∑ index ∈ items, value index)
          (indices.map_orderEmbOfFin_univ rfl).symm
      _ = _ := by rw [Finset.sum_map]; rfl
  rw [enumerate]
  simp_rw [enumerate]
  rw [← Lattice.index_pair_square_sum]
  apply Finset.sum_le_sum
  intro left _
  apply Finset.sum_le_sum
  intro right _
  exact embedded_pair_square embedding left right

end
end SourceUniformFibreVariance.Separation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
