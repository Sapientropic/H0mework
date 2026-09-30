import H0mework.Probability.Information.Pairwise
import H0mework.Probability.Recovery.AtomicCotest

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalInventory

open SourceGeneratedRuntimeHistoryProbability SourceWeightedRecovery SourceUniformFibreVariance
open scoped Classical
noncomputable section

def unitTask (bound : Nat) (actor index : Fin (bound + 1)) : ℝ :=
  if index = actor then Real.sqrt (bound + 1 : ℝ) else 0

private theorem task_distance (bound : Nat) (left right : Fin (bound + 1)) :
    (∑ actor : Fin (bound + 1), (unitTask bound actor right - unitTask bound actor left) ^ 2) =
      if left = right then 0 else 2 * (bound + 1 : ℝ) := by
  by_cases same : left = right
  · subst right
    simp
  · rw [if_neg same]
    have pointwise (actor : Fin (bound + 1)) :
        (unitTask bound actor right - unitTask bound actor left) ^ 2 =
          (if actor = left then (bound + 1 : ℝ) else 0) +
            (if actor = right then (bound + 1 : ℝ) else 0) := by
      by_cases a : actor = left
      · subst actor
        simp [unitTask, same, Ne.symm same, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ bound + 1)]
      · by_cases b : actor = right
        · subst actor
          simp [unitTask, same, Ne.symm same, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ bound + 1)]
        · simp [unitTask, a, b, Ne.symm a, Ne.symm b]
    simp_rw [pointwise]
    rw [Finset.sum_add_distrib]
    simp
    ring

private theorem pair_count (bound : Nat) (indices : Finset (Fin (bound + 1))) :
    (∑ left ∈ indices, ∑ right ∈ indices,
      ∑ actor : Fin (bound + 1), (unitTask bound actor right - unitTask bound actor left) ^ 2) =
        2 * (bound + 1 : ℝ) * ((indices.card : ℝ) ^ 2 - indices.card) := by
  simp_rw [task_distance]
  have row (left : Fin (bound + 1)) (inside : left ∈ indices) :
      (∑ right ∈ indices, if left = right then (0 : ℝ) else 2 * (bound + 1 : ℝ)) =
        2 * (bound + 1 : ℝ) * (indices.card - 1) := by
    have terms (right : Fin (bound + 1)) :
        (if left = right then (0 : ℝ) else 2 * (bound + 1 : ℝ)) =
          2 * (bound + 1 : ℝ) - (if left = right then 2 * (bound + 1 : ℝ) else 0) := by
      split_ifs <;> ring
    simp_rw [terms]
    rw [Finset.sum_sub_distrib]
    simp [inside]
    ring
  rw [Finset.sum_congr rfl row]
  simp only [Finset.sum_const, nsmul_eq_mul]
  ring

variable {Observed : Type*} [DecidableEq Observed]
  [MeasurableSpace Observed] [MeasurableSingletonClass Observed]

def cost (bound : Nat) (query : Fin (bound + 1) → Observed) : ℝ :=
  ∑ actor : Fin (bound + 1), ‖residual (historyPMF bound) query
    (taskValue (historyPMF bound) (fun index => (unitTask bound actor index : ℂ)))‖ ^ 2

theorem cost_eq (bound : Nat) (query : Fin (bound + 1) → Observed) :
    cost bound query = (bound + 1 : ℝ) - (outputs bound query).card := by
  unfold cost
  simp_rw [residual_pairwise]
  rw [← Finset.mul_sum, Finset.sum_comm]
  have atOutput (value : Observed) (present : value ∈ outputs bound query) :
      (∑ actor : Fin (bound + 1), ((fibre bound query value).card : ℝ)⁻¹ *
        ∑ left ∈ fibre bound query value, ∑ right ∈ fibre bound query value,
          (unitTask bound actor right - unitTask bound actor left) ^ 2) =
        2 * (bound + 1 : ℝ) * ((fibre bound query value).card - 1) := by
    rw [← Finset.mul_sum, Finset.sum_comm]
    simp_rw [Finset.sum_comm (s := Finset.univ) (t := fibre bound query value)]
    rw [pair_count]
    have nonzero := (positive_card bound query value present).ne'
    field_simp
  rw [Finset.sum_congr rfl atOutput, ← Finset.mul_sum]
  have counts : (∑ value ∈ outputs bound query, ((fibre bound query value).card : ℝ)) = bound + 1 := by
    exact_mod_cast fibre_card_sum bound query
  rw [Finset.sum_sub_distrib, counts]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  have nonzero : (bound + 1 : ℝ) ≠ 0 := by positivity
  field_simp

end
end SourceConditionalInventory
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
