import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.UBI.Capacity.Matching.Completion
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.BigOperators

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Capacity.QuantityFlow.Integral

open scoped BigOperators
open _root_.SaturationMonoid.ProcessGame.Society.UBI.Capacity

noncomputable section

variable {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]

private abbrev Copies {A : Type*} (mass : A → ℕ) := Σ a, Fin (mass a)

private def copies {A : Type*} (mass : A → ℕ) (group : Finset A) : Finset (Copies mass) :=
  group.sigma fun _ => Finset.univ

private theorem copies_card {A : Type*} (mass : A → ℕ) (group : Finset A) :
    (copies mass group).card = ∑ a ∈ group, mass a := by
  simp [copies, Finset.card_sigma]

def neighbours (allows : L → R → Bool) (group : Finset L) : Finset R :=
  Finset.univ.filter fun right => ∃ left ∈ group, allows left right = true

private def geometry (need : L → ℕ) (capacity : R → ℕ) (allows : L → R → Bool) :
    CanonicalBipartiteFeasibility (Copies need) (Copies capacity) where
  leftCarrier := Finset.univ
  rightCarrier := Finset.univ
  Feasible := fun left right => allows left.1 right.1 = true
  feasibleDecidable := fun _ _ => inferInstance

private theorem projection_contains_all_copies {A : Type*} [DecidableEq A] (mass : A → ℕ)
    (group : Finset (Copies mass)) : group.card ≤ ∑ a ∈ group.image Sigma.fst, mass a := by
  rw [← copies_card]
  apply Finset.card_le_card
  intro copy present
  exact Finset.mem_sigma.mpr ⟨Finset.mem_image_of_mem _ present, Finset.mem_univ _⟩

omit [DecidableEq R] in
private theorem neighbours_are_the_original_capacity_copies
    (need : L → ℕ) (capacity : R → ℕ) (allows : L → R → Bool)
    (group : Finset (Copies need)) :
    UBI.Capacity.neighbours (geometry need capacity allows) group =
      copies capacity (neighbours allows (group.image Sigma.fst)) := by
  ext right
  rw [neighbour_iff_original_compatible_edge, copies, Finset.mem_sigma]
  constructor
  · rintro ⟨left, present, _, compatible⟩
    exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, left.1, Finset.mem_image_of_mem _ present, compatible⟩,
      Finset.mem_univ _⟩
  · intro inside
    obtain ⟨left, present, compatible⟩ := (Finset.mem_filter.mp inside.1).2
    obtain ⟨copy, listed, rfl⟩ := Finset.mem_image.mp present
    exact ⟨copy, listed, Finset.mem_univ _, compatible⟩

private def grouped {E : Type*} (matching : Finset E) (left : E → L) (right : E → R)
    (l : L) (r : R) : ℕ :=
  (matching.filter fun edge => left edge = l ∧ right edge = r).card

omit [Fintype L] in
private theorem grouped_row {E : Type*} (matching : Finset E) (left : E → L) (right : E → R) (l : L) :
    (∑ r, grouped matching left right l r) = (matching.filter fun edge => left edge = l).card := by
  have count := Finset.sum_card_fiberwise_eq_card_filter
    (matching.filter fun edge => left edge = l) (Finset.univ : Finset R) right
  simpa only [grouped, Finset.filter_filter, and_comm, Finset.mem_univ, true_and, Finset.filter_true] using count

omit [Fintype R] in
private theorem grouped_column {E : Type*} (matching : Finset E) (left : E → L) (right : E → R) (r : R) :
    (∑ l, grouped matching left right l r) = (matching.filter fun edge => right edge = r).card := by
  have count := Finset.sum_card_fiberwise_eq_card_filter
    (matching.filter fun edge => right edge = r) (Finset.univ : Finset L) left
  simpa only [grouped, Finset.filter_filter, and_comm, Finset.mem_univ, true_and, Finset.filter_true] using count

private theorem grouped_total {E : Type*} (matching : Finset E) (left : E → L) (right : E → R) :
    (∑ l, ∑ r, grouped matching left right l r) = matching.card := by
  simp_rw [grouped_row]
  simpa only [Finset.mem_univ, Finset.filter_true] using
    Finset.sum_card_fiberwise_eq_card_filter matching (Finset.univ : Finset L) left

private theorem used_copies_are_within_the_original_capacity {A E : Type*} [DecidableEq A]
    (mass : A → ℕ) (matching : Finset E) (project : E → Copies mass)
    (distinct : Set.InjOn project (matching : Set E)) (a : A) :
    (matching.filter fun edge => (project edge).1 = a).card ≤ mass a := by
  let selected := matching.filter fun edge => (project edge).1 = a
  have inside : selected.image project ⊆ copies mass {a} := by
    intro copy present
    obtain ⟨edge, listed, rfl⟩ := Finset.mem_image.mp present
    exact Finset.mem_sigma.mpr ⟨Finset.mem_singleton.mpr (Finset.mem_filter.mp listed).2, Finset.mem_univ _⟩
  have cardBound := Finset.card_le_card inside
  rw [Finset.card_image_iff.mpr (distinct.mono (Finset.filter_subset _ _)), copies_card,
    Finset.sum_singleton] at cardBound
  exact cardBound

/-- Unit copies supply a finite existence argument. The allocation and its
cut are returned on the original demand and supply addresses. -/
theorem exists_allocation_meets_original_cut
    (need : L → ℕ) (capacity : R → ℕ) (allows : L → R → Bool) :
    ∃ (allocation : L → R → ℕ) (group : Finset L),
      (∀ l r, allows l r = false → allocation l r = 0) ∧
      (∀ l, (∑ r, allocation l r) ≤ need l) ∧
      (∀ r, (∑ l, allocation l r) ≤ capacity r) ∧
      (∑ l, need l) + (∑ r ∈ neighbours allows group, capacity r) ≤
        (∑ l, ∑ r, allocation l r) + (∑ l ∈ group, need l) := by
  classical
  let actual := geometry need capacity allows
  have nonempty : actual.matchings.Nonempty := by
    refine ⟨∅, ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.empty_subset _), actual.empty_isMatching⟩
  obtain ⟨matching, valid, maximum⟩ := Finset.exists_mem_eq_sup actual.matchings nonempty Finset.card
  change actual.maximumMatchingCapacity = matching.card at maximum
  let allocation := grouped matching (fun edge => edge.1.1) (fun edge => edge.2.1)
  have total : (∑ l, ∑ r, allocation l r) = matching.card := grouped_total _ _ _
  have lawful (l : L) (r : R) (denied : allows l r = false) : allocation l r = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro edge listed
    obtain ⟨inMatching, left, right⟩ := Finset.mem_filter.mp listed
    have access := ((actual.mem_edgeCarrier_iff edge).mp
      (actual.matching_subset_edgeCarrier valid inMatching)).2.2
    change allows edge.1.1 edge.2.1 = true at access
    change edge.1.1 = l at left
    change edge.2.1 = r at right
    rw [left, right, denied] at access
    contradiction
  have row (l : L) : (∑ r, allocation l r) ≤ need l := by
    dsimp only [allocation]
    rw [grouped_row]
    exact used_copies_are_within_the_original_capacity _ _ _ (actual.matching_laws valid).1 l
  have column (r : R) : (∑ l, allocation l r) ≤ capacity r := by
    dsimp only [allocation]
    rw [grouped_column]
    exact used_copies_are_within_the_original_capacity _ _ _ (actual.matching_laws valid).2 r
  have balance := actual_capacity_plus_the_largest_original_deficit_is_the_full_need actual
  rw [maximum] at balance
  have needCard : actual.leftCarrier.card = ∑ l, need l := by
    change Fintype.card (Copies need) = _
    simp [Copies]
  rw [needCard] at balance
  by_cases allPaid : maximumDeficit actual = 0
  · refine ⟨allocation, ∅, lawful, row, column, ?_⟩
    have empty : neighbours allows (∅ : Finset L) = ∅ := by simp [neighbours]
    rw [empty, Finset.sum_empty, Finset.sum_empty, add_zero, add_zero, total]
    omega
  · obtain ⟨group, _, largest⟩ := the_largest_deficit_is_attained_at_an_original_group actual
    let original := group.image Sigma.fst
    have supplyCard : (UBI.Capacity.neighbours actual group).card =
        ∑ r ∈ neighbours allows original, capacity r := by
      rw [neighbours_are_the_original_capacity_copies, copies_card]
    have originals := projection_contains_all_copies need group
    change group.card ≤ ∑ l ∈ original, need l at originals
    unfold deficit at largest
    rw [supplyCard] at largest
    refine ⟨allocation, original, lawful, row, column, ?_⟩
    rw [total]
    omega

end

end SaturationMonoid.ProcessGame.Society.Capacity.QuantityFlow.Integral
