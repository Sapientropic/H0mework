import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Capacity.QuantityFlow.Data
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Capacity.QuantityFlow.Network

open scoped BigOperators

variable {L R : Type*} [Fintype L] [Fintype R]

theorem group_allocation_le_compatible_supply (network : Network L R) {allocation : L → R → ℚ}
    (admitted : network.Admissible allocation) (group : Finset L) :
    (∑ slot ∈ group, rowTotal allocation slot) ≤ network.supplyOf (network.neighbours group) := by
  calc
    (∑ slot ∈ group, rowTotal allocation slot) = ∑ item, ∑ slot ∈ group, allocation slot item :=
      Finset.sum_comm
    _ = ∑ item ∈ network.neighbours group, ∑ slot ∈ group, allocation slot item := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro item _ outside
      apply Finset.sum_eq_zero
      intro slot present
      apply (admitted.1 slot item).2
      cases allowed : network.allows slot item
      · rfl
      · exact (outside ((network.mem_neighbours group item).mpr ⟨slot, present, allowed⟩)).elim
    _ ≤ network.supplyOf (network.neighbours group) := by
      apply Finset.sum_le_sum
      intro item _
      have subset := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ group)
        (fun slot _ _ => (admitted.1 slot item).1)
      exact subset.trans (admitted.2.2 item)

theorem admissible_total_le_demand (network : Network L R) {allocation : L → R → ℚ}
    (admitted : network.Admissible allocation) : total allocation ≤ network.demandOf Finset.univ :=
  Finset.sum_le_sum fun slot _ => admitted.2.1 slot

theorem allocation_is_bounded_by_every_original_cut [DecidableEq L]
    (network : Network L R) {allocation : L → R → ℚ}
    (admitted : network.Admissible allocation) (group : Finset L) :
    total allocation ≤ network.cut group := by
  let outside := Finset.univ \ group
  have partition := Finset.sum_sdiff (f := rowTotal allocation) (Finset.subset_univ group)
  have needsPartition := Finset.sum_sdiff (f := network.need) (Finset.subset_univ group)
  have other : (∑ slot ∈ outside, rowTotal allocation slot) ≤ network.demandOf outside :=
    Finset.sum_le_sum fun slot _ => admitted.2.1 slot
  have own := network.group_allocation_le_compatible_supply admitted group
  unfold cut gap total demandOf at *
  dsimp only [outside] at other
  linarith only [partition, needsPartition, other, own]

theorem full_quantity_iff_total_is_exact (network : Network L R) {allocation : L → R → ℚ}
    (admitted : network.Admissible allocation) :
    network.Complete allocation ↔ total allocation = network.demandOf Finset.univ := by
  constructor
  · intro paid
    exact Finset.sum_congr rfl fun slot _ => paid.2 slot
  · intro exactTotal
    refine ⟨admitted, fun slot => le_antisymm (admitted.2.1 slot) ?_⟩
    by_contra! short
    have strict : total allocation < network.demandOf Finset.univ :=
      Finset.sum_lt_sum (fun key _ => admitted.2.1 key) ⟨slot, Finset.mem_univ slot, short⟩
    exact strict.ne exactTotal

/-- The allocation and its original cut prove each other's optimality. -/
structure Certificate (network : Network L R) where
  allocation : L → R → ℚ
  group : Finset L
  admitted : network.Admissible allocation
  tight : total allocation = network.cut group

def check (network : Network L R) (allocation : L → R → ℚ) (group : Finset L) :
    Option (network.Certificate) :=
  if valid : network.Admissible allocation ∧ total allocation = network.cut group then
    some ⟨allocation, group, valid.1, valid.2⟩
  else none

theorem Certificate.optimal [DecidableEq L] {network : Network L R} (receipt : network.Certificate) :
    (∀ other, network.Admissible other → total other ≤ total receipt.allocation) ∧
      (∀ group, network.gap group ≤ network.gap receipt.group) ∧
      total receipt.allocation + network.gap receipt.group = network.demandOf Finset.univ := by
  have exactCut := receipt.tight
  change total receipt.allocation = network.demandOf Finset.univ - network.gap receipt.group at exactCut
  refine ⟨fun other legal => (network.allocation_is_bounded_by_every_original_cut legal receipt.group).trans_eq receipt.tight.symm,
    fun group => ?_, by linarith only [exactCut]⟩
  have bounded := network.allocation_is_bounded_by_every_original_cut receipt.admitted group
  change total receipt.allocation ≤ network.demandOf Finset.univ - network.gap group at bounded
  linarith only [exactCut, bounded]

theorem Certificate.complete_or_original_shortage {network : Network L R} (receipt : network.Certificate) :
    network.Complete receipt.allocation ∨ network.supplyOf (network.neighbours receipt.group) < network.demandOf receipt.group := by
  have upper := network.admissible_total_le_demand receipt.admitted
  rcases eq_or_lt_of_le upper with equal | short
  · exact .inl ((network.full_quantity_iff_total_is_exact receipt.admitted).mpr equal)
  · right
    have exactCut := receipt.tight
    unfold cut gap at exactCut
    linarith only [exactCut, short]

end SaturationMonoid.ProcessGame.Society.Capacity.QuantityFlow.Network
