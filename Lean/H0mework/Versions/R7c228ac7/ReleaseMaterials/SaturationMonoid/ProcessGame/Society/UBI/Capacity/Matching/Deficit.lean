import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.UBI.Capacity.Matching.Hall

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.UBI.Capacity

noncomputable section

variable {Left Right : Type*}

def deficit (geometry : CanonicalBipartiteFeasibility Left Right) (slots : Finset Left) : Nat :=
  slots.card - (neighbours geometry slots).card

def maximumDeficit (geometry : CanonicalBipartiteFeasibility Left Right) : Nat :=
  geometry.leftCarrier.powerset.sup (deficit geometry)

theorem every_original_group_deficit_is_bounded
    (geometry : CanonicalBipartiteFeasibility Left Right) (slots : Finset Left)
    (original : slots ⊆ geometry.leftCarrier) :
    deficit geometry slots ≤ maximumDeficit geometry :=
  Finset.le_sup (Finset.mem_powerset.mpr original)

theorem the_largest_deficit_is_attained_at_an_original_group
    (geometry : CanonicalBipartiteFeasibility Left Right) :
    ∃ slots ⊆ geometry.leftCarrier, deficit geometry slots = maximumDeficit geometry := by
  obtain ⟨slots, present, largest⟩ := Finset.exists_mem_eq_sup geometry.leftCarrier.powerset
    ⟨∅, Finset.mem_powerset.mpr (Finset.empty_subset _)⟩ (deficit geometry)
  exact ⟨slots, Finset.mem_powerset.mp present, largest.symm⟩

theorem every_matching_leaves_at_least_the_largest_original_deficit
    (geometry : CanonicalBipartiteFeasibility Left Right)
    (matching : Finset (Left × Right)) (actual : matching ∈ geometry.matchings) :
    matching.card + maximumDeficit geometry ≤ geometry.leftCarrier.card := by
  classical
  obtain ⟨slots, original, largest⟩ := the_largest_deficit_is_attained_at_an_original_group geometry
  let inside := matching.filter fun edge : Left × Right => edge.1 ∈ slots
  let outside := matching.filter fun edge : Left × Right => edge.1 ∉ slots
  have paid := a_matching_pays_at_most_the_neighbours_of_each_original_group geometry slots matching actual
  change inside.card ≤ (neighbours geometry slots).card at paid
  have distinct : Set.InjOn Prod.fst (outside : Set (Left × Right)) := by
    apply (geometry.matching_laws actual).1.mono
    intro edge present
    exact (Finset.mem_filter.mp present).1
  have limited : outside.card ≤ (geometry.leftCarrier \ slots).card := by
    rw [← Finset.card_image_iff.mpr distinct]
    apply Finset.card_le_card
    intro slot listed
    obtain ⟨edge, used, rfl⟩ := Finset.mem_image.mp listed
    obtain ⟨originalEdge, notInside⟩ := Finset.mem_filter.mp used
    exact Finset.mem_sdiff.mpr ⟨((geometry.mem_edgeCarrier_iff edge).mp
      (geometry.matching_subset_edgeCarrier actual originalEdge)).1, notInside⟩
  rw [Finset.card_sdiff_of_subset original] at limited
  have split : inside.card + outside.card = matching.card :=
    Finset.card_filter_add_card_filter_not (fun edge : Left × Right => edge.1 ∈ slots)
  have groupSize := Finset.card_le_card original
  have capacity := geometry.matching_card_le_left actual
  unfold deficit at largest
  omega

theorem the_canonical_capacity_cannot_exceed_the_original_deficit_bound
    (geometry : CanonicalBipartiteFeasibility Left Right) :
    geometry.maximumMatchingCapacity + maximumDeficit geometry ≤ geometry.leftCarrier.card := by
  classical
  have empty : ∅ ∈ geometry.matchings :=
    Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.empty_subset _), geometry.empty_isMatching⟩
  obtain ⟨matching, original, maximal⟩ :=
    Finset.exists_mem_eq_sup geometry.matchings ⟨∅, empty⟩ Finset.card
  rw [CanonicalBipartiteFeasibility.maximumMatchingCapacity, maximal]
  exact every_matching_leaves_at_least_the_largest_original_deficit geometry matching original

end

end SaturationMonoid.ProcessGame.Society.UBI.Capacity
