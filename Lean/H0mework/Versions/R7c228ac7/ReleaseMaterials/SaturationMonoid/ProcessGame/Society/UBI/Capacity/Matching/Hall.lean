import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.UBI.Capacity.Matching.Full
import Mathlib.Combinatorics.Hall.Finite

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.UBI.Capacity

noncomputable section

variable {Left Right : Type*}

def neighbours (geometry : CanonicalBipartiteFeasibility Left Right) (slots : Finset Left) : Finset Right := by
  classical
  exact slots.biUnion fun slot => geometry.rightCarrier.filter (geometry.Feasible slot)

theorem neighbour_iff_original_compatible_edge
    (geometry : CanonicalBipartiteFeasibility Left Right) (slots : Finset Left) (ordinal : Right) :
    ordinal ∈ neighbours geometry slots ↔
      ∃ slot ∈ slots, ordinal ∈ geometry.rightCarrier ∧ geometry.Feasible slot ordinal := by
  classical
  simp only [neighbours, Finset.mem_biUnion, Finset.mem_filter]

theorem a_matching_pays_at_most_the_neighbours_of_each_original_group [DecidableEq Left]
    (geometry : CanonicalBipartiteFeasibility Left Right) (slots : Finset Left)
    (matching : Finset (Left × Right)) (actual : matching ∈ geometry.matchings) :
    (matching.filter fun edge : Left × Right => edge.1 ∈ slots).card ≤ (neighbours geometry slots).card := by
  classical
  let selected := matching.filter fun edge : Left × Right => edge.1 ∈ slots
  have distinct : Set.InjOn Prod.snd (selected : Set (Left × Right)) := by
    apply (geometry.matching_laws actual).2.mono
    intro edge present
    exact (Finset.mem_filter.mp present).1
  rw [← Finset.card_image_iff.mpr distinct]
  apply Finset.card_le_card
  intro ordinal present
  obtain ⟨edge, listed, rfl⟩ := Finset.mem_image.mp present
  obtain ⟨original, slot⟩ := Finset.mem_filter.mp listed
  have eligible := (geometry.mem_edgeCarrier_iff edge).mp (geometry.matching_subset_edgeCarrier actual original)
  exact (neighbour_iff_original_compatible_edge geometry slots edge.2).mpr ⟨edge.1, slot, eligible.2⟩

theorem every_original_group_has_enough_neighbours_if_the_full_matching_is_paid
    (geometry : CanonicalBipartiteFeasibility Left Right)
    (paid : geometry.maximumMatchingCapacity = geometry.leftCarrier.card)
    (slots : Finset Left) (original : slots ⊆ geometry.leftCarrier) :
    slots.card ≤ (neighbours geometry slots).card := by
  classical
  obtain ⟨matching, actual, complete⟩ := (full_capacity_iff_there_is_a_complete_matching geometry).mp paid
  have useDistinct := (geometry.matching_laws actual).1
  have exactLeft : matching.image Prod.fst = geometry.leftCarrier := by
    apply Finset.eq_of_subset_of_card_le
    · intro slot listed
      obtain ⟨edge, present, rfl⟩ := Finset.mem_image.mp listed
      exact ((geometry.mem_edgeCarrier_iff edge).mp (geometry.matching_subset_edgeCarrier actual present)).1
    · rw [Finset.card_image_iff.mpr useDistinct, complete]
  let selected := matching.filter fun edge : Left × Right => edge.1 ∈ slots
  have covered : slots ⊆ selected.image Prod.fst := by
    intro slot inSlots
    obtain ⟨edge, used, address⟩ := Finset.mem_image.mp (exactLeft.symm ▸ original inSlots)
    exact Finset.mem_image.mpr ⟨edge, Finset.mem_filter.mpr ⟨used, address.symm ▸ inSlots⟩, address⟩
  exact (Finset.card_le_card covered).trans (Finset.card_image_le.trans
    (a_matching_pays_at_most_the_neighbours_of_each_original_group geometry slots matching actual))

/-- Full service is characterized by every source group having enough
compatible original receipts, with exclusivity across the entire group. -/
theorem full_payment_iff_every_original_group_has_enough_neighbours
    (geometry : CanonicalBipartiteFeasibility Left Right) :
    geometry.maximumMatchingCapacity = geometry.leftCarrier.card ↔
      ∀ slots ⊆ geometry.leftCarrier, slots.card ≤ (neighbours geometry slots).card := by
  classical
  refine ⟨every_original_group_has_enough_neighbours_if_the_full_matching_is_paid geometry, ?_⟩
  intro enough
  let L := { slot // slot ∈ geometry.leftCarrier }
  let allowed (slot : L) := geometry.rightCarrier.filter (geometry.Feasible slot.val)
  have hall (group : Finset L) : group.card ≤ (group.biUnion allowed).card := by
    let projected := group.image Subtype.val
    have inside : projected ⊆ geometry.leftCarrier := by
      intro slot found
      obtain ⟨original, _, rfl⟩ := Finset.mem_image.mp found
      exact original.property
    have same : group.biUnion allowed = neighbours geometry projected := by
      ext item
      rw [Finset.mem_biUnion, neighbour_iff_original_compatible_edge]
      constructor
      · rintro ⟨slot, listed, allowedAt⟩
        exact ⟨slot.val, Finset.mem_image.mpr ⟨slot, listed, rfl⟩, Finset.mem_filter.mp allowedAt⟩
      · rintro ⟨slot, listed, allowedAt⟩
        obtain ⟨original, used, rfl⟩ := Finset.mem_image.mp listed
        exact ⟨original, used, Finset.mem_filter.mpr allowedAt⟩
    rw [same, ← Finset.card_image_of_injective group Subtype.val_injective]
    exact enough projected inside
  obtain ⟨position, distinct, paid⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' allowed).mp hall
  let original : L ↪ Left × Right :=
    ⟨fun slot => (slot.val, position slot), fun _ _ same => Subtype.ext (congrArg Prod.fst same)⟩
  let matching := (Finset.univ : Finset L).map original
  have actual : matching ∈ geometry.matchings := by
    unfold CanonicalBipartiteFeasibility.matchings
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr ?_, ?_⟩
    · intro edge member
      obtain ⟨slot, _, rfl⟩ := Finset.mem_map.mp member
      exact (geometry.mem_edgeCarrier_iff (original slot)).mpr ⟨slot.property, Finset.mem_filter.mp (paid slot)⟩
    · constructor
      · intro first firstIn second secondIn equal
        obtain ⟨left, _, rfl⟩ := Finset.mem_map.mp firstIn
        obtain ⟨right, _, rfl⟩ := Finset.mem_map.mp secondIn
        exact congrArg original (Subtype.ext equal)
      · intro first firstIn second secondIn equal
        obtain ⟨left, _, rfl⟩ := Finset.mem_map.mp firstIn
        obtain ⟨right, _, rfl⟩ := Finset.mem_map.mp secondIn
        exact congrArg original (distinct equal)
  apply (full_capacity_iff_there_is_a_complete_matching geometry).mpr
  exact ⟨matching, actual, by simp [matching, L]⟩

theorem a_shortage_exhibits_an_original_group_and_its_own_scarce_neighbours
    (geometry : CanonicalBipartiteFeasibility Left Right)
    (short : geometry.maximumMatchingCapacity < geometry.leftCarrier.card) :
    ∃ slots ⊆ geometry.leftCarrier, (neighbours geometry slots).card < slots.card := by
  classical
  have missing := fun every => short.ne ((full_payment_iff_every_original_group_has_enough_neighbours geometry).mpr every)
  obtain ⟨slots, failed⟩ := not_forall.mp missing
  obtain ⟨original, gap⟩ := Classical.not_imp.mp failed
  exact ⟨slots, original, lt_of_not_ge gap⟩

end

end SaturationMonoid.ProcessGame.Society.UBI.Capacity
