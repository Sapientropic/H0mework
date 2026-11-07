import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.UBI.Capacity.Matching.Deficit
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.Fin

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.UBI.Capacity

noncomputable section

variable {Left Right : Type*}

private def augmented (geometry : CanonicalBipartiteFeasibility Left Right) (count : Nat) :
    CanonicalBipartiteFeasibility Left (Right ⊕ Fin count) where
  leftCarrier := geometry.leftCarrier
  rightCarrier := geometry.rightCarrier.disjSum Finset.univ
  Feasible := fun slot item => match item with
    | .inl original => geometry.Feasible slot original
    | .inr _ => True
  feasibleDecidable := fun _ _ => Classical.propDecidable _

private theorem augmented_neighbourhood_has_enough_positions
    (geometry : CanonicalBipartiteFeasibility Left Right) (slots : Finset Left)
    (original : slots ⊆ geometry.leftCarrier) :
    slots.card ≤ (neighbours (augmented geometry (maximumDeficit geometry)) slots).card := by
  classical
  by_cases occurs : slots.Nonempty
  · obtain ⟨slot, listed⟩ := occurs
    let padded := augmented geometry (maximumDeficit geometry)
    have enlarged : (neighbours geometry slots).disjSum (Finset.univ : Finset (Fin (maximumDeficit geometry))) ⊆
        neighbours padded slots := by
      intro item present
      apply (neighbour_iff_original_compatible_edge padded slots item).mpr
      cases item with
      | inl originalItem =>
        obtain ⟨sourceSlot, member, compatible⟩ :=
          (neighbour_iff_original_compatible_edge geometry slots originalItem).mp (Finset.inl_mem_disjSum.mp present)
        exact ⟨sourceSlot, member, Finset.inl_mem_disjSum.mpr compatible.1, compatible.2⟩
      | inr spare => exact ⟨slot, listed, Finset.inr_mem_disjSum.mpr (Finset.mem_univ spare), trivial⟩
    have size := Finset.card_le_card enlarged
    rw [Finset.card_disjSum, Finset.card_univ, Fintype.card_fin] at size
    have deficitBound := every_original_group_deficit_is_bounded geometry slots original
    unfold deficit at deficitBound
    change slots.card ≤ (neighbours padded slots).card
    omega
  · rw [Finset.not_nonempty_iff_eq_empty.mp occurs, Finset.card_empty]
    exact Nat.zero_le _

private def liftEdge (count : Nat) : (Left × Right) ↪ (Left × (Right ⊕ Fin count)) :=
  ⟨fun edge => (edge.1, .inl edge.2), fun _ _ same =>
    Prod.ext (congrArg (fun edge : Left × (Right ⊕ Fin count) => edge.1) same)
      (Sum.inl.inj (congrArg (fun edge : Left × (Right ⊕ Fin count) => edge.2) same))⟩

/-- Auxiliary positions are used only in the Hall argument. Removing them
leaves a matching exclusively on the original feasible edge carrier. -/
private theorem keep_original_edges
    (geometry : CanonicalBipartiteFeasibility Left Right) (count : Nat)
    (matching : Finset (Left × (Right ⊕ Fin count))) (valid : matching ∈ (augmented geometry count).matchings) :
    ∃ original ∈ geometry.matchings, matching.card ≤ original.card + count := by
  classical
  let padded := augmented geometry count
  let lifted := liftEdge (Left := Left) (Right := Right) count
  let original := geometry.edgeCarrier.filter (fun edge => lifted edge ∈ matching)
  let real (edge : Left × (Right ⊕ Fin count)) : Prop := match edge.2 with
    | .inl _ => True
    | .inr _ => False
  let kept := matching.filter real
  let spare := matching.filter (fun edge => ¬ real edge)
  have lawful : original ∈ geometry.matchings := by
    unfold CanonicalBipartiteFeasibility.matchings
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr (Finset.filter_subset _ _), ?_⟩
    have original_in_paid (edge : Left × Right) (present : edge ∈ original) : lifted edge ∈ matching :=
      (Finset.mem_filter.mp present).2
    have injective := padded.matching_laws valid
    constructor
    · intro first left second right same
      exact lifted.injective (injective.1 (original_in_paid first left) (original_in_paid second right) same)
    · intro first left second right same
      exact lifted.injective (injective.2 (original_in_paid first left) (original_in_paid second right)
        (congrArg (Sum.inl : Right → Right ⊕ Fin count) same))
  have kept_exact : original.map lifted = kept := by
    ext edge
    constructor
    · intro present
      obtain ⟨old, listed, rfl⟩ := Finset.mem_map.mp present
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp listed).2, trivial⟩
    · intro present
      obtain ⟨paid, originalSide⟩ := Finset.mem_filter.mp present
      rcases edge with ⟨slot, originalItem | extra⟩
      · have edgeFacts := (padded.mem_edgeCarrier_iff (slot, Sum.inl originalItem)).mp
          (padded.matching_subset_edgeCarrier valid paid)
        have edgeMem := (geometry.mem_edgeCarrier_iff (slot, originalItem)).mpr
          ⟨edgeFacts.1, Finset.inl_mem_disjSum.mp edgeFacts.2.1, edgeFacts.2.2⟩
        exact Finset.mem_map.mpr ⟨(slot, originalItem), Finset.mem_filter.mpr ⟨edgeMem, paid⟩, rfl⟩
      · exact originalSide.elim
  have spareLimited : spare.card ≤ count := by
    have distinct : Set.InjOn Prod.snd (spare : Set (Left × (Right ⊕ Fin count))) := by
      apply (padded.matching_laws valid).2.mono
      intro edge present
      exact (Finset.mem_filter.mp present).1
    have inPadding : spare.image Prod.snd ⊆ (Finset.univ : Finset (Fin count)).map Function.Embedding.inr := by
      intro item present
      obtain ⟨⟨slot, originalItem | extra⟩, assigned, rfl⟩ := Finset.mem_image.mp present
      · exact ((Finset.mem_filter.mp assigned).2 trivial).elim
      · exact Finset.mem_map.mpr ⟨extra, Finset.mem_univ _, rfl⟩
    have size := Finset.card_le_card inPadding
    rw [Finset.card_image_iff.mpr distinct, Finset.card_map, Finset.card_univ, Fintype.card_fin] at size
    exact size
  have exactCard : original.card = kept.card := by rw [← kept_exact, Finset.card_map]
  have split : kept.card + spare.card = matching.card := Finset.card_filter_add_card_filter_not real
  exact ⟨original, lawful, by omega⟩

theorem actual_capacity_plus_the_largest_original_deficit_is_the_full_need
    (geometry : CanonicalBipartiteFeasibility Left Right) :
    geometry.maximumMatchingCapacity + maximumDeficit geometry = geometry.leftCarrier.card := by
  let padded := augmented geometry (maximumDeficit geometry)
  have full : padded.maximumMatchingCapacity = padded.leftCarrier.card :=
    (full_payment_iff_every_original_group_has_enough_neighbours padded).mpr
      (augmented_neighbourhood_has_enough_positions geometry)
  obtain ⟨matching, paid, complete⟩ := (full_capacity_iff_there_is_a_complete_matching padded).mp full
  obtain ⟨original, originalPaid, size⟩ := keep_original_edges geometry (maximumDeficit geometry) matching paid
  have lower : original.card ≤ geometry.maximumMatchingCapacity := Finset.le_sup (f := Finset.card) originalPaid
  apply le_antisymm (the_canonical_capacity_cannot_exceed_the_original_deficit_bound geometry)
  change matching.card = geometry.leftCarrier.card at complete
  omega

end

end SaturationMonoid.ProcessGame.Society.UBI.Capacity
