import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Geometry
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.UBI.Capacity.Matching.Full

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock

open _root_.SaturationMonoid.ProcessGame.Society.UBI.Capacity

def qualifiedGeometry {Left Right : Type} (geometry : CanonicalBipartiteFeasibility Left Right)
    (condition : Left → Right → Prop) (decide : ∀ slot item, Decidable (condition slot item)) :
    CanonicalBipartiteFeasibility Left Right where
  leftCarrier := geometry.leftCarrier
  rightCarrier := geometry.rightCarrier
  Feasible := fun slot item => geometry.Feasible slot item ∧ condition slot item
  feasibleDecidable := fun slot item =>
    @instDecidableAnd _ _ (geometry.feasibleDecidable slot item) (decide slot item)

theorem each_existing_matching_is_retained_when_its_original_edges_pass
    {Left Right : Type} (geometry : CanonicalBipartiteFeasibility Left Right)
    (condition : Left → Right → Prop) (decide : ∀ slot item, Decidable (condition slot item))
    (matching : Finset (Left × Right)) (original : matching ∈ geometry.matchings)
    (passed : ∀ edge ∈ matching, condition edge.1 edge.2) :
    matching ∈ (qualifiedGeometry geometry condition decide).matchings := by
  classical
  unfold CanonicalBipartiteFeasibility.matchings
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_powerset.mpr ?_, geometry.matching_laws original⟩
  intro edge inside
  have actual := (geometry.mem_edgeCarrier_iff edge).mp (geometry.matching_subset_edgeCarrier original inside)
  exact ((qualifiedGeometry geometry condition decide).mem_edgeCarrier_iff edge).mpr
    ⟨actual.1, actual.2.1, actual.2.2, passed edge inside⟩

theorem a_short_matching_leaves_an_original_slot
    {Left Right : Type} (geometry : CanonicalBipartiteFeasibility Left Right)
    (short : geometry.maximumMatchingCapacity < geometry.leftCarrier.card)
    (matching : Finset (Left × Right)) (listed : matching ∈ geometry.matchings) :
    ∃ slot ∈ geometry.leftCarrier, ∀ edge ∈ matching, edge.1 ≠ slot := by
  classical
  have cardEq : (matching.image Prod.fst).card = matching.card :=
    Finset.card_image_iff.mpr (geometry.matching_laws listed).1
  have absent : ¬ geometry.leftCarrier ⊆ matching.image Prod.fst := by
    intro covered
    have count := Finset.card_le_card covered
    rw [cardEq] at count
    have bound : matching.card ≤ geometry.maximumMatchingCapacity := Finset.le_sup (f := Finset.card) listed
    exact (not_le_of_gt short) (count.trans bound)
  obtain ⟨slot, original, unpaid⟩ := Finset.not_subset.mp absent
  exact ⟨slot, original, fun edge present same => unpaid (Finset.mem_image.mpr ⟨edge, present, same⟩)⟩

/-- A distinct original debit for each service occupies the complete left
carrier of the existing canonical matching. -/
theorem distinct_paid_positions_cover_the_original_services
    {Left Right : Type} (geometry : CanonicalBipartiteFeasibility Left Right)
    (position : Left → Right) (distinct : Set.InjOn position geometry.leftCarrier)
    (paid : ∀ slot ∈ geometry.leftCarrier, position slot ∈ geometry.rightCarrier ∧
      geometry.Feasible slot (position slot)) :
    geometry.maximumMatchingCapacity = geometry.leftCarrier.card := by
  classical
  let embed : Left ↪ Left × Right := ⟨fun slot => (slot, position slot), fun _ _ equal => congrArg Prod.fst equal⟩
  let matching := geometry.leftCarrier.map embed
  have listed : matching ∈ geometry.matchings := by
    unfold CanonicalBipartiteFeasibility.matchings
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr ?_, ?_⟩
    · intro edge inside
      obtain ⟨slot, original, rfl⟩ := Finset.mem_map.mp inside
      obtain ⟨right, feasible⟩ := paid slot original
      exact (geometry.mem_edgeCarrier_iff (slot, position slot)).mpr ⟨original, right, feasible⟩
    · constructor
      · intro left leftMem right rightMem equal
        obtain ⟨first, firstMem, rfl⟩ := Finset.mem_map.mp leftMem
        obtain ⟨second, secondMem, rfl⟩ := Finset.mem_map.mp rightMem
        exact congrArg embed equal
      · intro left leftMem right rightMem equal
        obtain ⟨first, firstMem, rfl⟩ := Finset.mem_map.mp leftMem
        obtain ⟨second, secondMem, rfl⟩ := Finset.mem_map.mp rightMem
        exact congrArg embed (distinct firstMem secondMem equal)
  apply le_antisymm geometry.maximumMatchingCapacity_le_left
  have enough : matching.card ≤ geometry.maximumMatchingCapacity := Finset.le_sup (f := Finset.card) listed
  simpa only [matching, Finset.card_map] using enough

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock
