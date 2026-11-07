import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.UBI.Capacity.CanonicalMaximumMatching

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.UBI.Capacity

theorem full_capacity_iff_there_is_a_complete_matching
    {Left Right : Type*} (geometry : CanonicalBipartiteFeasibility Left Right) :
    geometry.maximumMatchingCapacity = geometry.leftCarrier.card ↔
      ∃ matching ∈ geometry.matchings, matching.card = geometry.leftCarrier.card := by
  classical
  constructor
  · intro enough
    have hasEmpty : ∅ ∈ geometry.matchings := by
      simp only [CanonicalBipartiteFeasibility.matchings, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨Finset.empty_subset _, geometry.empty_isMatching⟩
    obtain ⟨matching, listed, optimal⟩ :=
      Finset.exists_mem_eq_sup geometry.matchings ⟨∅, hasEmpty⟩ Finset.card
    exact ⟨matching, listed, optimal.symm.trans enough⟩
  · rintro ⟨matching, listed, covers⟩
    apply le_antisymm geometry.maximumMatchingCapacity_le_left
    exact covers ▸ (Finset.le_sup (f := Finset.card) listed)

end SaturationMonoid.ProcessGame.Society.UBI.Capacity
