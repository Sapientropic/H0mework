import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Capacity.QuantityFlow.Scaling

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Capacity.QuantityFlow.Network

open scoped BigOperators

variable {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]

/-- Every jointly achievable rational service profile is characterized by the
original row limits and the compatible supply of each original group. -/
theorem exact_profile_iff_original_group_bounds (network : Network L R) (profile : L → ℚ) :
    (∃ allocation, network.Admissible allocation ∧ ∀ slot, rowTotal allocation slot = profile slot) ↔
      (∀ slot, 0 ≤ profile slot ∧ profile slot ≤ network.need slot) ∧
        ∀ group : Finset L, (∑ slot ∈ group, profile slot) ≤ network.supplyOf (network.neighbours group) := by
  constructor
  · rintro ⟨allocation, admitted, realized⟩
    constructor
    · intro slot
      rw [← realized slot]
      exact ⟨Finset.sum_nonneg fun item _ => (admitted.1 slot item).1, admitted.2.1 slot⟩
    · intro group
      have bound := network.group_allocation_le_compatible_supply admitted group
      simpa only [realized] using bound
  · rintro ⟨within, enough⟩
    let requested : Network L R :=
      { network with need := profile, need_nonnegative := fun slot => (within slot).1 }
    obtain ⟨receipt⟩ := requested.exists_certificate
    rcases receipt.complete_or_original_shortage with paid | missing
    · refine ⟨receipt.allocation, ⟨paid.1.1, ?_, paid.1.2.2⟩, paid.2⟩
      intro slot
      exact (paid.1.2.1 slot).trans (within slot).2
    · exact (not_lt_of_ge (enough receipt.group) missing).elim

theorem complete_iff_every_original_group_has_enough_supply (network : Network L R) :
    (∃ allocation, network.Complete allocation) ↔
      ∀ group : Finset L, network.demandOf group ≤ network.supplyOf (network.neighbours group) := by
  rw [show (∃ allocation, network.Complete allocation) ↔
    (∃ allocation, network.Admissible allocation ∧ ∀ slot, rowTotal allocation slot = network.need slot)
    from Iff.rfl, network.exact_profile_iff_original_group_bounds]
  exact ⟨And.right, fun all => ⟨fun slot => ⟨network.need_nonnegative slot, le_rfl⟩, all⟩⟩

end SaturationMonoid.ProcessGame.Society.Capacity.QuantityFlow.Network
