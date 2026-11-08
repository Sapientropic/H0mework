import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Capacity.QuantityFlow.Solver

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Capacity.QuantityFlow.Network

open scoped BigOperators

variable {L R : Type*} [Fintype L] [Fintype R]

/-- Keep the due prefix of the original needs. The complete supply and
its compatibility stay on the original receipt addresses. -/
def restrict (network : Network L R) (active : L → Bool) : Network L R where
  need := fun slot => if active slot then network.need slot else 0
  capacity := network.capacity
  allows := network.allows
  need_nonnegative := fun slot => by split <;> first | exact network.need_nonnegative slot | rfl
  capacity_nonnegative := network.capacity_nonnegative

def PaysWhere (network : Network L R) (active : L → Bool) : Prop :=
  ∃ allocation, network.Admissible allocation ∧
    ∀ slot, active slot = true → rowTotal allocation slot = network.need slot

theorem restricted_allocation_is_admitted_on_original_rows (network : Network L R) (active : L → Bool)
    {allocation : L → R → ℚ} (admitted : (network.restrict active).Admissible allocation) :
    network.Admissible allocation := by
  refine ⟨admitted.1, fun slot => (admitted.2.1 slot).trans ?_, admitted.2.2⟩
  change (if active slot then network.need slot else 0) ≤ network.need slot
  split
  · rfl
  · exact network.need_nonnegative slot

theorem original_rows_can_be_restricted_to_any_earlier_due_prefix
    (network : Network L R) {earlier later : L → Bool}
    (included : ∀ slot, earlier slot = true → later slot = true) :
    network.PaysWhere later → network.PaysWhere earlier := by
  rintro ⟨allocation, legal, paid⟩
  exact ⟨allocation, legal, fun slot due => paid slot (included slot due)⟩

theorem restriction_is_exact_for_the_original_due_rows (network : Network L R) (active : L → Bool) :
    (∃ allocation, (network.restrict active).Complete allocation) ↔ network.PaysWhere active := by
  constructor
  · rintro ⟨allocation, legal, paid⟩
    refine ⟨allocation, network.restricted_allocation_is_admitted_on_original_rows active legal, fun slot due => ?_⟩
    simpa only [restrict, due, if_true] using paid slot
  · rintro ⟨allocation, legal, paid⟩
    let selected : L → R → ℚ := fun slot item => if active slot then allocation slot item else 0
    have row (slot : L) : rowTotal selected slot = (network.restrict active).need slot := by
      cases due : active slot
      · simp [rowTotal, selected, restrict, due]
      · simpa [rowTotal, selected, restrict, due] using paid slot due
    have supply (item : R) : columnTotal selected item ≤ (network.restrict active).capacity item := by
      refine (Finset.sum_le_sum fun slot _ => ?_).trans (legal.2.2 item)
      cases due : active slot
      · simpa [selected, due] using (legal.1 slot item).1
      · simp [selected, due]
    refine ⟨selected, ⟨fun slot item => ?_, fun slot => (row slot).le, supply⟩, row⟩
    cases due : active slot
    · simp [selected, due]
    · simpa [selected, restrict, due] using legal.1 slot item

variable [DecidableEq L]

theorem Certificate.gap_pos_iff_no_complete {network : Network L R} (receipt : network.Certificate) :
    0 < network.gap receipt.group ↔ ¬ ∃ allocation, network.Complete allocation := by
  constructor
  · intro short
    rintro ⟨allocation, paid⟩
    have upper := receipt.optimal.1 allocation paid.1
    have full := (network.full_quantity_iff_total_is_exact paid.1).mp paid
    linarith only [upper, full, receipt.optimal.2.2, short]
  · intro unavailable
    exact sub_pos.mpr (receipt.complete_or_original_shortage.resolve_left
      (fun complete => unavailable ⟨receipt.allocation, complete⟩))

theorem restricted_certificate_reports_exact_original_failure (network : Network L R)
    (active : L → Bool) (receipt : (network.restrict active).Certificate) :
    0 < (network.restrict active).gap receipt.group ↔ ¬ network.PaysWhere active := by
  rw [receipt.gap_pos_iff_no_complete, network.restriction_is_exact_for_the_original_due_rows active]

end SaturationMonoid.ProcessGame.Society.Capacity.QuantityFlow.Network
