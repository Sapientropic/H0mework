import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Contribution.Flow

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Contribution

open ResponsibilityLifecycle
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count : Nat)

theorem every_generated_principal_is_nonnegative
    (account : (Epoch.Finance.process input depth count).GeneratedState) (index : Nat) :
    0 ≤ principalAt input depth count account.current index := by
  unfold principalAt
  split
  · rename_i slot present
    have member := List.mem_of_getElem? present
    have sound := (Epoch.Finance.generated_sound input depth count account slot member).2
    exact Finset.sum_nonneg fun holder _ => sound holder
  · exact le_refl 0

/-- The original slot and its original source quantity are fixed before the
continuation. New admissions do not enlarge this slot's settlement authority. -/
theorem every_actual_continuation_keeps_the_original_receipt_below_its_source_quantity
    (account : (Epoch.Finance.process input depth count).GeneratedState)
    {target : ResponsibilityState (Epoch.Finance.vocabulary input depth count)}
    (run : (Epoch.Finance.process input depth count).Run account.current target)
    (index : Fin account.current.slots.length) :
    receivedAlong input depth count run index.val ≤
      (Epoch.Finance.slotClaim input depth count (account.current.slots.get index)).quantity input depth count := by
  let continued : (Epoch.Finance.process input depth count).GeneratedState :=
    ⟨target,account.generated.concatRuns (Epoch.Finance.process input depth count) run⟩
  have nonnegative := every_generated_principal_is_nonnegative input depth count continued index.val
  have conserved := an_original_slot_keeps_its_total_receipt_and_residual_exact input depth count run index.val index.isLt
  have bounded := (every_original_slot_has_a_nonnegative_finite_source_balance input depth count account index).2
  have read : principalAt input depth count account.current index.val =
      Financial.total input (Epoch.Finance.slotBalance input depth count (account.current.slots.get index)) := by
    simp only [principalAt,List.getElem?_eq_getElem index.isLt,List.get_eq_getElem]
  rw [read] at conserved
  change 0 ≤ principalAt input depth count target index.val at nonnegative
  linarith

theorem the_same_original_claim_cannot_pay_an_unbounded_cumulative_demand
    (account : (Epoch.Finance.process input depth count).GeneratedState)
    (index : Fin account.current.slots.length) (demand : Nat → ℚ)
    (unbounded : ∀ bound : ℚ,∃ stage,demand stage > bound) :
    ¬ (∀ stage,∃ target : ResponsibilityState (Epoch.Finance.vocabulary input depth count),
      ∃ run : (Epoch.Finance.process input depth count).Run account.current target,
        demand stage ≤ receivedAlong input depth count run index.val) := by
  intro paid
  obtain ⟨stage,above⟩ := unbounded
    ((Epoch.Finance.slotClaim input depth count (account.current.slots.get index)).quantity input depth count)
  obtain ⟨target,run,enough⟩ := paid stage
  have bounded := every_actual_continuation_keeps_the_original_receipt_below_its_source_quantity
    input depth count account run index
  exact (not_le_of_gt above) (enough.trans bounded)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Contribution
