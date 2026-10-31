import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Contribution.Principal

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Contribution

open ResponsibilityLifecycle
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count : Nat)

def OriginalClaimBounded (state : ResponsibilityState (Epoch.Finance.vocabulary input depth count)) : Prop :=
  ∀ slot ∈ state.slots, Financial.total input (Epoch.Finance.slotBalance input depth count slot) ≤
    (Epoch.Finance.slotClaim input depth count slot).quantity input depth count

theorem each_original_edge_preserves_the_source_claim_bound
    {state : ResponsibilityState (Epoch.Finance.vocabulary input depth count)}
    (bounded : OriginalClaimBounded input depth count state)
    (edge : (Epoch.Finance.process input depth count).Edge state) :
    OriginalClaimBounded input depth count edge.target := by
  intro slot member
  cases edge with
  | admit claim =>
      rcases List.mem_append.mp member with inherited | admitted
      · exact bounded slot inherited
      · have same : slot = .live (Epoch.Finance.admission input depth count claim).toObligation := by
          simpa only [List.mem_singleton,Epoch.Finance.process] using admitted
        subst slot
        have original : (Epoch.Finance.admission input depth count claim).toObligation.content = claim := by
          cases claim <;> rfl
        change Financial.total input (Epoch.Finance.admission input depth count claim).toObligation.residual ≤
          ((Epoch.Finance.admission input depth count claim).toObligation.content).quantity input depth count
        rw [original]
        exact le_of_eq (every_original_admission_has_its_source_quantity input depth count claim)
  | cross index obligation present boundary =>
      rcases List.mem_or_eq_of_mem_set member with inherited | changed
      · exact bounded slot inherited
      · subst slot
        have old := bounded (.live obligation) (present ▸ List.get_mem state.slots index)
        have balance := an_actual_boundary_cannot_refill_its_original_principal input depth count obligation boundary
        have nonnegative := a_lawful_actual_payment_is_nonnegative input depth count boundary.event boundary.lawful
        have retained := Epoch.Finance.boundary_claim input depth count boundary
        change Financial.total input (Epoch.Finance.slotBalance input depth count
          (Epoch.Finance.boundaryDisposition input depth count boundary).targetSlot) ≤
            (Epoch.Finance.slotClaim input depth count
              (Epoch.Finance.boundaryDisposition input depth count boundary).targetSlot).quantity input depth count
        rw [retained]
        change Financial.total input obligation.residual ≤ obligation.content.quantity input depth count at old
        linarith
  | reopen _ _ _ impossible => exact impossible.elim

theorem every_generated_claim_is_bounded_by_its_own_original_quantity
    (account : (Epoch.Finance.process input depth count).GeneratedState) :
    OriginalClaimBounded input depth count account.current := by
  rcases account with ⟨state,run⟩
  induction run with
  | nil => exact fun _ impossible => (List.not_mem_nil impossible).elim
  | step prior edge inherited => exact each_original_edge_preserves_the_source_claim_bound input depth count inherited edge

theorem every_original_slot_has_a_nonnegative_finite_source_balance
    (account : (Epoch.Finance.process input depth count).GeneratedState)
    (index : Fin account.current.slots.length) :
    0 ≤ Financial.total input (Epoch.Finance.slotBalance input depth count (account.current.slots.get index)) ∧
      Financial.total input (Epoch.Finance.slotBalance input depth count (account.current.slots.get index)) ≤
        (Epoch.Finance.slotClaim input depth count (account.current.slots.get index)).quantity input depth count := by
  have member := List.get_mem account.current.slots index
  have nonnegative := (Epoch.Finance.generated_sound input depth count account _ member).2
  refine ⟨?_,every_generated_claim_is_bounded_by_its_own_original_quantity input depth count account _ member⟩
  change 0 ≤ ((Epoch.Finance.slotBalance input depth count (account.current.slots.get index)).sum fun _ quantity => quantity)
  exact Finset.sum_nonneg fun holder _ => nonnegative holder

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Contribution
