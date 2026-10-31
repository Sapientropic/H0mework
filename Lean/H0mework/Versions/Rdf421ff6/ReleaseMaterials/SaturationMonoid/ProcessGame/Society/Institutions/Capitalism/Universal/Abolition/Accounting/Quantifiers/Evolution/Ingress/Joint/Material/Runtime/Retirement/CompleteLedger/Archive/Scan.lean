import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Archive.Survivor
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Consume
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.BalanceConservation.Readout

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger

open ResponsibilityLifecycle
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root.Epoch.Finance

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count : Nat)

open private allocateAt allocateFrom Allocation.idle from
  H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Allocation

theorem a_zero_survives_the_original_scan_only_outside_all_matching_reviews
    (item : ActualItem input depth count) (fuel position : Nat)
    (state : (process input depth count).GeneratedState) (available : ℚ) (nonnegative : 0 ≤ available)
    (index : Nat) (survivor : AdmittedObligation (vocabulary input depth count))
    (zero : survivor.residual = 0)
    (present : (allocateFrom input depth count item position fuel state available nonnegative).after.current.slots[index]? = some (.live survivor)) :
    state.current.slots[index]? = some (.live survivor) ∧
      (position ≤ index ∧ index < position + fuel → readReview input depth count survivor.content item = none) := by
  induction fuel generalizing position state available with
  | zero => exact ⟨present,fun bounds => (by omega : False).elim⟩
  | succ fuel ih =>
      let first := allocateAt input depth count item state position available nonnegative
      change (allocateFrom input depth count item (position + 1) fuel first.after
        first.remaining first.remaining_nonnegative).after.current.slots[index]? = some (.live survivor) at present
      have later := ih (position + 1) first.after first.remaining first.remaining_nonnegative present
      have earlier := an_original_zero_survives_one_scan_position_only_without_a_matching_review
        input depth count item state position available nonnegative index survivor zero later.1
      refine ⟨earlier.1,?_⟩
      intro bounds
      by_cases same : index = position
      · exact earlier.2 same
      · exact later.2 ⟨by omega,by omega⟩

theorem a_zero_survives_a_whole_actual_allocation_only_without_a_matching_review
    (item : ActualItem input depth count) (movement : Movement input depth count item)
    (state : (process input depth count).GeneratedState)
    (index : Nat) (survivor : AdmittedObligation (vocabulary input depth count))
    (zero : survivor.residual = 0)
    (present : (allocate input depth count item movement state).after.current.slots[index]? = some (.live survivor)) :
    state.current.slots[index]? = some (.live survivor) ∧ readReview input depth count survivor.content item = none := by
  have scan := a_zero_survives_the_original_scan_only_outside_all_matching_reviews
    input depth count item state.current.slots.length 0 state movement.quantity
      (movement.quantity_nonnegative input depth count) index survivor zero present
  have within : index < state.current.slots.length := by
    by_contra outside
    rw [List.getElem?_eq_none (Nat.le_of_not_lt outside)] at scan
    cases scan.1
  exact ⟨scan.1,scan.2 ⟨Nat.zero_le _,by omega⟩⟩

theorem a_zero_survives_one_actual_payment_only_without_a_matching_review
    (item : ActualItem input depth count) (state : (process input depth count).GeneratedState)
    (instrument : Instrument) (debtor holder : Party) (quantity : ℚ)
    (operation : (item.instruction input depth count).request.operation = .settle instrument debtor holder quantity)
    (accepted : (item.interpreter input depth count).Valid (item.instruction input depth count).before
      (item.instruction input depth count).request)
    (index : Nat) (survivor : AdmittedObligation (vocabulary input depth count))
    (zero : survivor.residual = 0)
    (present : ((consume input depth count item state).next input depth count).current.slots[index]? = some (.live survivor)) :
    state.current.slots[index]? = some (.live survivor) ∧ readReview input depth count survivor.content item = none := by
  obtain ⟨movement,parsed,_,_⟩ := an_actual_payment_generates_its_original_movement
    input depth count item instrument debtor holder quantity operation accepted
  rw [the_actual_settlement_next_is_the_same_original_allocator input depth count item instrument debtor holder quantity
    operation accepted state movement parsed] at present
  exact a_zero_survives_a_whole_actual_allocation_only_without_a_matching_review
    input depth count item movement state index survivor zero present

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger
