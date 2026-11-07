import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Scan
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

open private allocateAt allocateLive allocateFrom Allocation.idle from
  H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Allocation

theorem an_actual_cross_cannot_leave_a_new_live_zero
    (original : AdmittedObligation (vocabulary input depth count))
    (boundary : Boundary input depth count original)
    (survivor : AdmittedObligation (vocabulary input depth count))
    (present : (boundaryDisposition input depth count boundary).targetSlot = .live survivor) : survivor.residual ≠ 0 := by
  unfold boundaryDisposition at present
  split at present
  · cases present
  · rename_i notZero
    cases present
    exact notZero

theorem an_original_zero_survives_one_scan_position_only_without_a_matching_review
    (item : ActualItem input depth count) (state : (process input depth count).GeneratedState)
    (position : Nat) (available : ℚ) (nonnegative : 0 ≤ available)
    (index : Nat) (survivor : AdmittedObligation (vocabulary input depth count))
    (zero : survivor.residual = 0)
    (present : (allocateAt input depth count item state position available nonnegative).after.current.slots[index]? = some (.live survivor)) :
    state.current.slots[index]? = some (.live survivor) ∧
      (index = position → readReview input depth count survivor.content item = none) := by
  unfold allocateAt at present
  split at present
  next within =>
    split at present
    next archive observed =>
      change state.current.slots[index]? = some (.live survivor) at present
      refine ⟨present,?_⟩
      intro same
      subst index
      have old : state.current.slots[position]? = some (.terminal archive) := by
        rw [List.getElem?_eq_getElem within]
        exact congrArg some observed
      rw [old] at present
      cases present
    next obligation observed =>
      split at present
      next absent =>
        change state.current.slots[index]? = some (.live survivor) at present
        refine ⟨present,?_⟩
        intro same
        subst index
        have old : state.current.slots[position]? = some (.live obligation) := by
          rw [List.getElem?_eq_getElem within]
          exact congrArg some observed
        have identity := ObligationSlot.live.inj (Option.some.inj (old.symm.trans present))
        rw [← identity]
        exact absent
      next review selected =>
        let cap := min available review.quantity
        let sound := live_sound input depth count state ⟨position,within⟩ obligation observed
        let boundary := reviewBoundary input depth count obligation sound.1 review cap sound.2
          (le_min nonnegative (review.quantity_nonnegative input depth count)) (min_le_right _ _)
        change (state.current.slots.set position (boundaryDisposition input depth count boundary).targetSlot)[index]? =
          some (.live survivor) at present
        by_cases same : index = position
        · subst index
          rw [List.getElem?_set_self within] at present
          exact (an_actual_cross_cannot_leave_a_new_live_zero input depth count obligation boundary survivor (Option.some.inj present) zero).elim
        · rw [List.getElem?_set_ne (Ne.symm same)] at present
          exact ⟨present,fun identity => (same identity).elim⟩
  next outside =>
    change state.current.slots[index]? = some (.live survivor) at present
    refine ⟨present,?_⟩
    intro same
    subst index
    rw [List.getElem?_eq_none (Nat.le_of_not_lt outside)] at present
    cases present

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger
