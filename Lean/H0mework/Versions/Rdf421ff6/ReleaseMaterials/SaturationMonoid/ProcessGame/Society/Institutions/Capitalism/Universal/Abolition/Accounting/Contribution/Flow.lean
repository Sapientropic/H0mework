import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Contribution.Bounds

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Contribution

open ResponsibilityLifecycle
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count : Nat)

def originalEvent : LifecycleEvent (Epoch.Finance.vocabulary input depth count) → Epoch.Finance.Event input depth count
  | .admitted _ payload => payload.sourceEvent
  | .carried _ _ source _ | .terminal _ _ source _ | .superseded _ _ source _
  | .bearerReleased _ _ source _ => source
  | .reopened _ _ payload => payload.sourceEvent

def paidAt (index : Nat) (event : LifecycleEvent (Epoch.Finance.vocabulary input depth count)) : ℚ :=
  if event.slot = index then actualPaid input depth count (originalEvent input depth count event) else 0

def principalAt (state : ResponsibilityState (Epoch.Finance.vocabulary input depth count)) (index : Nat) : ℚ :=
  match state.slots[index]? with
  | some slot => Financial.total input (Epoch.Finance.slotBalance input depth count slot)
  | none => 0

def receivedAlong {first last : ResponsibilityState (Epoch.Finance.vocabulary input depth count)}
    (run : (Epoch.Finance.process input depth count).Run first last) (index : Nat) : ℚ :=
  (run.events.map (paidAt input depth count index)).sum

private theorem admission_is_not_an_extra_payment
    (claim : Epoch.Finance.Claim input depth count) :
    actualPaid input depth count (Epoch.Finance.admission input depth count claim).sourceEvent = 0 := by
  cases claim <;> rfl

private theorem admitted_slot_does_not_pay_an_old_claim
    (state : ResponsibilityState (Epoch.Finance.vocabulary input depth count))
    (claim : Epoch.Finance.Claim input depth count) (index : Nat) :
    paidAt input depth count index
      (NativeResponsibilityProcess.Edge.admit (P := Epoch.Finance.process input depth count)
        (source := state) claim).lifecycleEvent = 0 := by
  change (if state.slots.length = index then actualPaid input depth count
    (Epoch.Finance.admission input depth count claim).sourceEvent else 0) = 0
  rw [admission_is_not_an_extra_payment]
  simp

private theorem original_cross_source
    (state : ResponsibilityState (Epoch.Finance.vocabulary input depth count))
    (index : Fin state.slots.length) (obligation : AdmittedObligation (Epoch.Finance.vocabulary input depth count))
    (present : state.slots.get index = .live obligation)
    (boundary : Epoch.Finance.Boundary input depth count obligation) :
    originalEvent input depth count
      (NativeResponsibilityProcess.Edge.cross (P := Epoch.Finance.process input depth count)
        index obligation present boundary).lifecycleEvent = boundary.event := by
  dsimp only [NativeResponsibilityProcess.Edge.lifecycleEvent,Epoch.Finance.process]
  unfold Epoch.Finance.boundaryDisposition
  split <;> rfl

private theorem original_cross_slot
    (state : ResponsibilityState (Epoch.Finance.vocabulary input depth count))
    (index : Fin state.slots.length) (obligation : AdmittedObligation (Epoch.Finance.vocabulary input depth count))
    (present : state.slots.get index = .live obligation)
    (boundary : Epoch.Finance.Boundary input depth count obligation) :
    (NativeResponsibilityProcess.Edge.cross (P := Epoch.Finance.process input depth count)
      index obligation present boundary).lifecycleEvent.slot = index.val := by
  dsimp only [NativeResponsibilityProcess.Edge.lifecycleEvent,Epoch.Finance.process]
  unfold Epoch.Finance.boundaryDisposition
  split <;> rfl

theorem every_old_slot_accounts_for_its_original_payment
    {state : ResponsibilityState (Epoch.Finance.vocabulary input depth count)}
    (edge : (Epoch.Finance.process input depth count).Edge state) (index : Nat)
    (inside : index < state.slots.length) :
    principalAt input depth count edge.target index + paidAt input depth count index edge.lifecycleEvent =
      principalAt input depth count state index := by
  cases edge with
  | admit claim =>
      have noPayment := admitted_slot_does_not_pay_an_old_claim input depth count state claim index
      rw [noPayment,add_zero]
      change (match (state.slots ++ [_])[index]? with
        | some slot => Financial.total input (Epoch.Finance.slotBalance input depth count slot)
        | none => 0) = _
      rw [List.getElem?_append_left inside]
      rfl
  | cross changed obligation present boundary =>
      have source := original_cross_source input depth count state changed obligation present boundary
      have position := original_cross_slot input depth count state changed obligation present boundary
      by_cases same : changed.val = index
      · have beforeRead : state.slots[index]? = some (.live obligation) := by
          rw [← same,List.getElem?_eq_getElem changed.isLt]
          exact congrArg some present
        have afterRead := (Epoch.Finance.process input depth count).cross_target_slot changed obligation present boundary
        rw [same] at afterRead
        have payment : paidAt input depth count index
            (NativeResponsibilityProcess.Edge.cross (P := Epoch.Finance.process input depth count)
              changed obligation present boundary).lifecycleEvent = actualPaid input depth count boundary.event := by
          simp only [paidAt,position,same,if_true,source]
        rw [payment]
        simp only [principalAt]
        rw [afterRead,beforeRead]
        exact an_actual_boundary_cannot_refill_its_original_principal input depth count obligation boundary
      · have afterRead : (NativeResponsibilityProcess.Edge.cross (P := Epoch.Finance.process input depth count)
              changed obligation present boundary).target.slots[index]? = state.slots[index]? := by
          change (state.slots.set changed _)[index]? = _
          rw [List.getElem?_set,if_neg same]
        simp only [principalAt,afterRead,paidAt,position,if_neg same,add_zero]
  | reopen _ _ _ impossible => exact impossible.elim

theorem an_original_slot_keeps_its_total_receipt_and_residual_exact
    {first last : ResponsibilityState (Epoch.Finance.vocabulary input depth count)}
    (run : (Epoch.Finance.process input depth count).Run first last) (index : Nat)
    (inside : index < first.slots.length) :
    principalAt input depth count last index + receivedAlong input depth count run index =
      principalAt input depth count first index := by
  induction run with
  | nil => simp only [receivedAlong,NativeResponsibilityProcess.Run.events,List.map_nil,List.sum_nil,add_zero]
  | step prior edge inherited =>
      have lengthLe := (Epoch.Finance.run_retains_all_claims input depth count prior).length_le
      simp only [List.length_map] at lengthLe
      have step := every_old_slot_accounts_for_its_original_payment input depth count edge index (lt_of_lt_of_le inside lengthLe)
      simp only [receivedAlong,NativeResponsibilityProcess.Run.events,List.map_append,List.sum_append,
        List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
      change _ + (receivedAlong input depth count prior index + _) = _
      linarith

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Contribution
