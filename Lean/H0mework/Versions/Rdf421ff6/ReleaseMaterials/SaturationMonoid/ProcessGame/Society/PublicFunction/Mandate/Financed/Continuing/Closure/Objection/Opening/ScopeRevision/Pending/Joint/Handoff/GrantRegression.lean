import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Regression

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 24000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Grant.Regression

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
noncomputable section
abbrev authority := Handoff.Regression.authority
abbrev paidFresh := Handoff.Regression.financedFresh
abbrev paidLegacy := Handoff.Regression.financedReview

def paidInventory := Grant.inventory paidFresh paidLegacy.grants 4

theorem the_actual_new_law_emits_two_distinct_paid_boundary_receipts_in_order :
    (Grant.receipts paidFresh 0 4).map (Receipt.command paidFresh) = [.exit,.review] ∧
    (Grant.receipts paidFresh 0 4).map (Receipt.kind paidFresh) = [.maintained,.maintained] := by decide +kernel

theorem every_old_grant_is_kept_with_two_actual_native_crossings :
    paidInventory.length = 1 ∧
    paidInventory.map (fun entry => entry.continuation.state.history.length - entry.original.history.state.history.length) = [2] ∧
    paidInventory.map (fun entry => entry.continuation.crossing.events.map LifecycleEvent.kind) = [[.maintained,.maintained]] := by decide +kernel

def dry := Joint.submit authority Future.Regression.afterAdmission [⟨false,[],.resource,[],.use false [(.feedstock,2)] .external⟩]
def dryReviewed := Future.advance authority dry .revision

theorem actual_old_grant_and_paid_review_survive_material_exhaustion :
    dryReviewed.grants.length = 1 ∧ (Handoff.choose (Pending.B authority) dryReviewed.inputs).isSome = true := by decide +kernel

def dryFresh := (Handoff.choose (Pending.B authority) dryReviewed.inputs).get actual_old_grant_and_paid_review_survive_material_exhaustion.2

def refusedInventory := Grant.inventory dryFresh dryReviewed.grants 4

theorem a_new_grant_with_zero_exit_funds_produces_real_refusals_and_keeps_old_responsibility :
    (select dryFresh (start dryFresh)).isNone = true ∧
    (current dryFresh 3).technology.holder = some true ∧ (current dryFresh 3).stock true .service = 0 ∧
    (Grant.receipts dryFresh 0 4).map (Receipt.command dryFresh) = [.exit,.review] ∧
    (Grant.receipts dryFresh 0 4).map (Receipt.kind dryFresh) = [.deferred,.deferred] ∧
    refusedInventory.length = 1 ∧
    refusedInventory.map (fun entry => entry.continuation.crossing.events.map LifecycleEvent.kind) = [[.deferred,.deferred]] := by decide +kernel

theorem accepting_a_new_epoch_never_renames_the_original_live_slot
    (record : Mandate.Challenge.Cross.GrantResident (Pending.B authority) paidLegacy.inputs) (count : Nat) :
    (Grant.continued paidFresh record count).state.slots = record.history.state.slots :=
  every_original_slot_and_admission_is_literal paidFresh record count

abbrev publicScopeCrossGrantPaidFacade := EpochRuntime.facade authority Future.Regression.afterAdmission paidFresh
abbrev publicScopeCrossGrantRefusedFacade := EpochRuntime.facade authority dry dryFresh
abbrev publicScopeCrossGrantEmptyFacade := Handoff.Regression.publicScopeReviewedEpochFacade

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Grant.Regression
