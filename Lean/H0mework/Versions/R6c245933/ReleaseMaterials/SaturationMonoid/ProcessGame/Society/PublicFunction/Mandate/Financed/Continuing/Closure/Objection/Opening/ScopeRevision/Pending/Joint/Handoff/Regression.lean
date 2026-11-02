import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Reserve
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.EpochRuntime
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Future.Regression

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 24000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Regression

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
noncomputable section
abbrev authority := Future.Regression.ready
abbrev inventory := Future.Regression.inventory

def late := Joint.submit authority (Joint.submit authority inventory []) []
def reviewed := Future.advance authority late .revision

theorem actual_late_review_generates_a_fresh_scope :
    (Handoff.choose (Pending.B authority) reviewed.inputs).isSome = true := by decide +kernel

def fresh := (Handoff.choose (Pending.B authority) reviewed.inputs).get actual_late_review_generates_a_fresh_scope

def debts (account : Pending.Joint.Finance.Account) := account.current.slots.map fun slot =>
  ((Financial.Family.slotClaim Pending.Joint.Finance.sources slot).2.quantity,
    (Financial.Family.slotBalance Pending.Joint.Finance.sources slot) false,
    (Financial.Family.slotBalance Pending.Joint.Finance.sources slot) true)

theorem new_task_window_and_slots_are_generated_from_the_actual_review_successor :
    fresh.actor = false ∧ authority.task.deadline < fresh.task.earliest ∧
    fresh.task.slots.length = (Pending.B authority).source.seed.task.slots.length ∧
    (I fresh).initial = Pending.current authority reviewed.inputs := by
  exact ⟨by decide +kernel, fresh.new_window_is_after_the_actual_expired_scope, by decide +kernel, rfl⟩

theorem reserved_new_epoch_really_pays_each_original_content_and_keeps_the_old_principal :
    ((select fresh (start fresh)).map Paid.method) = some .reserved ∧
    (∀ index, (source fresh).SlotPaid (start fresh) (firstWord fresh) index) ∧
    debts reviewed.finance = [(7,0,5)] ∧ debts (Finance.account authority late fresh 4) = [(7,0,2)] := by decide +kernel

theorem actual_reserved_scope_has_its_original_production_and_retained_exit_material :
    (∃ payment : Paid fresh (start fresh), select fresh (start fresh) = some payment ∧ payment.method = .reserved ∧
      reserveProduction fresh (start fresh) ∈ (law fresh).rawItems
        (actual fresh 1).before (actual fresh 1).submitted) ∧
    MaterialHealthy (current fresh 4) ∧ ExitEnvelope (current fresh 4) := by
  have selection := reserved_new_epoch_really_pays_each_original_content_and_keeps_the_old_principal.1
  cases chosen : select fresh (start fresh) with
  | none => simp only [chosen,Option.map_none] at selection; cases selection
  | some payment =>
      have method : payment.method = .reserved := by
        simpa only [chosen,Option.map_some,Option.some.injEq] using selection
      have production := selected_reserved_word_really_produces_its_extra_service fresh _ payment chosen method
      refine ⟨⟨payment,rfl,method,?_⟩,
        selected_actual_service_and_response_preserve_exit_material fresh payment chosen⟩
      rw [first_word_is_actually_emitted,first_word_uses_the_actual_start]
      exact production.1

theorem early_review_and_unpaid_review_cannot_manufacture_a_new_scope :
    (Handoff.choose (Pending.B authority) (Future.advance authority inventory .revision).inputs).isNone = true ∧
    (Handoff.choose (Pending.B authority) (Future.advance authority Future.Regression.exhausted .revision).inputs).isNone = true := by
  decide +kernel

def dry := Joint.submit authority late [⟨false,[],.resource,[],.use false [(.feedstock,3)] .external⟩]
def dryReviewed := Future.advance authority dry .revision

theorem material_exhaustion_preserves_the_actual_scope_handoff :
    (Handoff.choose (Pending.B authority) dryReviewed.inputs).isSome = true := by decide +kernel

def dryFresh := (Handoff.choose (Pending.B authority) dryReviewed.inputs).get material_exhaustion_preserves_the_actual_scope_handoff

theorem exhausted_new_epoch_reports_failed_plans_and_does_not_clear_the_original_debt :
    (select dryFresh (start dryFresh)).isNone = true ∧
    debts (Finance.account authority dry dryFresh 4) = [(7,0,5)] ∧
    ¬ (source dryFresh).SlotPaid (start dryFresh) (firstWord dryFresh) ⟨0, by decide +kernel⟩ := by decide +kernel

def financedReview := Future.advance authority Future.Regression.afterAdmission .revision

theorem another_actual_history_generates_its_own_new_scope :
    (Handoff.choose (Pending.B authority) financedReview.inputs).isSome = true := by decide +kernel

def financedFresh := (Handoff.choose (Pending.B authority) financedReview.inputs).get another_actual_history_generates_its_own_new_scope

theorem a_paid_but_depleting_financing_word_is_rejected_as_a_replacement :
    (select financedFresh (start financedFresh)).isNone = true ∧
    (∀ item ∈ (law financedFresh).rawItems (start financedFresh)
        (serviceWord financedFresh (start financedFresh) .financed), (law financedFresh).Valid item.before item.request) ∧
    ServiceAdequate (law financedFresh) (start financedFresh) financedFresh.task
      (serviceWord financedFresh (start financedFresh) .financed) ∧
    (decodePaidOpening financedFresh (start financedFresh)
      (serviceWord financedFresh (start financedFresh) .financed)).isSome = true ∧
    ¬ ExitEnvelope ((law financedFresh).next (start financedFresh)
      (serviceWord financedFresh (start financedFresh) .financed)) := by decide +kernel

theorem the_blocked_actual_source_keeps_the_original_issued_principal :
    debts (Finance.account authority Future.Regression.afterAdmission financedFresh 4) = [(7,0,1)] := by
  decide +kernel

abbrev publicScopeReviewHandoffFacade := Runtime.facade authority late
abbrev publicScopeReviewedEpochFacade := EpochRuntime.facade authority late fresh
abbrev publicScopeReviewEarlyFacade := Runtime.facade authority inventory
abbrev publicScopeReviewedDryFacade := EpochRuntime.facade authority dry dryFresh
abbrev publicScopeReviewedFinanceFacade := EpochRuntime.facade authority Future.Regression.afterAdmission financedFresh

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Regression
