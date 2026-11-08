import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.FuelReentryConsumer

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 240000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.FuelReentryControls
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open FuelControlSource FuelControlControls

abbrev cursor (control : Controller) (rivals : Nat → Opponent code) := (FuelControlConsumer.finished control rivals).cursor
abbrev old (control : Controller) (rivals : Nat → Opponent code) := FuelReentrySource.bound (cursor control rivals)
abbrev arrival (control : Controller) (rivals : Nat → Opponent code) := FuelReentrySource.incoming (cursor control rivals)

theorem actual_normal_withheld_and_late_first_rounds_all_generate_their_own_next_round :
    FuelReentrySource.status (cursor never delayed) = .decided true ∧
      FuelReentrySource.status (cursor always latest) = .decided true ∧
      FuelReentrySource.status (cursor lateRelease latest) = .decided true := by
  exact ⟨FuelReentryConsumer.every_actual_compliant_first_window_generates_its_own_new_paid_round never delayed
      ((conforms_iff _ _).mp actual_remaining_budget_requires_delivery_at_the_last_external_opportunity.2.2.2.2.1),
    FuelReentryConsumer.every_actual_compliant_first_window_generates_its_own_new_paid_round always latest
      ((conforms_iff _ _).mp every_opportunity_can_really_be_withheld_without_forced_restoration.1),
    FuelReentryConsumer.every_actual_compliant_first_window_generates_its_own_new_paid_round lateRelease latest
      ((conforms_iff _ _).mp a_late_actual_signature_cannot_borrow_a_missing_send_or_receipt.1)⟩

theorem all_three_actual_histories_generate_private_admission :
    (MaterialRoundSource.inspect (old never delayed) window (arrival never delayed)).isSome = true ∧
      (MaterialRoundSource.inspect (old always latest) window (arrival always latest)).isSome = true ∧
      (MaterialRoundSource.inspect (old lateRelease latest) window (arrival lateRelease latest)).isSome = true := by
  decide +kernel

def normalEntry := (MaterialRoundSource.inspect (old never delayed) window (arrival never delayed)).get
  all_three_actual_histories_generate_private_admission.1
def heldEntry := (MaterialRoundSource.inspect (old always latest) window (arrival always latest)).get
  all_three_actual_histories_generate_private_admission.2.1
def lateEntry := (MaterialRoundSource.inspect (old lateRelease latest) window (arrival lateRelease latest)).get
  all_three_actual_histories_generate_private_admission.2.2
abbrev normal := MaterialRoundSource.actual (old never delayed) window (arrival never delayed) normalEntry
abbrev held := MaterialRoundSource.actual (old always latest) window (arrival always latest) heldEntry
abbrev late := MaterialRoundSource.actual (old lateRelease latest) window (arrival lateRelease latest) lateEntry

theorem old_blocked_decisions_are_not_rewritten_by_later_actual_success :
    FuelControlSource.result (FuelReentryConsumer.produce always latest).first = .blocked .missingSourceSubject ∧
      FuelControlSource.result (FuelReentryConsumer.produce lateRelease latest).first = .blocked .missingQuorum ∧
      (FuelReentryConsumer.produce always latest).first.omissions = [(0,0),(2,0),(4,0)] ∧
      (FuelReentryConsumer.produce lateRelease latest).first.omissions = [(0,0),(2,0)] ∧
      (MaterialRoundSource.before held 6).claims () 1 2 = 6 ∧
      (MaterialRoundSource.before late 6).claims () 1 2 = 5 := by decide +kernel

theorem actual_surviving_stock_and_debt_are_carried_across_the_distinct_histories :
    (MaterialRoundSource.before normal 6).claims () 1 2 = 5 ∧
      (MaterialRoundSource.before normal 6).stock 1 .service = 0 ∧
      (MaterialRoundSource.before held 6).stock 1 .service = 3 ∧
      (MaterialRoundSource.before late 6).stock 1 .service = 2 ∧
      (MaterialRoundSource.before normal 6).stock 2 .waste = 0 ∧
      (MaterialRoundSource.before normal 6).stock 2 .energy = 0 ∧
      (MaterialRoundSource.before normal 6).stock 2 .labor = 0 := by decide +kernel

theorem no_third_supply_is_minted_after_the_two_paid_normal_rounds :
    FuelMaterialSource.incoming normal 6 = [] ∧ FuelMaterialSource.status normal 6 = .phaseRefused ∧
      (MaterialRoundSource.prepared normal 6 []).claims () 1 2 = 5 ∧
      (MaterialRoundSource.inspect normal 6 []).isSome = false := by decide +kernel

abbrev emitter := MaterialRoundSource.emitter (old never delayed) window (arrival never delayed) normalEntry
abbrev input := MaterialRoundSource.input (old never delayed) window (arrival never delayed) normalEntry
abbrev protocol := MaterialRoundSource.protocol (old never delayed) window (arrival never delayed) normalEntry
abbrev environment := MaterialRoundSource.environment (old never delayed) window (arrival never delayed) normalEntry
abbrev vocabulary := MaterialRoundSource.vocabulary (old never delayed) window (arrival never delayed) normalEntry
abbrev encoding := MaterialRoundSource.encoding (old never delayed) window (arrival never delayed) normalEntry
abbrev reception := MaterialRoundSource.reception (old never delayed) window (arrival never delayed) normalEntry
abbrev slot := MaterialRoundSource.slot (old never delayed) window (arrival never delayed) normalEntry

theorem new_payment_requires_its_own_source_delivery_timing_and_quorum :
    slot ≠ originalScope ∧
      SubjectQuorum.produce emitter input 0 protocol environment vocabulary encoding reception 0 6 6 originalScope 1 = .blocked .missingSourceSubject ∧
      SubjectQuorum.produce emitter input 0 protocol (fun _ _ _ => none) vocabulary encoding reception 0 6 6 slot 1 = .blocked .missingQuorum ∧
      SubjectQuorum.produce emitter input 0 protocol environment vocabulary encoding ⟨fun _ _ => slot,0⟩ 0 6 6 slot 1 = .blocked .missingQuorum ∧
      SubjectQuorum.produce emitter input 0 protocol environment vocabulary encoding reception 0 6 6 slot 2 = .blocked .missingQuorum ∧
      SubjectQuorum.produce emitter input 0 protocol environment vocabulary encoding reception 0 6 5 slot 1 = .blocked .outsideBudgetWindow := by
  and_intros <;> decide +kernel

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.FuelReentryControls
