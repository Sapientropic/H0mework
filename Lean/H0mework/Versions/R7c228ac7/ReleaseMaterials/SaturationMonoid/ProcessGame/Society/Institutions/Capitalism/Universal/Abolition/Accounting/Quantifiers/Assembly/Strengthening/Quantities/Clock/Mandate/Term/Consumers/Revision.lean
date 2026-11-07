import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate.Term.Revision.Cut
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Matching
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Regression

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate.Term.Consumers.Revision

open Source.Program PublicFunction PublicFunction.Mandate
open PublicFunction.Mandate.Financed (Action base)
open OutstandingSource.History.NativeService
open SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision
open SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Regression (ready)

noncomputable section

abbrev installed := epochBound ready
abbrev paidWords := epochInputs ready
private abbrev geometry := serviceGeometry installed [] paidWords

private def debitIndex (slot : installed.source.Slot) : Nat :=
  (Method.front ready .productive (epochBefore ready)).length + 3 + slot.val

private theorem indexed (slot : installed.source.Slot) :
    debitIndex slot < (originalInventory installed [] paidWords).length := by
  have each : ∀ key : installed.source.Slot,
    debitIndex key < (originalInventory installed [] paidWords).length := by decide +kernel
  exact each slot

private def debitAt (slot : installed.source.Slot) : Fin (originalInventory installed [] paidWords).length :=
  ⟨debitIndex slot, indexed slot⟩

private theorem actual_debits_match_each_generated_revision_slot :
    geometry.maximumMatchingCapacity = geometry.leftCarrier.card := by
  apply distinct_paid_positions_cover_the_original_services geometry debitAt
  · intro left _ right _ equal
    apply Fin.ext
    have same := congrArg Fin.val equal
    change debitIndex left = debitIndex right at same
    unfold debitIndex at same
    omega
  · intro slot _
    refine ⟨Finset.mem_univ _, ?_⟩
    let check (key : installed.source.Slot) :=
      @Decidable.decide (geometry.Feasible key (debitAt key)) (geometry.feasibleDecidable key (debitAt key))
    have each : (List.finRange installed.source.seed.task.slots.length).all check = true := by decide +kernel
    exact @of_decide_eq_true _ (geometry.feasibleDecidable slot (debitAt slot))
      (List.all_eq_true.mp each slot (List.mem_finRange _))

theorem the_installed_revision_pays_all_service_and_release_on_its_actual_next :
    PaidAt installed [] paidWords where
  slots := by
    intro slot
    apply ((serviceThread installed [] paidWords slot).native_terminal_iff_recorded installed.source).mpr
    exact (OutstandingSource.History.NativeService.native_terminal_iff_recorded installed.source paidWords slot 2).mp
      (Regression.all_four_new_services_have_real_native_settlement slot)
  distinctDebits := actual_debits_match_each_generated_revision_slot
  closed := by decide +kernel
  next := OutstandingSource.History.actual_next installed.source paidWords 1

def an_earlier_revision_has_an_original_unpaid_slot : Issue installed [] [] := by
  let slot : installed.source.Slot := ⟨0, by decide +kernel⟩
  exact .service slot (((serviceThread installed [] [] slot).native_live_iff_unpaid installed.source).mpr
    (Term.Revision.the_original_revision_bootstrap_preserves_every_unpaid_service ready slot))

theorem the_paid_revision_installs_the_tight_real_cutoff :
    IsLeast (times installed []) (((ready.task.deadline : ℚ) : ℝ) : EReal) ∧
      (type_of% ((generateEpoch ready).initial_exact)) ∧
      (type_of% ((generateEpoch ready).financial_support)) := by
  exact ⟨(Term.Revision.the_installed_revision_cutoff_is_tight_iff_first_service_can_pay_and_release ready).mpr
    ⟨epochWord ready (epochBefore ready), the_installed_revision_pays_all_service_and_release_on_its_actual_next⟩,
    (generateEpoch ready).initial_exact, (generateEpoch ready).financial_support⟩

theorem every_later_original_input_respects_the_installed_cutoff
    (inputs : List (List Action)) (ordinal : Nat) (late : 4 ≤ ordinal) (word : List Action)
    (actual : ActualCommand base ready.scope
      (OutstandingSource.History.currentAt installed.source inputs ordinal) word) :
    actual.command ≠ .accept ∧ actual.command ≠ .renew ∧ ∀ candidate, actual.command ≠ .propose candidate := by
  have ordinalExact : expiryOrdinal installed.source.seed.initial.clock ready.task.deadline 1 = 4 := by
    decide +kernel
  apply the_expired_original_root_cannot_propose_accept_or_renew installed inputs ordinal ?_ word actual
  exact (exact_expiry_for_owned_constant_duration installed inputs 1 (by decide) (fun _ => rfl) ordinal).mpr
    (ordinalExact.symm ▸ late)

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate.Term.Consumers.Revision
