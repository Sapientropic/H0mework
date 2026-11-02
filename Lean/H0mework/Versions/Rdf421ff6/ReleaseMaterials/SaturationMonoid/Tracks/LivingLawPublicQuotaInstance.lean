import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Quota.Runtime
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Quota.FinanceRegression

set_option autoImplicit false

namespace SaturationMonoid.Tracks.LivingLawPublicQuotaInstance

open ProcessGame.Society.PublicFunction.Distributed.Reaction
open ProcessGame.Society.Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

abbrev original := Feedback.Quota.Regression.original
abbrev input := Feedback.Quota.Regression.input
abbrev position := Feedback.Quota.Regression.position
abbrev source := Feedback.Quota.Regression.source
abbrev publicQuotaFacade := Feedback.Quota.Runtime.facade original input rfl rfl 2 position 0 rfl
abbrev activated := Feedback.Quota.Runtime.activated original input rfl rfl 2 position 0 rfl
abbrev refusedOriginal := Feedback.Quota.Regression.refusedOriginal
abbrev refusedInput := Feedback.Quota.Regression.refusedInput
abbrev publicRefusedQuotaFacade := Feedback.Quota.Runtime.facade refusedOriginal refusedInput rfl rfl 2 position 0 rfl
abbrev refusedActivated := Feedback.Quota.Runtime.activated refusedOriginal refusedInput rfl rfl 2 position 0 rfl

theorem actual_supported_payment_and_uncovered_balance_are_consumed_with_the_original_next :
    (source.actualExecution 4).submitted = [Feedback.Quota.Regression.payment] ∧
      (source.actualExecution 4).after.claims () true false = 7 ∧
      Financial.outstanding source.input (Native.generate source 4).finance.current = 0 ∧
      (Native.generate source 4).finance.current.slots.length = 2 ∧
      HEq (publicQuotaFacade.readoutAt (activated 5) .quota)
        ((activated 5).tick.generated.projectionOutcome (.component ())) ∧
      HEq (publicQuotaFacade.readoutAt (activated 5) (.previous .feedback))
        ((activated 5).tick.generated.projectionOutcome (.inherited (.component ()))) ∧
      HEq (activated 5).tick.generated.wholeLedgerWriteBack
        ((activated 5).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt (activated 5).current.visit.current) ∧
      (activated 5).tick.nextCurrent = publicQuotaFacade.process.stateAt
        (publicQuotaFacade.process.successor (activated 5).state) := by
  rcases Feedback.Quota.Regression.actual_capped_payment_uses_both_original_slots_and_keeps_unbacked_balance with
    ⟨_old, requested, _debtor, _creditor, raw, native, slots, _memory, _queue⟩
  have quota := publicQuotaFacade.readoutAt_factorizes (activated 5) .quota
  have feedback := publicQuotaFacade.readoutAt_factorizes (activated 5) (.previous .feedback)
  exact ⟨requested, raw, native, slots, quota.2.2.2.1, feedback.2.2.2.1, quota.2.2.1, quota.2.2.2.2⟩

theorem actual_movement_full_allocation_is_consumed_by_the_same_root :
    (Financial.allocate source.input Feedback.Quota.Regression.origin Feedback.Quota.Regression.before
      Feedback.Quota.Regression.movement.quantity
      (Feedback.Quota.Regression.movement.quantity_nonnegative source.input)).remaining = 0 ∧
      HEq (publicQuotaFacade.readoutAt (activated 5) (.previous (.previous .responsibilities)))
        ((activated 5).tick.generated.projectionOutcome (.inherited (.inherited (.component ())))) ∧
      HEq (activated 5).tick.generated.wholeLedgerWriteBack
        ((activated 5).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt (activated 5).current.visit.current) ∧
      (activated 5).tick.nextCurrent = publicQuotaFacade.process.stateAt
        (publicQuotaFacade.process.successor (activated 5).state) := by
  have native := publicQuotaFacade.readoutAt_factorizes (activated 5) (.previous (.previous .responsibilities))
  exact ⟨Feedback.Quota.Regression.original_slot_quota_is_exhausted_and_uncovered_claims_are_preserved.1,
    native.2.2.2.1, native.2.2.1, native.2.2.2.2⟩

theorem actual_refusal_keeps_both_debts_on_its_own_root :
    Feedback.Quota.Regression.blocked
        (Feedback.Quota.proposal refusedOriginal refusedInput 2 position) = true ∧
      (Feedback.Quota.Regression.refusedSource.actualExecution 4).after.claims () true false = 9 ∧
      Financial.outstanding Feedback.Quota.Regression.refusedSource.input
        (Native.generate Feedback.Quota.Regression.refusedSource 4).finance.current = 2 ∧
      HEq (publicRefusedQuotaFacade.readoutAt (refusedActivated 5) .quota)
        ((refusedActivated 5).tick.generated.projectionOutcome (.component ())) ∧
      HEq (refusedActivated 5).tick.generated.wholeLedgerWriteBack
        ((refusedActivated 5).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          (refusedActivated 5).current.visit.current) ∧
      (refusedActivated 5).tick.nextCurrent = publicRefusedQuotaFacade.process.stateAt
        (publicRefusedQuotaFacade.process.successor (refusedActivated 5).state) := by
  rcases Feedback.Quota.Regression.the_exact_capped_candidate_is_rechecked_and_refusal_keeps_both_debts with
    ⟨blocked, _submitted, _debtor, _creditor, raw, native⟩
  have quota := publicRefusedQuotaFacade.readoutAt_factorizes (refusedActivated 5) .quota
  exact ⟨blocked, raw, native, quota.2.2.2.1, quota.2.2.1, quota.2.2.2.2⟩

def paidDispositionFromRuntime : Feedback.Quota.Runtime.Disposition original input 2 position 0 rfl :=
  match publicQuotaFacade.readoutAt (activated 5) .quota with
  | .inl active => active.2 rfl
  | .inr impossible => nomatch impossible

theorem paidDisposition_is_generated :
    paidDispositionFromRuntime = Feedback.Quota.Runtime.generate original input 2 position 0 rfl := rfl

theorem original_issue_sources_are_generated_in_the_actual_quota_payload :
    (∀ ordinal, ordinal ≤ 5 →
      ((Financial.accountAt source.input ordinal).current.slots.map (Financial.slotClaim source.input)).map
          (Identity.claimImage original.code source.input) =
        ((Financial.accountAt original.input ordinal).current.slots.map (Financial.slotClaim original.input)).map
          (Identity.claimImage original.code original.input)) ∧
      HEq (publicQuotaFacade.readoutAt (activated 5) .quota)
        ((activated 5).tick.generated.projectionOutcome (.component ())) ∧
      HEq (activated 5).tick.generated.wholeLedgerWriteBack
        ((activated 5).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt (activated 5).current.visit.current) ∧
      (activated 5).tick.nextCurrent = publicQuotaFacade.process.stateAt
        (publicQuotaFacade.process.successor (activated 5).state) := by
  have quota := publicQuotaFacade.readoutAt_factorizes (activated 5) .quota
  exact ⟨paidDispositionFromRuntime.prior_issue_sources, quota.2.2.2.1, quota.2.2.1, quota.2.2.2.2⟩

theorem complete_financial_transport_is_consumed_with_the_actual_supported_payment :
    paidDispositionFromRuntime.finance_transport.accepted = true ∧
      Feedback.Quota.amount original input 2 position ≤ Feedback.Quota.support source 2 position ∧
      (∀ instrument debtor creditor,
        Financial.BalanceConservation.ledgerClaims source.input (Feedback.Quota.account source 2).current
            instrument debtor creditor =
          Financial.BalanceConservation.ledgerClaims original.input (Feedback.Quota.account original 2).current
            instrument debtor creditor) ∧
      Native.Coupling.eventHistory original.code source.input (Feedback.Quota.account source 2) =
        Native.Coupling.eventHistory original.code original.input (Feedback.Quota.account original 2) ∧
      HEq (publicQuotaFacade.readoutAt (activated 5) .quota)
        ((activated 5).tick.generated.projectionOutcome (.component ())) ∧
      HEq (activated 5).tick.generated.wholeLedgerWriteBack
        ((activated 5).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt (activated 5).current.visit.current) ∧
      (activated 5).tick.nextCurrent = publicQuotaFacade.process.stateAt
        (publicQuotaFacade.process.successor (activated 5).state) := by
  have approved := paidDispositionFromRuntime.finance_transport_accepted
  have transport := Feedback.Quota.Finance.Outcome.certificate original input 2 position 0 rfl
    paidDispositionFromRuntime.finance_transport approved
  have quota := publicQuotaFacade.readoutAt_factorizes (activated 5) .quota
  exact ⟨approved,
    paidDispositionFromRuntime.planned_bound, transport.transport.same_native_quota,
    transport.transport.events, quota.2.2.2.1, quota.2.2.1, quota.2.2.2.2⟩

theorem full_financial_state_and_independent_verifier_are_consumed_with_the_original_next :
    Feedback.Quota.Finance.Transport original input 2 position 0 rfl ∧
      Feedback.Quota.Finance.verify original input 2 position 0 rfl = true ∧
      HEq (publicQuotaFacade.readoutAt (activated 5) .quota)
        ((activated 5).tick.generated.projectionOutcome (.component ())) ∧
      HEq (activated 5).tick.generated.wholeLedgerWriteBack
        ((activated 5).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt (activated 5).current.visit.current) ∧
      (activated 5).tick.nextCurrent = publicQuotaFacade.process.stateAt
        (publicQuotaFacade.process.successor (activated 5).state) := by
  have transport := Feedback.Quota.Finance.Outcome.certificate original input 2 position 0 rfl
    paidDispositionFromRuntime.finance_transport paidDispositionFromRuntime.finance_transport_accepted
  have quota := publicQuotaFacade.readoutAt_factorizes (activated 5) .quota
  exact ⟨transport.transport,
    Feedback.Quota.Finance.every_generated_transport_is_independently_verified original input 2 position 0 rfl,
    quota.2.2.2.1, quota.2.2.1, quota.2.2.2.2⟩


end SaturationMonoid.Tracks.LivingLawPublicQuotaInstance
