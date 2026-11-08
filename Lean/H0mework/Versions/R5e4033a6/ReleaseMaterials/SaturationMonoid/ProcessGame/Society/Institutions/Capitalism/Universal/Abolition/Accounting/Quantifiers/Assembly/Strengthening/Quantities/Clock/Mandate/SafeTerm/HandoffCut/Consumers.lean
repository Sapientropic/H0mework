import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate.SafeTerm.HandoffCut.Ledger
import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Continuation.Runtime

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate.SafeTerm.HandoffCut.Consumers

open Source.Program PublicFunction PublicFunction.Mandate
open PublicFunction.Mandate.Financed (base)
open SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection
open SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening
open SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision
open SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending
open SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint
open SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff
open SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World

noncomputable section

private def funded :=
  Followup.Joint.submit (Followup.Joint.initial (Financed.Continuing.Closure.start 12 []))
    [⟨false, [], .resource, [], .transfer false true [(.service, 1)]⟩]

private def authority := (ScopeRevision.choose funded).get (by decide +kernel)
private def pending := Pending.Joint.initial authority []
private def late := Pending.Joint.submit authority (Pending.Joint.submit authority pending []) []
private def first := (Handoff.choose (Pending.B authority) (Future.advance authority late .revision).inputs).get
  (by decide +kernel)
private def original := World.initial (Handoff.Continuation.Runtime.fromEpoch authority late first)
private abbrev epoch := Epoch.ofFresh first
private def supplied := World.submit original [Exit.production false, Exit.production false, Exit.production false]

private def payoff :=
  Repayment.Portfolio.word (Mandate.law base epoch.scope)
    (Handoff.debtPositions (World.current epoch supplied.inputs)) (World.current epoch supplied.inputs)

private def cleared := if payoff = [] then supplied else World.submit supplied payoff

private theorem clear : originalBalancesClear cleared :=
  (no_added_repayment_iff_all_original_staged_balances_clear cleared).mp (by decide +kernel)

private theorem passed : (produce cleared (nativeDraft cleared)).isInstalled = true := by
  decide +kernel

def installed : Installed cleared (nativeDraft cleared) :=
  Classical.choice (producer_installs_iff_actual_review_settlement_and_draft_are_paid.mp passed)

theorem the_actual_clear_cut_omits_the_empty_period_and_installs_earlier :
    (produce cleared (nativeDraft cleared)).isInstalled = true ∧
    (repaymentSuffix cleared).length = 0 ∧
    installed.fresh.ordinal = (oldCut cleared).inputs.length + 1 ∧
    installed.firstActual.before.clock + 1 = (World.current epoch (World.reviewed cleared).inputs).clock + 2 := by
  refine ⟨passed, (extra_periods_are_zero_iff_original_balances_clear cleared).mpr clear,
    a_clear_cut_recovers_the_latest_submitted_review cleared clear installed.fresh installed.chosen, ?_⟩
  rw [installed.first_service_starts_at_the_native_opening, a_clear_handoff_removes_one_real_clock_period cleared clear]
  ring

theorem the_earlier_actual_appointment_has_the_whole_original_evolution :
    Nonempty (Input.Event.Evolution ⟨_, cleared⟩ installed.packet) ∧
    Nonempty (Handoff.PaidOpening installed.fresh installed.firstActual.before installed.firstActual.submitted) :=
  ⟨⟨(.installed installed : Outcome cleared (nativeDraft cleared)).evolution⟩, ⟨installed.openingReceipt⟩⟩

theorem an_actual_owed_repayment_cannot_skip_the_paid_append :
    (repaymentSuffix supplied).length = 1 ∧ oldCut supplied = World.reviewed supplied := by
  have debt : World.repaymentWord supplied ≠ [] := by decide +kernel
  exact ⟨by simp [repaymentSuffix, debt],
    actual_debt_uses_the_existing_paid_repayment_cut _ (fun clear =>
      debt ((no_added_repayment_iff_all_original_staged_balances_clear _).mpr clear))⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate.SafeTerm.HandoffCut.Consumers
