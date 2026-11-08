import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate.SafeTerm.HandoffCut.Produce

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate.SafeTerm.HandoffCut

open Source.Program Institutions.Capitalism.Universal.Root PublicFunction PublicFunction.Mandate
open SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint
open SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff
open SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World

noncomputable section

variable {epoch : Epoch} {inventory : Inventory epoch} {draft : Drafts inventory}

def oldCutFinance (inventory : Inventory epoch) :
    (Financial.Family.process sources).Run inventory.finance.current (oldCut inventory).finance.current :=
  (World.financialRun inventory (World.reviewWord inventory)).concatRuns _
    (Install.submitAllRun (World.staged inventory) (repaymentSuffix inventory))

private def refusedFinance (inventory : Inventory epoch) :
    (Financial.Family.process sources).Run inventory.finance.current (refusedReviewCut inventory).finance.current := by
  unfold refusedReviewCut
  split
  · exact .nil
  · exact World.financialRun inventory (World.reviewWord inventory)

def Outcome.financeRun (result : Outcome inventory draft) :
    (Financial.Family.process sources).Run inventory.finance.current result.packet.2.finance.current :=
  match result with
  | .reviewBlocked .. => refusedFinance inventory
  | .repaymentBlocked .. | .cutBlocked .. | .draftBlocked .. => oldCutFinance inventory
  | .installed checked => (oldCutFinance inventory).concatRuns _
      (World.handoffAtFinancialRun (oldCut inventory) checked.fresh (draft checked.fresh))

theorem Outcome.complete_matrix (result : Outcome inventory draft) :
    Financial.Family.ledgerClaims sources result.packet.2.finance.current =
      (World.current result.packet.1 result.packet.2.inputs).claims :=
  result.packet.2.matrix

theorem Installed.original_service_keeps_the_literal_slots (installed : Installed inventory draft)
    (slot : epoch.source.Slot) :
    (World.openingCurrentService (oldCut inventory) installed.fresh (draft installed.fresh) slot).saved.state.current.slots =
      ((oldCut inventory).services slot).state.current.slots :=
  (World.openingCurrentService (oldCut inventory) installed.fresh (draft installed.fresh) slot).saved.slots

abbrev Installed.firstActual (installed : Installed inventory draft) :=
  OutstandingSource.History.actualExecution (Handoff.source installed.fresh) (draft installed.fresh) 1

def Installed.openingReceipt (installed : Installed inventory draft) :
    Handoff.PaidOpening installed.fresh installed.firstActual.before installed.firstActual.submitted :=
  (Install.originalOpening? (oldCut inventory) installed.fresh (draft installed.fresh)).get installed.opening.2.2.1

theorem Installed.first_service_starts_at_the_native_opening (installed : Installed inventory draft) :
    installed.firstActual.before.clock = (World.current epoch (oldCut inventory).inputs).clock + 2 :=
  (Install.registered_cutoff_equals_first_service_commit installed.fresh (draft installed.fresh)).1

theorem Installed.zero_extra_tick_advances_the_appointment_date_by_one
    (installed : Installed inventory draft) (clear : originalBalancesClear inventory)
    (legacy : Handoff.Ready epoch.bound (World.reviewed inventory).inputs) :
    installed.firstActual.before.clock + 1 = (Handoff.actual legacy 1).before.clock := by
  rw [installed.first_service_starts_at_the_native_opening]
  have legacyStart : (Handoff.actual legacy 1).before.clock =
      (World.current epoch (World.reviewed inventory).inputs).clock + 2 :=
    (Install.registered_cutoff_equals_first_service_commit legacy (Handoff.epochInputs legacy)).1
  rw [legacyStart, a_clear_handoff_removes_one_real_clock_period inventory clear]
  ring

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate.SafeTerm.HandoffCut
