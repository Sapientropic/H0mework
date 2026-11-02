import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Source

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Finance

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle
open Followup Financial.Family.BalanceConservation
variable {fuel : ℚ} {old : Followup.Joint.Inventory fuel} (authority : ScopeRevision.Ready old)
  {originInputs : List (List Action)} (inventory : Pending.Joint.Inventory authority originInputs)

noncomputable abbrev reviewed := Future.advance authority inventory .revision
noncomputable abbrev oldBound := Pending.B authority
noncomputable abbrev sources := Pending.Joint.Finance.sources

variable (fresh : Handoff.Ready (oldBound authority) (reviewed authority inventory).inputs)

noncomputable def account (count : Nat) := Financial.Family.continueVisits sources (Handoff.I fresh) 0 count
  (reviewed authority inventory).finance

theorem original_compatible : Compatible sources (Handoff.I fresh) (reviewed authority inventory).finance.current := by
  have old := (reviewed authority inventory).financeGenerated.compatible authority []
  intro claim member
  exact old claim member

theorem initial_matrix : Financial.Family.ledgerClaims sources (reviewed authority inventory).finance.current = (Handoff.I fresh).initial.claims :=
  Pending.Joint.financial_matrix_at_every_actual_cut authority (reviewed authority inventory)

theorem matrix (count : Nat) : Financial.Family.ledgerClaims sources (account authority inventory fresh count).current =
    (Handoff.current fresh count).claims := by
  simpa only [Nat.zero_add, sources, Pending.Joint.Finance.sources, id_eq, account,
    Handoff.current, OutstandingSource.History.currentAt] using continueVisits_claims_source sources (Handoff.I fresh) 0 count (reviewed authority inventory).finance
    (original_compatible authority inventory fresh) (initial_matrix authority inventory fresh)

noncomputable def run (count : Nat) : (Financial.Family.process sources).Run (reviewed authority inventory).finance.current
    (account authority inventory fresh count).current :=
  Financial.Family.continueVisits_run sources (Handoff.I fresh) 0 count (reviewed authority inventory).finance

noncomputable def migration (count index : Nat) (slot : ObligationSlot (Financial.Family.vocabulary sources))
    (present : (reviewed authority inventory).finance.current.slots[index]? = some slot) :=
  Financial.Family.Migration.follow sources (run authority inventory fresh count) index slot present

theorem every_complete_original_claim_is_preserved (count : Nat) :
    (reviewed authority inventory).finance.current.slots.map (Financial.Family.slotClaim sources) <+:
      (account authority inventory fresh count).current.slots.map (Financial.Family.slotClaim sources) :=
  Financial.Family.continueVisits_preserves_original_claims sources (Handoff.I fresh) 0 count _

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Finance
