import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Settlement.Local

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Settlement

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle
open Followup
variable {fuel : ℚ} {old : Followup.Joint.Inventory fuel} (ready : Ready old)
  {originInputs : List (List Action)} (inventory : Inventory ready originInputs)

noncomputable abbrev grantProcess (record : Mandate.Challenge.Cross.GrantResident (B ready) inventory.inputs) :=
  Lifecycle.Observed.process (base := base) (scope := ready.scope)
    (currentAt := Mandate.Challenge.Cross.grantCurrent (B ready) (advance ready inventory).inputs)
    (wordAt := Mandate.Challenge.Cross.grantWord (B ready) (advance ready inventory).inputs)
    (birth := record.birth.val)
    (grant := Mandate.Challenge.Cross.transportGrant (B ready) inventory.inputs (emit ready inventory) record.birth record.grant)

structure Native where
  private mk ::
  serviceRuns : (index : (epochSource ready).Slot) →
    (OutstandingSource.History.NativeService.threadProcess (epochSource ready) originInputs).Run
      (inventory.services index).state.current ((advance ready inventory).services index).state.current
  objections : (resident : Mandate.Challenge.Cross.Resident (B ready) inventory.inputs) → resident ∈ inventory.objections →
    Descendant ready resident (advance ready inventory)
  grants : (record : Mandate.Challenge.Cross.GrantResident (B ready) inventory.inputs) → record ∈ inventory.grants →
    record.advance (B ready) (emit ready inventory) ∈ (advance ready inventory).grants
  grantRuns : (record : Mandate.Challenge.Cross.GrantResident (B ready) inventory.inputs) →
    (grantProcess ready inventory record).Run record.history.state (record.advance (B ready) (emit ready inventory)).history.state
  financialRun : (Financial.Family.process Finance.sources).Run inventory.finance.current (advance ready inventory).finance.current
  financialMigrations : ∀ index slot, inventory.finance.current.slots[index]? = some slot →
    Financial.Family.Migration.Follow Finance.sources financialRun index slot
  financial_matrix : Financial.Family.ledgerClaims Finance.sources (advance ready inventory).finance.current =
    (current ready (advance ready inventory).inputs).claims

noncomputable def native : Native ready inventory :=
  ⟨every_original_service_has_actual_native_continuation ready inventory (emit ready inventory),
    fun resident inside => (begin ready inventory resident inside).step ready (emit ready inventory),
    every_old_grant_is_in_the_next_inventory ready inventory (emit ready inventory),
    fun record => record.actualRun (B ready) (emit ready inventory),
    every_original_financial_slot_has_actual_native_continuation ready inventory (emit ready inventory),
    fun index slot present => Financial.Family.Migration.follow _ _ index slot present,
    financial_matrix_at_every_actual_cut ready _⟩

noncomputable def run : Nat → Inventory ready originInputs
  | 0 => inventory
  | count + 1 => advance ready (run count)

noncomputable def financeRun : (count : Nat) → (Financial.Family.process Finance.sources).Run
    inventory.finance.current (run ready inventory count).finance.current
  | 0 => .nil
  | count + 1 => (financeRun count).concatRuns _ (native ready (run ready inventory count)).financialRun

noncomputable def serviceRun (index : (epochSource ready).Slot) : (count : Nat) →
    (OutstandingSource.History.NativeService.threadProcess (epochSource ready) originInputs).Run
      (inventory.services index).state.current ((run ready inventory count).services index).state.current
  | 0 => .nil
  | count + 1 => (serviceRun index count).concatRuns _ ((native ready (run ready inventory count)).serviceRuns index)

noncomputable def objectionRun (original : Mandate.Challenge.Cross.Resident (B ready) inventory.inputs)
    (inside : original ∈ inventory.objections) : (count : Nat) →
      Joint.Descendant ready original (run ready inventory count)
  | 0 => begin ready inventory original inside
  | count + 1 => (objectionRun original inside count).step ready (emit ready (run ready inventory count))

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Settlement
