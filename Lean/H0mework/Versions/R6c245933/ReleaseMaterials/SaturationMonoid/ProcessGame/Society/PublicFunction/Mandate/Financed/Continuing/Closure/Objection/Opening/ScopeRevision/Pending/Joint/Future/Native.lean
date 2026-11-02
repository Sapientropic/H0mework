import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Future.Source

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Future

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle
open Followup
variable {fuel : ℚ} {old : Followup.Joint.Inventory fuel} (ready : Ready old)
  {originInputs : List (List Action)} (inventory : Inventory ready originInputs) (intent : Intent)

noncomputable abbrev grantProcess (record : Mandate.Challenge.Cross.GrantResident (B ready) inventory.inputs) :=
  Lifecycle.Observed.process (base := base) (scope := ready.scope)
    (currentAt := Mandate.Challenge.Cross.grantCurrent (B ready) (staged ready inventory intent).inputs)
    (wordAt := Mandate.Challenge.Cross.grantWord (B ready) (staged ready inventory intent).inputs)
    (birth := record.birth.val)
    (grant := Mandate.Challenge.Cross.transportGrant (B ready) inventory.inputs (emit ready inventory intent) record.birth record.grant)

noncomputable abbrev newGrants := Mandate.Challenge.Cross.newbornGrants (B ready) (inputs := inventory.inputs) (emit ready inventory intent)

structure Native where
  private mk ::
  response : Settlement.Native ready (staged ready inventory intent)
  serviceRuns : (index : (epochSource ready).Slot) →
    (OutstandingSource.History.NativeService.threadProcess (epochSource ready) originInputs).Run
      (inventory.services index).state.current ((advance ready inventory intent).services index).state.current
  objections : (resident : Mandate.Challenge.Cross.Resident (B ready) inventory.inputs) → resident ∈ inventory.objections →
    Descendant ready resident (advance ready inventory intent)
  grants : (record : Mandate.Challenge.Cross.GrantResident (B ready) inventory.inputs) → record ∈ inventory.grants →
    (record.advance (B ready) (emit ready inventory intent)).advance (B ready)
      (Settlement.emit ready (staged ready inventory intent)) ∈ (advance ready inventory intent).grants
  grantRuns : (record : Mandate.Challenge.Cross.GrantResident (B ready) inventory.inputs) →
    (grantProcess ready inventory intent record).Run record.history.state
      (record.advance (B ready) (emit ready inventory intent)).history.state
  newborns : ∀ record ∈ newGrants ready inventory intent,
    record.advance (B ready) (Settlement.emit ready (staged ready inventory intent)) ∈ (advance ready inventory intent).grants
  financialRun : (Financial.Family.process Finance.sources).Run inventory.finance.current (advance ready inventory intent).finance.current
  financialMigrations : ∀ index slot, inventory.finance.current.slots[index]? = some slot →
    Financial.Family.Migration.Follow Finance.sources financialRun index slot
  financial_matrix : Financial.Family.ledgerClaims Finance.sources (advance ready inventory intent).finance.current =
    (current ready (advance ready inventory intent).inputs).claims

noncomputable def native : Native ready inventory intent := by
  let response := Settlement.native ready (staged ready inventory intent)
  let financial := (every_original_financial_slot_has_actual_native_continuation ready inventory (emit ready inventory intent)).concatRuns _ response.financialRun
  refine ⟨response, ?_, ?_, ?_, ?_, ?_, financial, ?_, response.financial_matrix⟩
  · intro index
    exact (every_original_service_has_actual_native_continuation ready inventory (emit ready inventory intent) index).concatRuns _ (response.serviceRuns index)
  · intro resident inside
    exact ((begin ready inventory resident inside).step ready (emit ready inventory intent)).step ready
      (Settlement.emit ready (staged ready inventory intent))
  · intro record inside
    exact response.grants _ (every_old_grant_is_in_the_next_inventory ready inventory (emit ready inventory intent) record inside)
  · intro record
    exact record.actualRun (B ready) (emit ready inventory intent)
  · intro record member
    apply response.grants
    exact List.mem_append_right _ member
  · intro index slot present
    exact Financial.Family.Migration.follow _ _ index slot present

noncomputable def financeRun (inventory : Inventory ready originInputs) : (intents : List Intent) → (Financial.Family.process Finance.sources).Run
    inventory.finance.current (run ready inventory intents).finance.current
  | [] => .nil
  | intent :: tail => (native ready inventory intent).financialRun.concatRuns _ (financeRun (advance ready inventory intent) tail)

noncomputable def serviceRun (inventory : Inventory ready originInputs) (index : (epochSource ready).Slot) : (intents : List Intent) →
    (OutstandingSource.History.NativeService.threadProcess (epochSource ready) originInputs).Run
      (inventory.services index).state.current ((run ready inventory intents).services index).state.current
  | [] => .nil
  | intent :: tail => ((native ready inventory intent).serviceRuns index).concatRuns _
      (serviceRun (advance ready inventory intent) index tail)

noncomputable def descendants {start : Inventory ready originInputs}
    {original : Mandate.Challenge.Cross.Resident (B ready) start.inputs}
    {inventory : Inventory ready originInputs} (descendant : Joint.Descendant ready original inventory) :
    (intents : List Intent) → Joint.Descendant ready original (run ready inventory intents)
  | [] => descendant
  | intent :: tail => descendants
      ((descendant.step ready (emit ready inventory intent)).step ready (Settlement.emit ready (staged ready inventory intent))) tail

noncomputable def objectionRun (original : Mandate.Challenge.Cross.Resident (B ready) inventory.inputs)
    (inside : original ∈ inventory.objections) (intents : List Intent) :
    Joint.Descendant ready original (run ready inventory intents) :=
  descendants ready (begin ready inventory original inside) intents

noncomputable def evolutionFinanceRun (inventory : Inventory ready originInputs) : (count : Nat) →
    (Financial.Family.process Finance.sources).Run inventory.finance.current (evolve ready inventory count).finance.current
  | 0 => .nil
  | count + 1 => (native ready inventory (nextIntent ready inventory)).financialRun.concatRuns _
      (evolutionFinanceRun (advance ready inventory (nextIntent ready inventory)) count)

noncomputable def evolutionServiceRun (inventory : Inventory ready originInputs) (index : (epochSource ready).Slot) : (count : Nat) →
    (OutstandingSource.History.NativeService.threadProcess (epochSource ready) originInputs).Run
      (inventory.services index).state.current ((evolve ready inventory count).services index).state.current
  | 0 => .nil
  | count + 1 => ((native ready inventory (nextIntent ready inventory)).serviceRuns index).concatRuns _
      (evolutionServiceRun (advance ready inventory (nextIntent ready inventory)) index count)

noncomputable def evolvingDescendants {start : Inventory ready originInputs}
    {original : Mandate.Challenge.Cross.Resident (B ready) start.inputs}
    {inventory : Inventory ready originInputs} (descendant : Joint.Descendant ready original inventory) :
    (count : Nat) → Joint.Descendant ready original (evolve ready inventory count)
  | 0 => descendant
  | count + 1 => evolvingDescendants
      ((descendant.step ready (emit ready inventory (nextIntent ready inventory))).step ready
        (Settlement.emit ready (staged ready inventory (nextIntent ready inventory)))) count

noncomputable def evolutionObjectionRun (original : Mandate.Challenge.Cross.Resident (B ready) inventory.inputs)
    (inside : original ∈ inventory.objections) (count : Nat) :
    Joint.Descendant ready original (evolve ready inventory count) :=
  evolvingDescendants ready (begin ready inventory original inside) count

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Future
