import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Matrix
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Challenge.Cross.GrantInventory
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Outstanding.History.NativeThread

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle
open Followup

variable {fuel : ℚ} {old : Followup.Joint.Inventory fuel} (ready : Ready old)

structure Inventory (originInputs : List (List Action)) where
  private mk ::
  inputs : List (List Action)
  objections : List (Mandate.Challenge.Cross.Resident (B ready) inputs)
  grants : List (Mandate.Challenge.Cross.GrantResident (B ready) inputs)
  finance : Finance.Account
  financeGenerated : Finance.Generated ready originInputs inputs finance
  services : (index : (epochSource ready).Slot) →
    OutstandingSource.History.NativeService.Thread (epochSource ready) originInputs index inputs

def initial (inputs : List (List Action)) : Inventory ready inputs :=
  ⟨inputs, beforeResidents ready inputs, Mandate.Challenge.Cross.grantsBefore (B ready) inputs, Finance.initial ready inputs, .initial,
    fun index => OutstandingSource.History.NativeService.Thread.initial (epochSource ready) index⟩

variable {originInputs : List (List Action)}

theorem financial_matrix_at_every_actual_cut (inventory : Inventory ready originInputs) :
    Financial.Family.ledgerClaims Finance.sources inventory.finance.current = (current ready inventory.inputs).claims :=
  inventory.financeGenerated.actual_matrix ready

noncomputable def submit (inventory : Inventory ready originInputs) (word : List Action) : Inventory ready originInputs :=
  ⟨inventory.inputs ++ [word],
    Mandate.Challenge.Cross.advanceAll (B ready) inventory.objections word,
    Mandate.Challenge.Cross.advanceGrants (B ready) inventory.grants word,
    Finance.append ready inventory.inputs word inventory.finance,
    .submit inventory.financeGenerated word,
    fun index => (inventory.services index).advance (epochSource ready) word⟩

noncomputable def actual (inventory : Inventory ready originInputs) (word : List Action) :=
  OutstandingSource.History.actualExecution (epochSource ready) (submit ready inventory word).inputs (inventory.inputs.length + 1)

theorem actual_word_and_cut (inventory : Inventory ready originInputs) (word : List Action) :
    (actual ready inventory word).submitted = word ∧ (actual ready inventory word).before = current ready inventory.inputs :=
  ⟨Mandate.Challenge.Cross.emitted_word_is_actual (B ready) inventory.inputs word,
    Mandate.Challenge.Cross.emitted_word_uses_actual_cut (B ready) inventory.inputs word⟩

theorem every_old_objection_is_in_the_next_inventory (inventory : Inventory ready originInputs) (word : List Action)
    (resident : Mandate.Challenge.Cross.Resident (B ready) inventory.inputs) (inside : resident ∈ inventory.objections) :
    resident.advance (B ready) word ∈ (submit ready inventory word).objections :=
  Mandate.Challenge.Cross.every_old_resident_is_actually_consumed _ _ _ resident inside

def old_objection_actual_run (inventory : Inventory ready originInputs) (word : List Action)
    (resident : Mandate.Challenge.Cross.Resident (B ready) inventory.inputs) := resident.responseRun (B ready) word

theorem every_old_grant_is_in_the_next_inventory (inventory : Inventory ready originInputs) (word : List Action)
    (grant : Mandate.Challenge.Cross.GrantResident (B ready) inventory.inputs) (inside : grant ∈ inventory.grants) :
    grant.advance (B ready) word ∈ (submit ready inventory word).grants :=
  Mandate.Challenge.Cross.every_original_grant_is_preserved _ _ _ grant inside

def old_grant_actual_run (inventory : Inventory ready originInputs) (word : List Action)
    (grant : Mandate.Challenge.Cross.GrantResident (B ready) inventory.inputs) := grant.actualRun (B ready) word

def every_original_service_has_actual_native_continuation (inventory : Inventory ready originInputs) (word : List Action)
    (index : (epochSource ready).Slot) := (inventory.services index).actualRun (epochSource ready) word

def every_original_financial_slot_has_actual_native_continuation (inventory : Inventory ready originInputs)
    (word : List Action) := Finance.appendRun ready inventory.inputs word inventory.finance

def old_financial_debt_keeps_its_complete_native_admission (inventory : Inventory ready originInputs)
    (word : List Action) (index : Nat) (slot : ObligationSlot (Financial.Family.vocabulary Finance.sources))
    (present : inventory.finance.current.slots[index]? = some slot) :=
  Finance.oldDebtContinuation ready inventory.inputs word inventory.finance index slot present

theorem only_actual_new_issues_are_added (inventory : Inventory ready originInputs) (word : List Action) :
    (submit ready inventory word).finance.current.slots.map (Financial.Family.slotClaim Finance.sources) =
      inventory.finance.current.slots.map (Financial.Family.slotClaim Finance.sources) ++
        (Financial.Family.visitOrigins Finance.sources
          (OutstandingSource.History.input (epochSource ready) (inventory.inputs ++ [word]))
          (inventory.inputs.length + 2)).filterMap (Financial.Family.originsClaim? Finance.sources) :=
  Finance.append_issues_only_actual_new_claims ready inventory.inputs word inventory.finance

theorem original_service_terminal_archive_is_literal (inventory : Inventory ready originInputs) (word : List Action)
    (index : (epochSource ready).Slot) (terminal : (inventory.services index).state.current.TerminalAt 0) :
    ((submit ready inventory word).services index).state = (inventory.services index).state :=
  (inventory.services index).terminal_state_is_preserved (epochSource ready) terminal word

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint
