import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.History
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Receipts
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.InventoryExact
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Migration

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native

open Institutions.Capitalism.Universal.Source.Program
open Institutions.Capitalism.Universal.Root ResponsibilityLifecycle

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (source : Machine Party Good Port Technology Instrument)

structure Disposition (depth : Nat) where
  private mk ::
  services : (index : Slot source) → Prefix source index (depth + 1)
  services_exact : services = fun index => historyAt source index (depth + 1)
  finance : (Financial.process source.input).GeneratedState
  finance_exact : finance = Financial.accountAt source.input (depth + 2)
  financeArrival : (Financial.process source.input).Run
    (Financial.accountAt source.input (depth + 1)).current finance.current
  migrations : ∀ index slot,
    (Financial.accountAt source.input (depth + 1)).current.slots[index]? = some slot →
      Financial.Migration.Follow source.input financeArrival index slot

def generate (depth : Nat) : Disposition source depth :=
  ⟨fun index => historyAt source index (depth + 1), rfl, Financial.accountAt source.input (depth + 2), rfl,
    Financial.consumeOrigins_run source.input _ _, fun index slot present =>
      Financial.Migration.follow source.input (Financial.consumeOrigins_run source.input _ _) index slot present⟩

theorem both_consumers_use_the_same_actual_word (depth : Nat) :
    (Financial.inventoryAt source.input (ProgrammeHistory.visitAt source.input (depth + 1))).filterMap
      (Financial.InstructionOrigin.instruction? source.input) =
      source.code.law.rawItems (source.actualExecution depth).before (source.actualExecution depth).submitted :=
  Financial.inventoryAt_instructions_exact source.input _

def financeCrossing (depth : Nat) :
    (Financial.process source.input).Run
      (generate source depth).finance.current (generate source (depth + 1)).finance.current :=
  Financial.consumeOrigins_run source.input _ _

theorem finance_keeps_all_original_claims (depth : Nat) :
    (generate source depth).finance.current.slots.map (Financial.slotClaim source.input) <+:
      (generate source (depth + 1)).finance.current.slots.map (Financial.slotClaim source.input) :=
  Financial.every_original_debt_is_retained source.input (depth + 2)

theorem service_is_live_exactly_while_unpaid (depth : Nat) (index : Slot source) :
    ((generate source depth).services index).state.LiveAt 0 ↔
      ∀ earlier < depth + 1, ¬ Paid source earlier index :=
  native_live_iff_unpaid source index (depth + 1)

theorem actual_feasible_response_closes_native_services (policy : source.code.Policy)
    (chosen : source.policy? = some policy) (feasible : source.code.feasible policy)
    (eligible : source.code.eligible (trace source.code policy source.history source.opponent) = true)
    (index : Slot source) :
    ((generate source source.history.length).services index).state.TerminalAt 0 :=
  actual_service_closes_every_native_slot source _
    (source.actual_reaction_pays_the_original_task policy chosen feasible eligible) index

theorem every_settled_service_keeps_its_first_archive (depth later : Nat) (index : Slot source)
    (terminal : ((generate source depth).services index).state.TerminalAt 0) :
    ((generate source (depth + later)).services index).state = ((generate source depth).services index).state := by
  change (historyAt source index (depth + later + 1)).state = _
  rw [show depth + later + 1 = depth + 1 + later by omega]
  exact first_archive_is_retained source index (depth + 1) later terminal

theorem selected_and_original_native_services_are_actually_settled
    (choice : Selection source.code source.reference) (selected : source.answer = .selected choice)
    (originalFeasible : source.code.feasible source.reference)
    (eligible : source.code.eligible (trace source.code source.reference source.history source.opponent) = true) :
    (∀ index, ((generate (source.withSide .original) source.history.length).services index).state.TerminalAt 0) ∧
      (∀ index, ((generate (source.withSide .replacement) source.history.length).services index).state.TerminalAt 0) := by
  have paid := source.both_actual_sources_pay_when_the_original_task_is_admissible choice selected originalFeasible eligible
  exact ⟨fun index => actual_service_closes_every_native_slot _ _ paid.1 index,
    fun index => actual_service_closes_every_native_slot _ _ paid.2 index⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native
