import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Response

/-! Any live original slot triggers an actual source-generated redress attempt.
Only the whole original receipt census can select the terminal branch. -/

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Responsibility.Dispatch
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
noncomputable section
variable {epoch : Epoch} (inventory : Inventory epoch)

/-- Every current and past native slot participates in the trigger. -/
def needsResponse : Bool := !(settled ⟨epoch,inventory⟩)

def intent : Input.Intent :=
  if (current epoch inventory.inputs).technology.holder.isSome then .exit else .revision

theorem intent_is_eligible : Input.Eligible epoch (intent inventory) (current epoch inventory.inputs) := by
  unfold intent
  split
  · exact ‹(current epoch inventory.inputs).technology.holder.isSome = true›
  · trivial

inductive Attempt where
  | private paid (payment : Input.Paid epoch (intent inventory) (current epoch inventory.inputs))
      (selected : Input.choose epoch (intent inventory) (current epoch inventory.inputs) = some payment)
      (legal : ∀ item ∈ (Mandate.law base epoch.scope).rawItems (current epoch inventory.inputs) (Input.emit inventory (intent inventory)),
        (Mandate.law base epoch.scope).Valid item.before item.request)
  | private blocked (absent : Input.choose epoch (intent inventory) (current epoch inventory.inputs) = none)
      (refusal : ∃ item ∈ (Mandate.law base epoch.scope).rawItems (current epoch inventory.inputs) (Input.emit inventory (intent inventory)),
        ¬ (Mandate.law base epoch.scope).Valid item.before item.request)
      (coverage : ∀ choice ∈ Input.menu epoch (intent inventory) (current epoch inventory.inputs),
        ¬ Input.Legal epoch (intent inventory) (current epoch inventory.inputs) choice)

def attempt : Attempt inventory := by
  cases Input.outcome epoch (intent inventory) (current epoch inventory.inputs)
  next payment selected legal => exact .paid payment selected legal
  next absent => exact False.elim (absent (intent_is_eligible inventory))
  next eligible absent refusal => exact .blocked absent refusal (Input.no_selected_choice_has_escaped_its_actual_check epoch _ _ absent)

def word := Input.emit inventory (intent inventory)
def after := Input.advance inventory (intent inventory)
def trace := Progress.Runtime.trace (after inventory)
def native : Evolution ⟨epoch,inventory⟩ (trace inventory).packet :=
  .append (Event.inputEvolution inventory (intent inventory)) (trace inventory).native

def original (row : Row ⟨epoch,inventory⟩) := transport (native inventory) row

def finance (index : Nat) (slot : ObligationSlot (Financial.Family.vocabulary sources))
    (present : inventory.finance.current.slots[index]? = some slot) :=
  Progress.Response.financialSlotAlong (native inventory) index slot present

inductive Result where
  | private terminal (receipt : WholeTerminationReceipt ⟨epoch,inventory⟩)
  | private continued (needed : needsResponse inventory = true)
      (request : Attempt inventory) (request_exact : request = attempt inventory)
      (response : Trace (after inventory)) (response_exact : response = trace inventory)

def produce : Result inventory :=
  if complete : settled ⟨epoch,inventory⟩ = true then .terminal (settled_iff_whole_termination_receipts.mp complete)
  else .continued (by simp only [needsResponse,complete,Bool.not_false]) (attempt inventory) rfl (trace inventory) rfl

theorem every_live_original_slot_forces_the_actual_response (row : Row ⟨epoch,inventory⟩)
    (index : Fin row.state.slots.length) (obligation : AdmittedObligation row.V)
    (present : row.state.slots[index.val]? = some (.live obligation)) :
    needsResponse inventory = true ∧
      produce inventory = Result.continued (inventory := inventory) (by
        simp only [needsResponse,a_live_original_slot_prevents_total_settlement row index obligation present,Bool.not_false])
        (attempt inventory) rfl (trace inventory) rfl := by
  have pending := a_live_original_slot_prevents_total_settlement row index obligation present
  constructor
  · simp only [needsResponse,pending,Bool.not_false]
  · simp only [produce,pending,Bool.false_eq_true,not_false_eq_true,dif_neg]

theorem actual_word_and_saved_cut :
    (Input.execution inventory (intent inventory)).submitted = word inventory ∧
    (Input.execution inventory (intent inventory)).before = current epoch inventory.inputs :=
  Input.actual_word_and_cut inventory (intent inventory)

theorem every_shortage_generates_an_actual_repair
    (demand : Input.Demand epoch (intent inventory) (current epoch inventory.inputs))
    (member : demand ∈ Input.demands epoch (intent inventory) (current epoch inventory.inputs)) :
    demand.failed ∈ (Mandate.law base epoch.scope).rawItems (current epoch inventory.inputs) (word inventory) ∧
    ¬ (Mandate.law base epoch.scope).Valid demand.failed.before demand.failed.request ∧
    demand.debit ∈ (Mandate.law base epoch.scope).debit demand.failed.before demand.failed.request ∧
    0 < demand.debit.2 - demand.failed.before.stock demand.debit.1.1 demand.debit.1.2 ∧
    demand.request epoch ∈ word inventory :=
  Input.every_demand_is_a_real_shortfall_in_the_emitted_word epoch _ _ demand member

theorem all_original_native_rows_reach_the_actual_response (row : Row ⟨epoch,inventory⟩) :
    (original inventory row).row.origin = row.origin ∧
      row.state.history <+: (original inventory row).state.history :=
  every_actual_step_retains_its_original_admission_and_history (native inventory) row

def rootActual := OutstandingSource.History.actualExecution epoch.source (trace inventory).finalInputs (inventory.inputs.length+1)

theorem dispatch_word_is_in_the_whole_root_source :
    inventory.inputs ++ [word inventory] <+: (trace inventory).finalInputs := by
  have first : inventory.inputs ++ [word inventory] <+: (after inventory).inputs := by
    refine ⟨[Input.repayment inventory (intent inventory)],?_⟩
    rw [after,Input.inputs_exact]
    simp only [word,List.append_assoc,List.singleton_append]
  exact first.trans (trace inventory).saved_inputs_are_in_the_final_source

theorem the_original_root_actually_executes_the_dispatch :
    (rootActual inventory).submitted = word inventory ∧
    (rootActual inventory).before = current epoch inventory.inputs := by
  obtain ⟨suffix,same⟩ := dispatch_word_is_in_the_whole_root_source inventory
  unfold rootActual
  rw [← same]
  constructor
  · rw [OutstandingSource.History.scheduled_input_is_actual epoch.source _ inventory.inputs.length (by simp)]
    simp
  · change OutstandingSource.History.currentAt epoch.source ((inventory.inputs ++ [word inventory]) ++ suffix) (inventory.inputs.length+2) = _
    rw [(OutstandingSource.History.actual_frame _ _ _).1,List.append_assoc,
      OutstandingSource.History.extending_inputs_preserves_its_executed_prefix epoch.source inventory.inputs
        ([word inventory] ++ suffix) _ (Nat.le_refl _)]
    exact (OutstandingSource.History.actual_frame epoch.source inventory.inputs _).1.symm

theorem paid_exit_executes_retirement_in_the_dispatch
    (exiting : intent inventory = .exit)
    (paid : Input.Paid epoch .exit (current epoch inventory.inputs))
    (selected : Input.choose epoch .exit (current epoch inventory.inputs) = some paid) :
    (current epoch inventory.inputs).technology.holder = some paid.choice.actor ∧
    ((Mandate.law base epoch.scope).execute (current epoch inventory.inputs) 0 (word inventory)).final.technology.holder = none ∧
    ((Mandate.law base epoch.scope).execute (current epoch inventory.inputs) 0 (word inventory)).final.technology.offered = none := by
  rw [word,exiting,Input.emit,Input.paid_word_is_the_actual_selected_candidate epoch .exit _ paid selected]
  exact ⟨Input.paid_exit_is_the_original_holders_own_action epoch _ paid,
    (Input.paid_exit_retires_the_actual_holder epoch _ paid).2⟩

theorem the_paid_exit_is_the_same_root_actual_next
    (exiting : intent inventory = .exit)
    (paid : Input.Paid epoch .exit (current epoch inventory.inputs))
    (selected : Input.choose epoch .exit (current epoch inventory.inputs) = some paid) :
    (rootActual inventory).after.technology.holder = none ∧
    (rootActual inventory).after.technology.offered = none := by
  have effect := paid_exit_executes_retirement_in_the_dispatch inventory exiting paid selected
  rw [(rootActual inventory).after_exact,(the_original_root_actually_executes_the_dispatch inventory).1,
    (the_original_root_actually_executes_the_dispatch inventory).2]
  exact effect.2

theorem whole_termination_is_the_only_terminal_branch (complete : settled ⟨epoch,inventory⟩ = true) :
    produce inventory = Result.terminal (settled_iff_whole_termination_receipts.mp complete) := by
  simp only [produce,dif_pos complete]

theorem the_same_actual_root_consumes_dispatch_original_rows_and_next :
    (rootActual inventory).submitted = word inventory ∧
    (rootActual inventory).before = current epoch inventory.inputs ∧
    (∀ row : Row ⟨epoch,inventory⟩, (original inventory row).row.origin = row.origin ∧
      row.state.history <+: (original inventory row).state.history) ∧
    HEq (Progress.Runtime.activated (after inventory) (Progress.Runtime.ordinal (after inventory))).tick.generated.wholeLedgerWriteBack
      ((Progress.Runtime.activated (after inventory) (Progress.Runtime.ordinal (after inventory))).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
        (Progress.Runtime.activated (after inventory) (Progress.Runtime.ordinal (after inventory))).current.visit.current) ∧
    (Progress.Runtime.activated (after inventory) (Progress.Runtime.ordinal (after inventory))).tick.nextCurrent =
      (Progress.Runtime.facade (after inventory)).process.stateAt
        ((Progress.Runtime.facade (after inventory)).process.successor
          (Progress.Runtime.activated (after inventory) (Progress.Runtime.ordinal (after inventory))).state) := by
  have factor := (Progress.Runtime.facade (after inventory)).readoutAt_factorizes
    (Progress.Runtime.activated (after inventory) (Progress.Runtime.ordinal (after inventory))) (.inr ())
  exact ⟨(the_original_root_actually_executes_the_dispatch inventory).1,
    (the_original_root_actually_executes_the_dispatch inventory).2,
    all_original_native_rows_reach_the_actual_response inventory,factor.2.2.1,factor.2.2.2.2⟩

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Responsibility.Dispatch
