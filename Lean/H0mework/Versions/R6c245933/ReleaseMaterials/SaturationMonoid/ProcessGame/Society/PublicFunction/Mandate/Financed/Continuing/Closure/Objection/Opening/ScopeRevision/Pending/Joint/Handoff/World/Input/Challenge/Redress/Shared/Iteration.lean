import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Challenge.Redress.Shared.Execution
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Challenge.Redress.Shared.Deadline
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Challenge.Redress.Shared.Past

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Challenge.Redress.Shared.Iteration
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
open Input.Event Input.Event.Future.Expiry.Progress.Responsibility
noncomputable section
variable {epoch : Epoch} (inventory : Inventory epoch)

abbrev staged := Dispatch.after (Shared.after inventory)
abbrev activation := Future.Expiry.Progress.Runtime.activated (staged inventory)
  (Future.Expiry.Progress.Runtime.ordinal (staged inventory))
abbrev facade := Future.Expiry.Progress.Runtime.facade (staged inventory)

structure JointReceipt where
  private mk ::
  challenges : Shared.Disposition inventory
  challenges_exact : challenges = Shared.produce inventory
  newborn : Shared.Newborn.CensusReceipt inventory
  newborn_exact : newborn = Shared.Newborn.receipt inventory
  grants : List (Sigma fun record : {record : Shared.Grant.Record inventory // record ∈ inventory.grants} => Shared.Grant.Disposition inventory record.val)
  grants_exact : grants = Shared.Grant.allOriginalGrants inventory
  current : Shared.Residual.Receipt inventory
  current_exact : current = Shared.Residual.produce inventory
  past : Shared.Past.Receipt inventory
  past_exact : past = Shared.Past.produce inventory
  rows : ∀ row : Input.Event.Future.Expiry.Progress.Responsibility.Row ⟨epoch,inventory⟩,
    (Shared.Runtime.originalRow inventory row).row.origin = row.origin ∧
      row.state.history <+: (Shared.Runtime.originalRow inventory row).state.history
  matrix : Financial.Family.ledgerClaims sources (Shared.Runtime.answer inventory).packet.2.finance.current =
    (World.current (Shared.Runtime.answer inventory).packet.1 (Shared.Runtime.answer inventory).packet.2.inputs).claims
  expired : epoch.scope.task.deadline <
    (World.current (Shared.Runtime.answer inventory).packet.1 (Shared.Runtime.answer inventory).packet.2.inputs).clock
  submitted : (Shared.Runtime.rootActual inventory).submitted = Shared.word inventory
  before : (Shared.Runtime.rootActual inventory).before = World.current epoch inventory.inputs
  ledger : HEq (activation inventory).tick.generated.wholeLedgerWriteBack
    ((activation inventory).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt (activation inventory).current.visit.current)
  next : (activation inventory).tick.nextCurrent =
    (facade inventory).process.stateAt ((facade inventory).process.successor (activation inventory).state)

def joint : JointReceipt inventory := by
  have factor := (facade inventory).readoutAt_factorizes (activation inventory) (.inr ())
  exact ⟨Shared.produce inventory,rfl,Shared.Newborn.receipt inventory,rfl,
    Shared.Grant.allOriginalGrants inventory,rfl,Shared.Residual.produce inventory,rfl,
    Shared.Past.produce inventory,rfl,
    Shared.Runtime.every_initial_native_row_retains_its_origin_and_complete_history inventory,
    (Shared.Runtime.answer inventory).packet.2.matrix,
    (Shared.Runtime.answer inventory).original_scope_has_actually_expired,
    (Shared.Runtime.the_original_root_actually_executes_the_shared_disposition inventory).1,
    (Shared.Runtime.the_original_root_actually_executes_the_shared_disposition inventory).2,
    factor.2.2.1,factor.2.2.2.2⟩

/-- Only native whole-census receipts permit an idle step. -/
inductive Step where
  | private terminal (receipt : WholeTerminationReceipt ⟨epoch,inventory⟩)
  | private continued (active : settled ⟨epoch,inventory⟩ = false)
      (receipt : JointReceipt inventory) (exact : receipt = joint inventory)

def produce : Step inventory :=
  if complete : settled ⟨epoch,inventory⟩ = true then
    .terminal (settled_iff_whole_termination_receipts.mp complete)
  else .continued (Bool.eq_false_iff.mpr complete) (joint inventory) rfl

def Step.packet (step : Step inventory) : Packet :=
  match step with
  | .terminal _ => ⟨epoch,inventory⟩
  | .continued .. => (Shared.Runtime.answer inventory).packet

def Step.native (step : Step inventory) : Evolution ⟨epoch,inventory⟩ step.packet := by
  cases step
  next receipt => exact .same _
  next active receipt exact => exact Shared.Runtime.native inventory

def Step.isTerminal : Step inventory → Bool
  | .terminal _ => true | .continued .. => false

theorem Step.termination (step : Step inventory) (terminal : step.isTerminal = true) :
    WholeTerminationReceipt ⟨epoch,inventory⟩ := by
  cases step
  next receipt => exact receipt
  next active receipt exact => cases terminal

theorem terminal_iff_whole_native_receipts :
    (produce inventory).isTerminal = true ↔ WholeTerminationReceipt ⟨epoch,inventory⟩ := by
  unfold produce
  split
  · exact ⟨fun _ => settled_iff_whole_termination_receipts.mp ‹_›,fun _ => rfl⟩
  · constructor
    · intro impossible; cases impossible
    · intro receipt
      exact False.elim (‹settled ⟨epoch,inventory⟩ ≠ true› (settled_iff_whole_termination_receipts.mpr receipt))

theorem active_calls_the_same_joint_source (active : settled ⟨epoch,inventory⟩ = false) :
    produce inventory = .continued active (joint inventory) rfl := by
  simp only [produce,active,Bool.false_eq_true,not_false_eq_true,dif_neg]

theorem every_live_slot_calls_the_joint_source (row : Input.Event.Future.Expiry.Progress.Responsibility.Row ⟨epoch,inventory⟩)
    (index : Fin row.state.slots.length) (obligation : AdmittedObligation row.V)
    (present : row.state.slots[index.val]? = some (.live obligation)) :
    produce inventory = .continued (a_live_original_slot_prevents_total_settlement row index obligation present)
      (joint inventory) rfl :=
  active_calls_the_same_joint_source inventory (a_live_original_slot_prevents_total_settlement row index obligation present)

def next (packet : Packet) := (produce packet.2).packet

def after (packet : Packet) : Nat → Packet
  | 0 => packet
  | count+1 => next (after packet count)

def native (packet : Packet) : (count : Nat) → Evolution packet (after packet count)
  | 0 => .same packet
  | count+1 => .append (native packet count) (produce (after packet count).2).native

def step (packet : Packet) (count : Nat) := produce (after packet count).2

theorem after_add (packet : Packet) (first rest : Nat) :
    after packet (first+rest) = after (after packet first) rest := by
  induction rest with
  | zero => rfl
  | succ rest ih =>
    change next (after packet (first+rest)) = next (after (after packet first) rest)
    exact congrArg next ih

/-- A cutoff is a new observation point, never a certificate of termination. -/
def suffix (packet : Packet) (first rest : Nat) :
    Evolution (after packet first) (after packet (first+rest)) := by
  rw [after_add]
  exact native (after packet first) rest

def original (packet : Packet) (first rest : Nat) (row : Input.Event.Future.Expiry.Progress.Responsibility.Row (after packet first)) :=
  transport (suffix packet first rest) row

def complete (packet : Packet) (first rest : Nat) (row : Input.Event.Future.Expiry.Progress.Responsibility.Row (after packet first)) :=
  (original packet first rest row).complete

theorem every_intermediate_row_keeps_its_origin_and_entire_history
    (packet : Packet) (first rest : Nat) (row : Input.Event.Future.Expiry.Progress.Responsibility.Row (after packet first)) :
    (original packet first rest row).row.origin = row.origin ∧
      row.state.history <+: (original packet first rest row).state.history :=
  every_actual_step_retains_its_original_admission_and_history (suffix packet first rest) row

def financialSlot (packet : Packet) (first rest index : Nat)
    (slot : ObligationSlot (Financial.Family.vocabulary sources))
    (present : (after packet first).2.finance.current.slots[index]? = some slot) :=
  Future.Expiry.Progress.Response.financialSlotAlong (suffix packet first rest) index slot present

theorem every_intermediate_financial_slot_keeps_its_principal_and_exact_records
    (packet : Packet) (first rest index : Nat) (slot : ObligationSlot (Financial.Family.vocabulary sources))
    (present : (after packet first).2.finance.current.slots[index]? = some slot) :
    Financial.Family.Migration.principal sources (financialSlot packet first rest index slot present).slot +
      (financialSlot packet first rest index slot present).path.paid sources = Financial.Family.Migration.principal sources slot ∧
    (financialSlot packet first rest index slot present).path.records sources index =
      (Future.Expiry.Progress.Response.financeAlong (suffix packet first rest)).events.filter (fun event => event.slot == index) :=
  ⟨(financialSlot packet first rest index slot present).path.conservation sources,
    (Future.Expiry.Progress.Response.every_actual_path_preserves_each_original_financial_address
      (suffix packet first rest) index slot present).2⟩

private theorem clock_nondecreasing {first last : Packet} (path : Evolution first last) :
    (World.current first.1 first.2.inputs).clock ≤ (World.current last.1 last.2.inputs).clock := by
  induction path with
  | same packet => exact le_refl _
  | submit inventory word =>
    have update := Event.observed_current_is_raw_next inventory word
    change _ ≤ (World.current _ (Event.observed inventory word).inputs).clock
    rw [update]
    exact (Mandate.law base _).next_clock_nondecreasing _ _
  | @handoff epoch inventory fresh =>
    change _ ≤ (OutstandingSource.History.currentAt (Epoch.ofFresh fresh).bound.source
      (World.handoff inventory fresh).inputs ((World.handoff inventory fresh).inputs.length+2)).clock
    rw [Future.Expiry.source_clock]
    change (World.current epoch inventory.inputs).clock ≤ (World.current epoch inventory.inputs).clock + _
    exact le_add_of_nonneg_right (Nat.cast_nonneg _)
  | @handoffAt epoch inventory fresh actualInputs =>
    change _ ≤ (OutstandingSource.History.currentAt (Epoch.ofFresh fresh).bound.source
      (World.handoffAt inventory fresh actualInputs).inputs ((World.handoffAt inventory fresh actualInputs).inputs.length+2)).clock
    rw [Future.Expiry.source_clock]
    change (World.current epoch inventory.inputs).clock ≤ (World.current epoch inventory.inputs).clock + _
    exact le_add_of_nonneg_right (Nat.cast_nonneg _)
  | append earlier later before after => exact before.trans after

theorem every_active_cut_exhausts_its_original_jurisdiction
    (active : settled ⟨epoch,inventory⟩ = false) :
    epoch.scope.task.deadline <
      (World.current (next ⟨epoch,inventory⟩).1 (next ⟨epoch,inventory⟩).2.inputs).clock := by
  change _ < (World.current (produce inventory).packet.1 (produce inventory).packet.2.inputs).clock
  rw [active_calls_the_same_joint_source inventory active]
  exact (joint inventory).expired

theorem every_actual_suffix_keeps_the_original_jurisdiction_expired
    (active : settled ⟨epoch,inventory⟩ = false) {last : Packet}
    (path : Evolution (next ⟨epoch,inventory⟩) last) :
    epoch.scope.task.deadline < (World.current last.1 last.2.inputs).clock :=
  (every_active_cut_exhausts_its_original_jurisdiction inventory active).trans_le (clock_nondecreasing path)

theorem every_future_original_task_use_is_refused
    (active : settled ⟨epoch,inventory⟩ = false) {last : Packet}
    (path : Evolution (next ⟨epoch,inventory⟩) last)
    (word : List Action) (item : ExecutionItem Bool Good Mandate.Source.Port (State Bool Unit) Unit)
    (member : item ∈ (Mandate.law base epoch.scope).rawItems (World.current last.1 last.2.inputs) word)
    (bearer : Bool) (goods : Bundle Good) (purpose : Use)
    (operation : item.request.operation = .use bearer goods purpose) (taskUse : Mandate.TaskUse epoch.scope item.request) :
    ¬ (Mandate.law base epoch.scope).Valid item.before item.request :=
  Future.Expiry.Jurisdiction.expired_task_use_is_refused epoch.scope _
    (every_actual_suffix_keeps_the_original_jurisdiction_expired inventory active path)
    word item member bearer goods purpose operation taskUse

theorem no_future_acceptance_renewal_or_proposal_can_revive_the_original_scope
    (active : settled ⟨epoch,inventory⟩ = false) {last : Packet}
    (path : Evolution (next ⟨epoch,inventory⟩) last) (word : List Action)
    (event : Mandate.ActualCommand base epoch.scope (World.current last.1 last.2.inputs) word) :
    event.command ≠ .accept ∧ event.command ≠ .renew ∧ ∀ candidate, event.command ≠ .propose candidate :=
  Future.Expiry.Jurisdiction.expired_scope_cannot_generate_acceptance_renewal_or_proposal epoch.scope _
    (every_actual_suffix_keeps_the_original_jurisdiction_expired inventory active path) word event

theorem every_active_cut_has_a_strictly_later_actual_successor
    (active : settled ⟨epoch,inventory⟩ = false) :
    (World.current epoch inventory.inputs).clock <
      (World.current (next ⟨epoch,inventory⟩).1 (next ⟨epoch,inventory⟩).2.inputs).clock := by
  change _ < (World.current (produce inventory).packet.1 (produce inventory).packet.2.inputs).clock
  rw [active_calls_the_same_joint_source inventory active]
  exact (clock_nondecreasing (.append (.submit inventory (Shared.word inventory))
      (Event.inputEvolution (Shared.after inventory) (Dispatch.intent (Shared.after inventory))))).trans_lt
    (Shared.Runtime.answer inventory).the_actual_boundary_is_not_a_clock_self_loop


theorem a_live_cut_cannot_be_a_stationary_actual_sink
    (active : settled ⟨epoch,inventory⟩ = false) : next ⟨epoch,inventory⟩ ≠ ⟨epoch,inventory⟩ := by
  intro same
  have strict := every_active_cut_has_a_strictly_later_actual_successor inventory active
  rw [same] at strict
  exact (lt_irrefl _ strict)

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Challenge.Redress.Shared.Iteration

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Challenge.Redress.Shared.Iteration.Native
open Input.Event.Future.Expiry.Progress
variable {epoch : Epoch} (inventory : Inventory epoch)

def joint : JointReceipt inventory := by
  have factor := (facade inventory).readoutAt_factorizes (activation inventory) (.inr ())
  exact ⟨Shared.produce inventory,rfl,Shared.Newborn.receipt inventory,rfl,
    Shared.Grant.allOriginalGrants inventory,rfl,Shared.Residual.produce inventory,rfl,
    Shared.Past.produce inventory,rfl,
    Shared.Runtime.every_initial_native_row_retains_its_origin_and_complete_history inventory,
    (Shared.Runtime.answer inventory).packet.2.matrix,
    (Shared.Runtime.answer inventory).original_scope_has_actually_expired,
    (Shared.Runtime.the_original_root_actually_executes_the_shared_disposition inventory).1,
    (Shared.Runtime.the_original_root_actually_executes_the_shared_disposition inventory).2,
    factor.2.2.1,factor.2.2.2.2⟩

theorem joint_exact : joint inventory = Iteration.joint inventory := rfl
@[csimp] theorem joint_codegen : @Iteration.joint = @joint := rfl

def produce : Step inventory :=
  if complete : Responsibility.settled ⟨epoch,inventory⟩ = true then
    .terminal (Responsibility.settled_iff_whole_termination_receipts.mp complete)
  else .continued (Bool.eq_false_iff.mpr complete) (joint inventory) (joint_exact inventory)

theorem produce_exact : produce inventory = Iteration.produce inventory := rfl
@[csimp] theorem produce_codegen : @Iteration.produce = @produce := by
  funext epoch inventory
  exact (produce_exact inventory).symm

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Challenge.Redress.Shared.Iteration.Native
