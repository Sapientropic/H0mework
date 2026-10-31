import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Responsibility.Transport

/-! The existing source-bounded response is consumed with every original native
row and its full history, the actual opening/blockage, and the whole original account. -/
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Response
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
noncomputable section
variable {epoch : Epoch} (inventory : Inventory epoch)

abbrev trace := Progress.Runtime.trace inventory
abbrev packet := (trace inventory).packet

def opening := (trace inventory).ending.2.1.openness

def original (row : Responsibility.Row ⟨epoch,inventory⟩) := Responsibility.transport (trace inventory).native row

def originalRun (row : Responsibility.Row ⟨epoch,inventory⟩) := (original inventory row).complete

def originalFinance (index : Nat) (slot : ObligationSlot (Financial.Family.vocabulary sources))
    (present : inventory.finance.current.slots[index]? = some slot) :=
  Financial.Family.Migration.follow sources (trace inventory).finance index slot present

def boundarySlot (slot : Responsibility.Slot (packet inventory)) := Responsibility.inspect slot

/-- The same fixed Family process consumes every actual primitive or handoff edge. -/
def financeAlong {first last : Packet} (path : Evolution first last) :
    (Financial.Family.process sources).Run first.2.finance.current last.2.finance.current := by
  induction path with
  | same packet => exact .nil
  | submit inventory word => exact World.financialRun inventory word
  | handoff inventory fresh => exact World.handoffFinancialRun inventory fresh
  | append earlier later before after => exact before.concatRuns _ after

def financialSlotAlong {first last : Packet} (path : Evolution first last)
    (index : Nat) (slot : ObligationSlot (Financial.Family.vocabulary sources))
    (present : first.2.finance.current.slots[index]? = some slot) :=
  Financial.Family.Migration.follow sources (financeAlong path) index slot present

theorem every_actual_path_preserves_each_original_financial_address {first last : Packet}
    (path : Evolution first last) (index : Nat) (slot : ObligationSlot (Financial.Family.vocabulary sources))
    (present : first.2.finance.current.slots[index]? = some slot) :
    Financial.Family.Migration.identity sources (financialSlotAlong path index slot present).slot =
      Financial.Family.Migration.identity sources slot ∧
    ((financialSlotAlong path index slot present).path.records sources index) =
      (financeAlong path).events.filter (fun event => event.slot == index) :=
  ⟨(financialSlotAlong path index slot present).path.preserves_identity sources,
    (financialSlotAlong path index slot present).recorded⟩

theorem every_original_origin_and_full_history_reaches_the_same_actual_response
    (row : Responsibility.Row ⟨epoch,inventory⟩) :
    (original inventory row).row.origin = row.origin ∧
    row.state.history <+: (original inventory row).state.history :=
  Responsibility.every_actual_step_retains_its_original_admission_and_history (trace inventory).native row

theorem every_original_financial_slot_has_its_own_exact_boundary_path (index : Nat)
    (slot : ObligationSlot (Financial.Family.vocabulary sources))
    (present : inventory.finance.current.slots[index]? = some slot) :
    Financial.Family.Migration.identity sources (originalFinance inventory index slot present).slot =
      Financial.Family.Migration.identity sources slot ∧
    ((originalFinance inventory index slot present).path.records sources index) =
      (trace inventory).finance.events.filter (fun event => event.slot == index) :=
  ⟨(originalFinance inventory index slot present).path.preserves_identity sources,
    (originalFinance inventory index slot present).recorded⟩

/-- The path may include refused raw words. Accepted primitive histories form
an explicit subrelation, with no authority assigned to a refused request. -/
def Accepted {first last : Packet} : Evolution first last → Prop
  | .same _ => True
  | @Evolution.submit epoch inventory word =>
      ∀ item ∈ (Mandate.law base epoch.scope).rawItems (current epoch inventory.inputs) word,
        (Mandate.law base epoch.scope).Valid item.before item.request
  | .handoff _ _ => True
  | .append before after => Accepted before ∧ Accepted after

def LegallyReachableFrom (first last : Packet) : Prop := ∃ path : Evolution first last, Accepted path

def ResponsibilityActive (packet : Packet) : Prop :=
  ∃ (row : Responsibility.Row packet) (index : Fin row.state.slots.length)
    (obligation : AdmittedObligation row.V), row.state.slots[index.val]? = some (.live obligation)

theorem active_responsibility_prevents_whole_termination {packet : Packet} (active : ResponsibilityActive packet) :
    ¬ Responsibility.WholeTerminationReceipt packet := by
  obtain ⟨row,index,obligation,present⟩ := active
  have pending := Responsibility.a_live_original_slot_prevents_total_settlement row index obligation present
  intro receipt
  have complete := Responsibility.settled_iff_whole_termination_receipts.mpr receipt
  rw [pending] at complete
  cases complete

theorem every_actual_cut_has_its_source_bounded_joint_response {first last : Packet}
    (path : Evolution first last) (active : ResponsibilityActive last) :
    ∃ response : Trace last.2,
      response = Progress.Runtime.trace last.2 ∧
      response.steps ≤ remaining last.2 + 1 ∧
      Nonempty (Future.Openness response.ending.2.1.event.original.original.decision) ∧
      (∀ row : Responsibility.Row first,
        let located := Responsibility.transport (.append path response.native) row
        located.row.origin = row.origin ∧ row.state.history <+: located.state.history ∧
          Nonempty (located.native.Run row.origin.initial located.state)) ∧
      (current last.1 last.2.inputs).clock < (current response.packet.1 response.packet.2.inputs).clock ∧
      ¬ Responsibility.WholeTerminationReceipt last := by
  refine ⟨Progress.Runtime.trace last.2,rfl,(Progress.Runtime.fromRoot last.2).2,
    ⟨(Progress.Runtime.trace last.2).ending.2.1.openness⟩,?_,
    (Progress.Runtime.trace last.2).the_actual_boundary_is_not_a_clock_self_loop,
    active_responsibility_prevents_whole_termination active⟩
  intro row
  have kept := Responsibility.every_actual_step_retains_its_original_admission_and_history
    (.append path (Progress.Runtime.trace last.2).native) row
  exact ⟨kept.1,kept.2,⟨(Responsibility.transport (.append path (Progress.Runtime.trace last.2).native) row).complete⟩⟩

theorem every_legal_cut_has_the_same_joint_response {first last : Packet}
    (reachable : LegallyReachableFrom first last) (active : ResponsibilityActive last) :
    ∃ path : Evolution first last, Accepted path ∧
      ∃ response : Trace last.2, response = Progress.Runtime.trace last.2 ∧
        response.steps ≤ remaining last.2 + 1 ∧
        (∀ row : Responsibility.Row first,
          (Responsibility.transport (.append path response.native) row).row.origin = row.origin ∧
          row.state.history <+: (Responsibility.transport (.append path response.native) row).state.history) ∧
        ¬ Responsibility.WholeTerminationReceipt last := by
  obtain ⟨path,legal⟩ := reachable
  obtain ⟨response,exact,bound,opening,rows,clock,notTerminal⟩ := every_actual_cut_has_its_source_bounded_joint_response path active
  exact ⟨path,legal,response,exact,bound,fun row => ⟨(rows row).1,(rows row).2.1⟩,notTerminal⟩

variable {inventory}
def afterHistory (history : List (List Action)) := Progress.Runtime.trace (Event.run ⟨epoch,inventory⟩ history).2

def historyPath (history : List (List Action)) : Evolution ⟨epoch,inventory⟩ (afterHistory (inventory := inventory) history).packet :=
  .append (Event.runEvolution ⟨epoch,inventory⟩ history) (afterHistory history).native

def originalAfterHistory (history : List (List Action)) (row : Responsibility.Row ⟨epoch,inventory⟩) :=
  Responsibility.transport (historyPath history) row

def originalRunAfterHistory (history : List (List Action)) (row : Responsibility.Row ⟨epoch,inventory⟩) :=
  (originalAfterHistory history row).complete

theorem every_finite_actual_history_keeps_all_original_rows (history : List (List Action))
    (row : Responsibility.Row ⟨epoch,inventory⟩) :
    (originalAfterHistory history row).row.origin = row.origin ∧
    row.state.history <+: (originalAfterHistory history row).state.history :=
  Responsibility.every_actual_step_retains_its_original_admission_and_history (historyPath history) row

variable (inventory)
theorem the_same_actual_root_consumes_all_origins_openness_settlement_and_next :
    (∀ row : Responsibility.Row ⟨epoch,inventory⟩,
      (original inventory row).row.origin = row.origin ∧
        row.state.history <+: (original inventory row).state.history) ∧
    Nonempty (Future.Openness (trace inventory).ending.2.1.event.original.original.decision) ∧
    (Responsibility.settled (packet inventory) = true ↔ Responsibility.WholeTerminationReceipt (packet inventory)) ∧
    (∀ slot : Responsibility.Slot (packet inventory), Nonempty (Responsibility.SlotDisposition slot)) ∧
    HEq ((Progress.Runtime.facade inventory).readoutAt
      (Progress.Runtime.activated inventory (Progress.Runtime.ordinal inventory)) (.inr ()))
      ((Progress.Runtime.activated inventory (Progress.Runtime.ordinal inventory)).tick.generated.projectionOutcome (.component ())) ∧
    HEq (Progress.Runtime.activated inventory (Progress.Runtime.ordinal inventory)).tick.generated.wholeLedgerWriteBack
      ((Progress.Runtime.activated inventory (Progress.Runtime.ordinal inventory)).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
        (Progress.Runtime.activated inventory (Progress.Runtime.ordinal inventory)).current.visit.current) ∧
    (Progress.Runtime.activated inventory (Progress.Runtime.ordinal inventory)).tick.nextCurrent =
      (Progress.Runtime.facade inventory).process.stateAt ((Progress.Runtime.facade inventory).process.successor
        (Progress.Runtime.activated inventory (Progress.Runtime.ordinal inventory)).state) := by
  have factor := (Progress.Runtime.facade inventory).readoutAt_factorizes
    (Progress.Runtime.activated inventory (Progress.Runtime.ordinal inventory)) (.inr ())
  exact ⟨every_original_origin_and_full_history_reaches_the_same_actual_response inventory,
    ⟨opening inventory⟩,Responsibility.settled_iff_whole_termination_receipts,
    fun slot => ⟨boundarySlot inventory slot⟩,factor.2.2.2.1,factor.2.2.1,factor.2.2.2.2⟩

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Response
