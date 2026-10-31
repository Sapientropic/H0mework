import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Runtime

/-! A finite consumer of the actual inventory's native slots. This does not
create a terminal event: an archive must already contain its original receipt. -/
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Responsibility
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
noncomputable section

inductive Row (packet : Packet) where
  | currentGrant (entry : Mandate.Challenge.Cross.GrantResident packet.1.bound packet.2.inputs)
      (member : entry ∈ packet.2.grants)
  | pastGrant (entry : GrantCohort) (member : entry ∈ packet.2.pastGrants)
  | currentChallenge (entry : Mandate.Challenge.Cross.Resident packet.1.bound packet.2.inputs)
      (member : entry ∈ packet.2.objections)
  | pastChallenge (entry : ChallengeCohort packet.1.scope) (member : entry ∈ packet.2.pastChallenges)
  | currentService (index : packet.1.source.Slot)
  | pastService (entry : ServiceCohort packet.1.source.seed.initial.clock) (member : entry ∈ packet.2.pastServices)
  | finance

variable {packet : Packet}

def Row.V : Row packet → Vocabulary
  | .currentGrant .. | .pastGrant .. => Continuation.Grant.V
  | .currentChallenge entry _ => Mandate.Challenge.V (Mandate.Challenge.fromHistory packet.1.bound) entry.originInputs
  | .pastChallenge entry _ => Mandate.Challenge.V (Mandate.Challenge.fromHistory entry.origin.1.original) entry.origin.2.originInputs
  | .currentService _ => OutstandingSource.History.NativeService.V packet.1.source (epochInputs packet.1.fresh)
  | .pastService entry _ => OutstandingSource.History.NativeService.V entry.origin.source entry.origin.originInputs
  | .finance => Financial.Family.vocabulary sources

def Row.state (row : Row packet) : ResponsibilityState row.V :=
  match row with
  | .currentGrant entry _ => entry.history.state
  | .pastGrant entry _ => entry.saved.state
  | .currentChallenge entry _ => entry.history.state.current
  | .pastChallenge entry _ => entry.saved.state.current
  | .currentService index => (packet.2.services index).state.current
  | .pastService entry _ => entry.saved.state.current
  | .finance => packet.2.finance.current

def census (packet : Packet) : List (Row packet) :=
  packet.2.grants.attach.map (fun entry => .currentGrant entry.val entry.property) ++
  packet.2.pastGrants.attach.map (fun entry => .pastGrant entry.val entry.property) ++
  packet.2.objections.attach.map (fun entry => .currentChallenge entry.val entry.property) ++
  packet.2.pastChallenges.attach.map (fun entry => .pastChallenge entry.val entry.property) ++
  (List.finRange packet.1.source.seed.task.slots.length).map Row.currentService ++
  packet.2.pastServices.attach.map (fun entry => .pastService entry.val entry.property) ++ [.finance]

theorem every_original_row_is_in_the_census (row : Row packet) : row ∈ census packet := by
  cases row with
  | currentGrant entry member => simp only [census,List.mem_append,List.mem_map]; exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨⟨entry,member⟩,List.mem_attach _ _,rfl⟩)))))
  | pastGrant entry member => simp only [census,List.mem_append,List.mem_map]; exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨⟨entry,member⟩,List.mem_attach _ _,rfl⟩)))))
  | currentChallenge entry member => simp only [census,List.mem_append,List.mem_map]; exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨⟨entry,member⟩,List.mem_attach _ _,rfl⟩))))
  | pastChallenge entry member => simp only [census,List.mem_append,List.mem_map]; exact Or.inl (Or.inl (Or.inl (Or.inr ⟨⟨entry,member⟩,List.mem_attach _ _,rfl⟩)))
  | currentService index => simp only [census,List.mem_append,List.mem_map]; exact Or.inl (Or.inl (Or.inr ⟨index,List.mem_finRange _,rfl⟩))
  | pastService entry member => simp only [census,List.mem_append,List.mem_map]; exact Or.inl (Or.inr ⟨⟨entry,member⟩,List.mem_attach _ _,rfl⟩)
  | finance => exact List.mem_append_right _ (List.mem_singleton_self _)

structure Slot (packet : Packet) where
  row : Row packet
  index : Fin row.state.slots.length

def Slot.value (slot : Slot packet) : ObligationSlot slot.row.V := slot.row.state.slots.get slot.index

inductive SlotDisposition (slot : Slot packet) where
  | pending (obligation : AdmittedObligation slot.row.V) (present : slot.value = .live obligation)
  | archived (archive : TerminalArchive slot.row.V) (present : slot.value = .terminal archive)

def inspect (slot : Slot packet) : SlotDisposition slot :=
  match present : slot.value with
  | .live obligation => .pending obligation present
  | .terminal archive => .archived archive present

def isTerminal {V : Vocabulary} : ObligationSlot V → Bool
  | .live _ => false
  | .terminal _ => true

def Row.settled (row : Row packet) : Bool := row.state.slots.all isTerminal

def ResponsibilitySettled (packet : Packet) : Prop :=
  ∀ (row : Row packet) (index : Fin row.state.slots.length), row.state.TerminalAt index.val

def settled (packet : Packet) : Bool := (census packet).all Row.settled

private theorem terminal_test {V : Vocabulary} (slots : List (ObligationSlot V)) :
    slots.all isTerminal = true ↔ ∀ index : Fin slots.length, ∃ archive, slots[index.val]? = some (.terminal archive) := by
  rw [List.all_eq_true]
  constructor
  · intro all index
    have tested := all (slots.get index) (List.get_mem slots index)
    cases same : slots.get index with
    | live obligation => rw [same] at tested; cases tested
    | terminal archive => exact ⟨archive,by simpa only [List.getElem?_eq_getElem index.isLt,List.get_eq_getElem] using congrArg some same⟩
  · intro all slot member
    obtain ⟨index,present⟩ := List.mem_iff_get.mp member
    obtain ⟨archive,terminal⟩ := all index
    have same : slots.get index = .terminal archive := by
      simpa only [List.getElem?_eq_getElem index.isLt,Option.some.injEq,List.get_eq_getElem] using terminal
    rw [← present,same]
    rfl

theorem settled_iff_every_original_slot_is_terminal : settled packet = true ↔ ResponsibilitySettled packet := by
  rw [settled,List.all_eq_true]
  constructor
  · intro all row
    exact (terminal_test row.state.slots).mp (all row (every_original_row_is_in_the_census row))
  · intro all row _
    exact (terminal_test row.state.slots).mpr (all row)

theorem a_live_original_slot_prevents_total_settlement (row : Row packet) (index : Fin row.state.slots.length)
    (obligation : AdmittedObligation row.V) (present : row.state.slots[index.val]? = some (.live obligation)) :
    settled packet = false := by
  cases tested : settled packet
  · rfl
  · obtain ⟨archive,terminal⟩ := settled_iff_every_original_slot_is_terminal.mp tested row index
    rw [present] at terminal
    cases terminal

theorem a_current_grant_is_still_an_original_live_responsibility
    (entry : Mandate.Challenge.Cross.GrantResident packet.1.bound packet.2.inputs)
    (member : entry ∈ packet.2.grants) : settled packet = false := by
  let row : Row packet := .currentGrant entry member
  let index : Fin row.state.slots.length := ⟨0,by change 0 < entry.history.state.slots.length; rw [entry.history.slots]; exact Nat.zero_lt_succ 0⟩
  exact a_live_original_slot_prevents_total_settlement row index entry.history.obligation (by
    change entry.history.state.slots[0]? = _
    rw [entry.history.slots]
    rfl)

theorem a_past_grant_remains_live_after_actual_authority_withdrawal
    (entry : GrantCohort) (member : entry ∈ packet.2.pastGrants) : settled packet = false := by
  let row : Row packet := .pastGrant entry member
  let index : Fin row.state.slots.length := ⟨0,by change 0 < entry.saved.state.slots.length; rw [entry.saved.slots]; exact Nat.zero_lt_succ 0⟩
  exact a_live_original_slot_prevents_total_settlement row index entry.origin.2.history.obligation (by
    change entry.saved.state.slots[0]? = _
    rw [entry.saved.slots]
    rfl)

def Row.isService : Row packet → Bool
  | .currentService _ | .pastService .. => true
  | _ => false

/-- The source service process permits terminal archives only with its own
actual payment receipt; this test includes every retained past service. -/
def TaskComplete (packet : Packet) : Prop :=
  ∀ (row : Row packet), row.isService = true →
    ∀ index : Fin row.state.slots.length, row.state.TerminalAt index.val

structure WholeTerminationReceipt (packet : Packet) : Prop where
  task : TaskComplete packet
  responsibilities : ResponsibilitySettled packet

theorem settled_iff_whole_termination_receipts : settled packet = true ↔ WholeTerminationReceipt packet := by
  constructor
  · intro tested
    have all := settled_iff_every_original_slot_is_terminal.mp tested
    exact ⟨fun row _ => all row,all⟩
  · intro receipt
    exact settled_iff_every_original_slot_is_terminal.mpr receipt.responsibilities

theorem completed_service_with_an_original_live_grant_is_not_whole_termination
    (_service : TaskComplete packet)
    (entry : Mandate.Challenge.Cross.GrantResident packet.1.bound packet.2.inputs)
    (member : entry ∈ packet.2.grants) : ¬ WholeTerminationReceipt packet := by
  intro receipt
  have yes := settled_iff_whole_termination_receipts.mpr receipt
  rw [a_current_grant_is_still_an_original_live_responsibility entry member] at yes
  cases yes

def fromRoot {epoch : Epoch} (inventory : Inventory epoch) := settled (Progress.Runtime.trace inventory).packet

theorem the_same_actual_root_cannot_erase_a_live_boundary_row {epoch : Epoch} (inventory : Inventory epoch)
    (row : Row (Progress.Runtime.trace inventory).packet) (index : Fin row.state.slots.length)
    (obligation : AdmittedObligation row.V) (present : row.state.slots[index.val]? = some (.live obligation)) :
    fromRoot inventory = false := a_live_original_slot_prevents_total_settlement row index obligation present


theorem an_existing_grant_is_not_forgotten_by_the_source_bounded_response {epoch : Epoch}
    (inventory : Inventory epoch) (entry : GrantCohort) (member : entry ∈ inventory.pastGrants) :
    fromRoot inventory = false := by
  let moved := (Progress.Runtime.trace inventory).native.grant entry member
  exact a_past_grant_remains_live_after_actual_authority_withdrawal moved.row moved.member

theorem arbitrary_actual_events_do_not_erase_the_original_grant {epoch : Epoch}
    (inventory : Inventory epoch) (entry : GrantCohort) (member : entry ∈ inventory.pastGrants)
    (history : List (List Action)) : fromRoot (Event.run ⟨epoch,inventory⟩ history).2 = false := by
  let moved := (Event.runEvolution ⟨epoch,inventory⟩ history).grant entry member
  exact an_existing_grant_is_not_forgotten_by_the_source_bounded_response _ moved.row moved.member

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Responsibility
