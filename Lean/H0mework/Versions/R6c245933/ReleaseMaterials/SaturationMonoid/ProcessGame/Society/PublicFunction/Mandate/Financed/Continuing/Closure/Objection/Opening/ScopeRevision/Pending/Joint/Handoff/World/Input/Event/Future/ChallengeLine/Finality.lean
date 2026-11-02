import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.ChallengeLine.Runtime

/-! Semantic consumption of actual saved native rows. A terminal slot retains
its original Claim and recorded withdrawal; a pending slot remains live. -/

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.ChallengeLine.Finality
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
noncomputable section
variable (origin : Origin)
abbrev family := Mandate.Challenge.fromHistory origin.bound

inductive Withdrawal (claim : Mandate.Challenge.Claim (family origin) origin.inputs) :
    Mandate.Challenge.Event (family origin) origin.inputs → Type where
  | inOrigin (target : Mandate.Challenge.Target (family origin) origin.inputs claim)
      (attempt : Mandate.Challenge.Attempt (family origin) origin.inputs (target.claim (family origin) origin.inputs))
      (accepted : (Mandate.law base origin.scope).Valid
        (attempt.position.item (family origin) origin.inputs).before (attempt.position.item (family origin) origin.inputs).request) :
      Withdrawal claim (.attempt claim target attempt)
  | remote (inputs : List (List Action)) (target : Mandate.Challenge.Cross.Target (family origin) claim inputs)
      (attempt : Mandate.Challenge.Attempt (family origin) inputs target.claim)
      (accepted : (Mandate.law base origin.scope).Valid
        (attempt.position.item (family origin) inputs).before (attempt.position.item (family origin) inputs).request) :
      Withdrawal claim (.remoteAttempt claim inputs target attempt)

def readFulfilled (event : Mandate.Challenge.Event (family origin) origin.inputs)
    (claim : Mandate.Challenge.Claim (family origin) origin.inputs)
    (address : Financial.InstructionOrigin (Mandate.Challenge.I (family origin) origin.inputs))
    (receipt : origin.V.FulfilledAt event claim address) : Withdrawal origin claim event := by
  cases receipt with
  | inl localReceipt =>
    cases event with
    | birth original => exact nomatch localReceipt
    | reaffirm original previous receipt => exact nomatch localReceipt
    | attempt original target attempt =>
      rcases localReceipt with ⟨rfl,_,accepted⟩
      exact .inOrigin target attempt accepted
    | remoteReaffirm original inputs target receipt => exact nomatch localReceipt
    | remoteAttempt original inputs target attempt => exact nomatch localReceipt
    | scopeBoundary original source later receipt => exact nomatch localReceipt
  | inr remoteReceipt =>
    cases event with
    | birth original => exact nomatch remoteReceipt
    | reaffirm original previous receipt => exact nomatch remoteReceipt
    | attempt original target attempt => exact nomatch remoteReceipt
    | remoteReaffirm original inputs target receipt => exact nomatch remoteReceipt
    | remoteAttempt original inputs target attempt =>
      rcases remoteReceipt with ⟨rfl,_,accepted⟩
      exact .remote inputs target attempt accepted
    | scopeBoundary original source later receipt => exact nomatch remoteReceipt

def readArchive (archive : TerminalArchive origin.V) : Withdrawal origin archive.obligation.content archive.sourceEvent := by
  cases archive.receipt with
  | fulfilled receipt => exact readFulfilled origin archive.sourceEvent archive.obligation.content archive.obligation.scope receipt
  | waived impossible => exact nomatch impossible
  | invalidated impossible => exact nomatch impossible
  | abandonedWithConsequence impossible => exact nomatch impossible
  | impossibleResidueAccepted impossible => exact nomatch impossible

variable {origin}
def Withdrawal.inputs {claim event} : Withdrawal origin claim event → List (List Action)
  | .inOrigin .. => origin.inputs
  | .remote inputs .. => inputs

def Withdrawal.item {claim event} (receipt : Withdrawal origin claim event) : ExecutionItem Bool Good Mandate.Source.Port (State Bool Unit) Unit :=
  match receipt with
  | .inOrigin target attempt accepted => attempt.position.item (family origin) origin.inputs
  | .remote inputs target attempt accepted => attempt.position.item (family origin) inputs

def Withdrawal.snapshot {claim event} : Withdrawal origin claim event → State Bool Unit
  | .inOrigin target .. => (target.claim (family origin) origin.inputs).snapshot (family origin) origin.inputs
  | .remote inputs target .. => target.snapshot (family origin)

theorem Withdrawal.actually_withdraws_both_authority_legs {claim event} (receipt : Withdrawal origin claim event) :
    ((Mandate.law base origin.scope).step receipt.item.before receipt.item.request).technology.holder = none ∧
    ((Mandate.law base origin.scope).step receipt.item.before receipt.item.request).technology.offered = none ∧
    ((Mandate.law base origin.scope).step receipt.item.before receipt.item.request).technology.version = receipt.snapshot.version + 1 := by
  cases receipt with
  | inOrigin target attempt accepted => exact attempt.actual_withdrawal (family origin) origin.inputs _ accepted
  | remote inputs target attempt accepted => exact attempt.actual_withdrawal (family origin) inputs _ accepted


variable (origin)
def slotClaim : ObligationSlot origin.V → Mandate.Challenge.Claim (family origin) origin.inputs
  | .live obligation => obligation.content
  | .terminal archive => archive.obligation.content

private theorem boundary_keeps_claim {obligation : AdmittedObligation origin.V} {event : origin.V.SourceEvent}
    (disposition : BoundaryDisposition origin.V obligation event) :
    slotClaim origin disposition.targetSlot = obligation.content := by
  cases disposition with
  | carry carry => exact carry.target_content
  | bearerRelease release => cases release <;> rfl
  | terminal receipt =>
    cases receipt with
    | final receipt => rfl
    | superseded impossible => exact nomatch impossible.incidence

private theorem run_keeps_original (process : NativeResponsibilityProcess origin.V)
    (admissions : ∀ event, (process.admissionPayload event).content = origin.claim)
    {first last : ResponsibilityState origin.V} (path : process.Run first last)
    (initial : ∀ slot ∈ first.slots, slotClaim origin slot = origin.claim) :
    ∀ slot ∈ last.slots, slotClaim origin slot = origin.claim := by
  induction path with
  | nil => exact initial
  | @step middle path edge ih =>
    intro slot member
    cases edge with
    | admit event =>
      rcases List.mem_append.mp member with previous | fresh
      · exact ih slot previous
      · have same : slot = .live (process.admissionPayload event).toObligation := List.mem_singleton.mp fresh
        rw [same]
        exact admissions event
    | cross address obligation present event =>
      rcases List.mem_or_eq_of_mem_set member with previous | changed
      · exact ih slot previous
      · rw [changed,boundary_keeps_claim]
        exact ih (.live obligation) (present ▸ List.get_mem middle.slots address)
    | reopen address archive present event => exact nomatch (process.reopenPayload event).incidence

private theorem saved_admissions {oldScope : Mandate.Scope (Party := Bool) (Good := Good) (Port := Mandate.Source.Port)}
    {bound : BoundSource base oldScope} {inputs : List (List Action)}
    (fresh : Handoff.Ready bound inputs) (record : Mandate.Challenge.Cross.Resident bound inputs)
    (code : Handoff.Continuation.Challenge.Code (oldScope := oldScope)) :
    ∀ event, ((Handoff.Continuation.Challenge.processAt fresh record code).admissionPayload event).content = record.original := by
  induction code with
  | seed => intro event; rfl
  | step past source later ih => exact ih

private theorem row_keeps_original {packet : Packet} (row : Row packet) :
    ∀ slot ∈ row.state.current.slots, slotClaim row.origin slot = row.origin.claim := by
  have admissions : ∀ event, (row.native.admissionPayload event).content = row.origin.claim := by
    cases row with
    | current record member => intro event; rfl
    | past entry member => exact saved_admissions entry.origin.1.fresh entry.origin.2 entry.saved.code
  exact run_keeps_original row.origin row.native admissions row.state.generated (by
    intro slot impossible
    exact nomatch impossible)

def Recorded (archive : TerminalArchive origin.V) (state : ResponsibilityState origin.V) : Prop :=
  ∃ address, LifecycleEvent.terminal address archive.obligation archive.sourceEvent archive.receipt ∈ state.history

private theorem run_records_archives (process : NativeResponsibilityProcess origin.V)
    {first last : ResponsibilityState origin.V} (path : process.Run first last)
    (initial : ∀ archive, .terminal archive ∈ first.slots → Recorded origin archive first) :
    ∀ archive, .terminal archive ∈ last.slots → Recorded origin archive last := by
  induction path with
  | nil => exact initial
  | @step middle path edge ih =>
    intro archive member
    have retain : Recorded origin archive middle → Recorded origin archive edge.target := by
      rintro ⟨address,recorded⟩
      exact ⟨address,by rw [NativeResponsibilityProcess.Edge.history_append]; exact List.mem_append_left _ recorded⟩
    cases edge with
    | admit event =>
      rcases List.mem_append.mp member with previous | fresh
      · exact retain (ih archive previous)
      · have impossible := List.mem_singleton.mp fresh
        cases impossible
    | cross address obligation present event =>
      rcases List.mem_or_eq_of_mem_set member with previous | changed
      · exact retain (ih archive previous)
      · cases disposition : process.boundaryDisposition event with
        | carry carry => simp only [disposition,BoundaryDisposition.targetSlot] at changed; cases changed
        | bearerRelease release => simp only [disposition,BoundaryDisposition.targetSlot] at changed; cases changed
        | terminal receipt =>
          cases receipt with
          | superseded successor => simp only [disposition,BoundaryDisposition.targetSlot] at changed; cases changed
          | final receipt =>
            simp only [disposition,BoundaryDisposition.targetSlot] at changed
            have same : archive = ⟨obligation,process.boundarySource event,receipt⟩ := ObligationSlot.terminal.inj changed
            subst archive
            exact ⟨address.val,by
              rw [NativeResponsibilityProcess.Edge.history_append]
              apply List.mem_append_right
              simp only [NativeResponsibilityProcess.Edge.lifecycleEvent,disposition,List.mem_singleton]
              rfl⟩
    | reopen address previous present event =>
      rcases List.mem_or_eq_of_mem_set member with previous | changed
      · exact retain (ih archive previous)
      · cases changed

private theorem row_records_archives {packet : Packet} (row : Row packet) :
    ∀ archive, .terminal archive ∈ row.state.current.slots → Recorded row.origin archive row.state.current :=
  run_records_archives row.origin row.native row.state.generated (by intro archive impossible; exact nomatch impossible)

inductive SlotDisposition {packet : Packet} (position : Located origin packet) where
  | pending (obligation : AdmittedObligation origin.V)
      (slots : position.state.current.slots = [.live obligation])
      (content : obligation.content = origin.claim)
  | withdrawn (archive : TerminalArchive origin.V)
      (slots : position.state.current.slots = [.terminal archive])
      (content : archive.obligation.content = origin.claim)
      (recorded : Recorded origin archive position.state.current)
      (actual : Withdrawal origin archive.obligation.content archive.sourceEvent)

def readRow {packet : Packet} (position : Located origin packet) : SlotDisposition origin position := by
  rcases position with ⟨row,same⟩
  cases same
  have content := row_keeps_original row
  have recorded := row_records_archives row
  cases row with
  | current record member =>
    rcases record with ⟨inputs,original,history,within⟩
    cases history with
    | pending target state slots => exact .pending (Mandate.Challenge.Cross.tracked _ target) slots rfl
    | closed state archive slots =>
      refine .withdrawn archive slots ?_ ?_ (readArchive ⟨packet.1.scope,packet.1.bound,inputs,original⟩ archive)
      · exact content (.terminal archive) (by change _ ∈ state.current.slots; rw [slots]; exact List.mem_singleton_self _)
      · exact recorded archive (by change _ ∈ state.current.slots; rw [slots]; exact List.mem_singleton_self _)
  | past entry member =>
    cases entry.saved.shape with
    | pending obligation slots same jurisdiction anchor => exact .pending obligation slots same
    | closed archive slots =>
      refine .withdrawn archive slots ?_ ?_ (readArchive ⟨entry.origin.1.originalScope,entry.origin.1.original,entry.origin.2.originInputs,entry.origin.2.original⟩ archive)
      · exact content (.terminal archive) (by change _ ∈ entry.saved.state.current.slots; rw [slots]; exact List.mem_singleton_self _)
      · exact recorded archive (by change _ ∈ entry.saved.state.current.slots; rw [slots]; exact List.mem_singleton_self _)


theorem original_claim_is_preserved_at_every_live_or_archived_slot {packet : Packet}
    (position : Located origin packet) (slot : ObligationSlot origin.V) (member : slot ∈ position.state.current.slots) :
    slotClaim origin slot = origin.claim := by
  rcases position with ⟨row,same⟩
  cases same
  exact row_keeps_original row slot member

theorem an_actual_archive_requires_its_original_recorded_withdrawal {packet : Packet}
    (position : Located origin packet) (archive : TerminalArchive origin.V)
    (member : .terminal archive ∈ position.state.current.slots) :
    archive.obligation.content = origin.claim ∧ Recorded origin archive position.state.current ∧
    ((Mandate.law base origin.scope).step (readArchive origin archive).item.before (readArchive origin archive).item.request).technology.holder = none ∧
    ((Mandate.law base origin.scope).step (readArchive origin archive).item.before (readArchive origin archive).item.request).technology.offered = none ∧
    ((Mandate.law base origin.scope).step (readArchive origin archive).item.before (readArchive origin archive).item.request).technology.version =
      (readArchive origin archive).snapshot.version + 1 := by
  refine ⟨original_claim_is_preserved_at_every_live_or_archived_slot origin position (.terminal archive) member,?_,
    (readArchive origin archive).actually_withdraws_both_authority_legs⟩
  rcases position with ⟨row,same⟩
  cases same
  exact row_records_archives row archive member

def SlotDisposition.isPending {packet : Packet} {position : Located origin packet} : SlotDisposition origin position → Bool
  | .pending .. => true
  | .withdrawn .. => false

variable {epoch : Epoch} (inventory : Inventory epoch) (depth : Nat)

def allRows (row : Row (Runtime.fromRoot inventory depth).packet) :
    SlotDisposition row.origin ⟨row,rfl⟩ := readRow row.origin ⟨row,rfl⟩

def newbornAfterEvents (active : Mandate.Response.Active (current epoch inventory.inputs))
    (history : List (List Action)) (laterDepth : Nat) :
    SlotDisposition (birthOrigin inventory active)
      ((Runtime.fromRoot inventory depth).newbornAfterEvents active history laterDepth).1 :=
  readRow _ _

theorem every_original_archive_and_the_financial_account_share_the_actual_root :
    (∀ (row : Row (Runtime.fromRoot inventory depth).packet) (archive : TerminalArchive row.origin.V),
      .terminal archive ∈ row.state.current.slots →
      archive.obligation.content = row.origin.claim ∧ Recorded row.origin archive row.state.current ∧
      ((Mandate.law base row.origin.scope).step (readArchive row.origin archive).item.before
        (readArchive row.origin archive).item.request).technology.holder = none ∧
      ((Mandate.law base row.origin.scope).step (readArchive row.origin archive).item.before
        (readArchive row.origin archive).item.request).technology.offered = none ∧
      ((Mandate.law base row.origin.scope).step (readArchive row.origin archive).item.before
        (readArchive row.origin archive).item.request).technology.version = (readArchive row.origin archive).snapshot.version + 1) ∧
    Financial.Family.ledgerClaims sources (Runtime.fromRoot inventory depth).packet.2.finance.current =
      (current (Runtime.fromRoot inventory depth).packet.1 (Runtime.fromRoot inventory depth).packet.2.inputs).claims ∧
    HEq ((Runtime.facade inventory depth).readoutAt (Runtime.activated inventory depth (Runtime.ordinal inventory)) (.inr ()))
      ((Runtime.activated inventory depth (Runtime.ordinal inventory)).tick.generated.projectionOutcome (.component ())) ∧
    HEq (Runtime.activated inventory depth (Runtime.ordinal inventory)).tick.generated.wholeLedgerWriteBack
      ((Runtime.activated inventory depth (Runtime.ordinal inventory)).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
        (Runtime.activated inventory depth (Runtime.ordinal inventory)).current.visit.current) ∧
    (Runtime.activated inventory depth (Runtime.ordinal inventory)).tick.nextCurrent =
      (Runtime.facade inventory depth).process.stateAt ((Runtime.facade inventory depth).process.successor
        (Runtime.activated inventory depth (Runtime.ordinal inventory)).state) := by
  have root := Runtime.the_actual_newborn_full_run_financial_account_and_own_next_share_the_original_root inventory depth
  exact ⟨fun row archive member => an_actual_archive_requires_its_original_recorded_withdrawal row.origin ⟨row,rfl⟩ archive member,
    root.2.2.2.1,root.2.2.2.2.1,root.2.2.2.2.2.1,root.2.2.2.2.2.2⟩

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.ChallengeLine.Finality
