import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Execution

/-! Source-indexed symbolic authentication for actual paid sends. A symbol names
an event in the fixed source trace; it is not a cryptographic byte string.
The interface fixes the protocol interpretation of a site's local snapshot.
Site keys remain distinct even when `siteParty` maps several sites to one actor. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication

open Distributed Institutions.Capitalism.Universal.Source.Program

structure Scope where
  epoch : Nat
  instanceId : Nat
  phase : Nat
  deriving DecidableEq

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (code : Code Party Good Port Technology Instrument)

structure Interface where
  scope : Fin code.sites → LocalSnapshot Party Good Instrument → Scope

structure EnvelopeData (Actor : Type) (sites signals : Nat) where
  occurrence : Nat
  serial : Nat
  key : Fin sites
  actor : Actor
  recipient : Fin sites
  scope : Scope
  payload : Fin signals
  sentAfter : Nat
  deriving DecidableEq

abbrev Envelope := EnvelopeData Party code.sites code.signals

variable (interface : Interface code) (policy : code.Policy)
  (initial : RawCurrent Party Good Technology Instrument)

def frameAt (events : List (Event Party Good Port Technology Instrument code.sites)) (n : Nat) :=
  code.replay policy initial (events.take n)

def emittedEnvelope (frame : code.Frame) (n : Nat) (sender recipient : Fin code.sites) : Envelope code :=
  ⟨n, frame.sent.length, sender, code.siteParty sender, recipient,
    interface.scope sender (code.snapshot sender (code.rawAt initial frame)),
    code.readLocal sender (code.snapshot sender (code.rawAt initial frame)), frame.word.length⟩

def issuedAt (events : List (Event Party Good Port Technology Instrument code.sites))
    (n : Nat) : Option (Envelope code) :=
  match events[n]? with
  | some (.send sender recipient) =>
      let frame := frameAt code policy initial events n
      if ∀ item ∈ code.law.rawItems (code.rawAt initial frame) (code.sendCost sender recipient),
          code.law.Valid item.before item.request then
        some (emittedEnvelope code interface initial frame n sender recipient)
      else none
  | _ => none

def verify (events : List (Event Party Good Port Technology Instrument code.sites))
    (wire : Envelope code) : Bool :=
  decide (issuedAt code interface policy initial events wire.occurrence = some wire)

theorem verify_iff (events : List (Event Party Good Port Technology Instrument code.sites))
    (wire : Envelope code) :
    verify code interface policy initial events wire = true ↔
      issuedAt code interface policy initial events wire.occurrence = some wire := by
  simp only [verify, decide_eq_true_eq]

/-- Authentication reconstructs the actual sending event, payment and complete
body; no caller-supplied signature law or completed certificate is an input. -/
theorem authenticated_origin (events : List (Event Party Good Port Technology Instrument code.sites))
    (wire : Envelope code) (accepted : verify code interface policy initial events wire = true) :
    let frame := frameAt code policy initial events wire.occurrence
    events[wire.occurrence]? = some (.send wire.key wire.recipient) ∧
      wire = emittedEnvelope code interface initial frame wire.occurrence wire.key wire.recipient ∧
      (∀ item ∈ code.law.rawItems (code.rawAt initial frame) (code.sendCost wire.key wire.recipient),
        code.law.Valid item.before item.request) ∧
      wire.actor = code.siteParty wire.key ∧
      (code.step policy initial frame (.send wire.key wire.recipient)).sent =
        frame.sent ++ [⟨wire.key, wire.recipient, wire.payload, wire.sentAfter⟩] := by
  have issued := (verify_iff code interface policy initial events wire).mp accepted
  unfold issuedAt at issued
  split at issued <;> try contradiction
  rename_i sender recipient event
  dsimp only at issued
  split at issued <;> try contradiction
  rename_i paid
  have same := Option.some.inj issued
  have key : wire.key = sender := (congrArg EnvelopeData.key same).symm
  have recipient_eq : wire.recipient = recipient := (congrArg EnvelopeData.recipient same).symm
  have payload := (congrArg EnvelopeData.payload same).symm
  have sentAfter := (congrArg EnvelopeData.sentAfter same).symm
  dsimp only
  rw [key, recipient_eq]
  refine ⟨event, same.symm, paid, (congrArg EnvelopeData.actor same).symm, ?_⟩
  rw [payload, sentAfter]
  exact code.send_is_an_actual_local_reading policy initial _ sender recipient paid

theorem same_symbol_same_message
    (events : List (Event Party Good Port Technology Instrument code.sites))
    (first second : Envelope code)
    (one : verify code interface policy initial events first = true)
    (two : verify code interface policy initial events second = true)
    (same : first.occurrence = second.occurrence) : first = second := by
  have h := (verify_iff code interface policy initial events first).mp one
  rw [same, (verify_iff code interface policy initial events second).mp two] at h
  exact (Option.some.inj h).symm

inductive Rejection where
  | missingWire | missingDelivery | unauthenticated | wrongRecipient | staleScope
  | unpaidDelivery | duplicate
  deriving DecidableEq

inductive VerdictData (Wire : Type) where
  | accepted (wire : Wire)
  | rejected (reason : Rejection)
  deriving DecidableEq

abbrev Verdict := VerdictData (Envelope code)

def deliveredAt (events : List (Event Party Good Port Technology Instrument code.sites))
    (n serial : Nat) : Bool :=
  match events[n]? with
  | some (.deliver address) => address == serial
  | _ => false

def check (events : List (Event Party Good Port Technology Instrument code.sites))
    (receiver : Fin code.sites) (n : Nat) (seen : List Nat) (wire : Envelope code) : Verdict code :=
  if deliveredAt code events n wire.serial ≠ true then .rejected .missingDelivery
  else if ¬ wire.occurrence < n then .rejected .unauthenticated
  else if verify code interface policy initial events wire ≠ true then .rejected .unauthenticated
  else if wire.recipient ≠ receiver then .rejected .wrongRecipient
  else if wire.scope ≠ interface.scope receiver
      (code.snapshot receiver (code.rawAt initial (frameAt code policy initial events n))) then
    .rejected .staleScope
  else if ¬ ∀ item ∈ code.law.rawItems (code.rawAt initial (frameAt code policy initial events n))
      (code.deliveryCost receiver), code.law.Valid item.before item.request then .rejected .unpaidDelivery
  else if wire.occurrence ∈ seen then .rejected .duplicate
  else .accepted wire

theorem check_sound (events : List (Event Party Good Port Technology Instrument code.sites))
    (receiver : Fin code.sites) (n : Nat) (seen : List Nat) (wire result : Envelope code)
    (accepted : check code interface policy initial events receiver n seen wire = .accepted result) :
    result = wire ∧ deliveredAt code events n wire.serial = true ∧ wire.occurrence < n ∧
      verify code interface policy initial events wire = true ∧ wire.recipient = receiver ∧
      wire.scope = interface.scope receiver
        (code.snapshot receiver (code.rawAt initial (frameAt code policy initial events n))) ∧
      (∀ item ∈ code.law.rawItems (code.rawAt initial (frameAt code policy initial events n))
        (code.deliveryCost receiver), code.law.Valid item.before item.request) ∧ wire.occurrence ∉ seen := by
  unfold check at accepted
  split_ifs at accepted; simp_all

structure ReceiptData (Wire : Type) where
  wire : Wire
  delivery : Nat
  deriving DecidableEq

abbrev Receipt := ReceiptData (Envelope code)

structure EntryData (Wire : Type) where
  delivery : Nat
  submitted : Option Wire
  verdict : VerdictData Wire
  deriving DecidableEq

abbrev Entry := EntryData (Envelope code)

structure ReceiverStateData (Wire : Type) where
  receipts : List (ReceiptData Wire)
  audit : List (EntryData Wire)
  deriving DecidableEq

abbrev ReceiverState := ReceiverStateData (Envelope code)

def receive (events : List (Event Party Good Port Technology Instrument code.sites))
    (receiver : Fin code.sites) (n : Nat) (wire : Option (Envelope code))
    (state : ReceiverState code) : ReceiverState code :=
  let verdict := match wire with
    | none => VerdictData.rejected .missingWire
    | some message => check code interface policy initial events receiver n
        (state.receipts.map fun receipt => receipt.wire.occurrence) message
  { receipts := match verdict with
      | .accepted message => state.receipts ++ [⟨message, n⟩]
      | .rejected _ => state.receipts
    audit := state.audit ++ [⟨n, wire, verdict⟩] }

def run (events : List (Event Party Good Port Technology Instrument code.sites))
    (receiver : Fin code.sites) (incoming : Nat → Option (Envelope code)) : Nat → ReceiverState code
  | 0 => ⟨[], []⟩
  | n + 1 => receive code interface policy initial events receiver n (incoming n)
      (run events receiver incoming n)

theorem receipts_authenticated
    (events : List (Event Party Good Port Technology Instrument code.sites))
    (receiver : Fin code.sites) (incoming : Nat → Option (Envelope code)) (count : Nat)
    (receipt : Receipt code)
    (present : receipt ∈ (run code interface policy initial events receiver incoming count).receipts) :
    verify code interface policy initial events receipt.wire = true ∧
      receipt.wire.recipient = receiver ∧ receipt.wire.occurrence < receipt.delivery ∧
      receipt.delivery < count ∧ deliveredAt code events receipt.delivery receipt.wire.serial = true := by
  induction count with
  | zero => simp [run] at present
  | succ n ih =>
    simp only [run, receive] at present
    split at present
    · rename_i message outcome
      rcases List.mem_append.mp present with old | fresh
      · obtain ⟨auth, who, before, bounded, delivered⟩ := ih old
        exact ⟨auth, who, before, by omega, delivered⟩
      · have same := List.mem_singleton.mp fresh
        subst receipt
        cases h : incoming n with
        | none => simp [h] at outcome
        | some wire =>
          simp only [h] at outcome
          obtain ⟨rfl, delivered, before, auth, who, rest⟩ :=
            check_sound code interface policy initial events receiver n _ wire message outcome
          exact ⟨auth, who, before, Nat.lt_succ_self _, delivered⟩
    · obtain ⟨auth, who, before, bounded, delivered⟩ := ih present
      exact ⟨auth, who, before, by omega, delivered⟩

theorem receipt_symbols_unique
    (events : List (Event Party Good Port Technology Instrument code.sites))
    (receiver : Fin code.sites) (incoming : Nat → Option (Envelope code)) (count : Nat) :
    ((run code interface policy initial events receiver incoming count).receipts.map
      fun receipt => receipt.wire.occurrence).Nodup := by
  induction count with
  | zero => simp [run]
  | succ n ih =>
    simp only [run, receive]
    split
    · rename_i message outcome
      have fresh : message.occurrence ∉
          ((run code interface policy initial events receiver incoming n).receipts.map
            fun receipt => receipt.wire.occurrence) := by
        cases h : incoming n with
        | none => simp [h] at outcome
        | some wire =>
          simp only [h] at outcome
          obtain ⟨rfl, _, _, _, _, _, _, unused⟩ :=
            check_sound code interface policy initial events receiver n _ wire message outcome
          exact unused
      simpa using List.nodup_append.mpr ⟨ih, by simp, by simpa using fresh⟩
    · exact ih

/-- Conflict is indexed by the complete protocol slot. Different phases are
different signing duties, even if their payloads differ. -/
def Conflicts (first second : Envelope code) : Prop :=
  first.key = second.key ∧ first.scope = second.scope ∧ first.payload ≠ second.payload

instance (first second : Envelope code) : Decidable (Conflicts code first second) := by
  unfold Conflicts; infer_instance

def evidence (state : ReceiverState code) : List (Receipt code × Receipt code) :=
  (state.receipts.product state.receipts).filter fun pair => decide (Conflicts code pair.1.wire pair.2.wire)

theorem evidence_iff (state : ReceiverState code) (first second : Receipt code) :
    (first, second) ∈ evidence code state ↔
      first ∈ state.receipts ∧ second ∈ state.receipts ∧ Conflicts code first.wire second.wire := by
  rw [evidence, List.mem_filter]
  constructor
  · rintro ⟨inside, conflict⟩
    exact ⟨(List.mem_product.mp inside).1, (List.mem_product.mp inside).2, of_decide_eq_true conflict⟩
  · rintro ⟨one, two, conflict⟩
    exact ⟨List.mem_product.mpr ⟨one, two⟩, decide_eq_true conflict⟩

theorem generated_evidence_has_two_actual_sends
    (events : List (Event Party Good Port Technology Instrument code.sites))
    (receiver : Fin code.sites) (incoming : Nat → Option (Envelope code)) (count : Nat)
    (first second : Receipt code)
    (present : (first, second) ∈ evidence code (run code interface policy initial events receiver incoming count)) :
    verify code interface policy initial events first.wire = true ∧
      verify code interface policy initial events second.wire = true ∧
      first.wire.occurrence ≠ second.wire.occurrence ∧ Conflicts code first.wire second.wire := by
  obtain ⟨one, two, conflict⟩ := (evidence_iff code _ first second).mp present
  have auth₁ := (receipts_authenticated code interface policy initial events receiver incoming count first one).1
  have auth₂ := (receipts_authenticated code interface policy initial events receiver incoming count second two).1
  refine ⟨auth₁, auth₂, ?_, conflict⟩
  intro same
  have equal := same_symbol_same_message code interface policy initial events first.wire second.wire auth₁ auth₂ same
  exact conflict.2.2 (congrArg EnvelopeData.payload equal)

theorem different_phases_do_not_conflict (first second : Envelope code)
    (different : first.scope.phase ≠ second.scope.phase) : ¬ Conflicts code first second := by
  intro conflict
  exact different (congrArg Scope.phase conflict.2.1)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication
