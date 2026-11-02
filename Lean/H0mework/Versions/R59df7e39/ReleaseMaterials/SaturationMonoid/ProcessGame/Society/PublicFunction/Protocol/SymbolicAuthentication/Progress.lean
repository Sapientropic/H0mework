import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.Timing

/-! A finite communication condition generates receipts and a quorum readout.
The condition is computed from actual deliveries and the original receive
guards, before consulting the receiver's duplicate ledger. It is not an
assumed certificate or a fairness axiom. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.Progress

open Distributed Institutions.Capitalism.Universal.Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (code : Code Party Good Port Technology Instrument)
  (interface : Interface code) (policy : code.Policy)
  (initial : RawCurrent Party Good Technology Instrument)

/-- Reference transport reconstructs the body of an actually addressed packet.
It neither schedules delivery nor supplies a candidate certificate. -/
def transported (events : List (Event Party Good Port Technology Instrument code.sites))
    (receiver : Fin code.sites) (n : Nat) : Option (Envelope code) :=
  match events[n]? with
  | some (.deliver serial) =>
      ((List.range n).filterMap (issuedAt code interface policy initial events)).find?
        (fun wire => decide (wire.serial = serial ∧ wire.recipient = receiver))
  | _ => none

theorem transported_has_actual_origin
    (events : List (Event Party Good Port Technology Instrument code.sites))
    (receiver : Fin code.sites) (n : Nat) (wire : Envelope code)
    (generated : transported code interface policy initial events receiver n = some wire) :
    ∃ emission < n, issuedAt code interface policy initial events emission = some wire ∧
      deliveredAt code events n wire.serial = true ∧ wire.recipient = receiver := by
  unfold transported at generated
  split at generated <;> try contradiction
  rename_i serial actual
  obtain ⟨emission, bounded, issued⟩ := List.mem_filterMap.mp (List.mem_of_find?_eq_some generated)
  have address := of_decide_eq_true (List.find?_some
    (p := fun message : Envelope code => decide (message.serial = serial ∧ message.recipient = receiver)) generated)
  refine ⟨emission, List.mem_range.mp bounded, issued, ?_, address.2⟩
  simp [deliveredAt, actual, address.1]

def usableAt (events : List (Event Party Good Port Technology Instrument code.sites))
    (receiver : Fin code.sites) (incoming : Nat → Option (Envelope code)) (n : Nat) : Option (Envelope code) :=
  match incoming n with
  | none => none
  | some wire =>
      if check code interface policy initial events receiver n [] wire = .accepted wire then some wire else none

def readyKeys (events : List (Event Party Good Port Technology Instrument code.sites))
    (receiver : Fin code.sites) (incoming : Nat → Option (Envelope code))
    (count : Nat) (scope : Scope) (value : Fin code.signals) : Finset (Fin code.sites) :=
  (Finset.range count).biUnion fun n =>
    match usableAt code interface policy initial events receiver incoming n with
    | none => ∅
    | some wire => if wire.scope = scope ∧ wire.payload = value then {wire.key} else ∅

theorem receive_preserves_receipts
    (events : List (Event Party Good Port Technology Instrument code.sites))
    (receiver : Fin code.sites) (n : Nat) (input : Option (Envelope code))
    (state : ReceiverState code) :
    state.receipts ⊆ (receive code interface policy initial events receiver n input state).receipts := by
  intro receipt present
  simp only [receive]
  split
  · exact List.mem_append_left _ present
  · exact present

theorem run_preserves_receipts
    (events : List (Event Party Good Port Technology Instrument code.sites))
    (receiver : Fin code.sites) (incoming : Nat → Option (Envelope code))
    (before after : Nat) (ordered : before ≤ after) :
    (run code interface policy initial events receiver incoming before).receipts ⊆
      (run code interface policy initial events receiver incoming after).receipts := by
  induction after with
  | zero => simpa only [Nat.le_zero.mp ordered] using (List.Subset.refl _)
  | succ after ih =>
    by_cases same : before = after + 1
    · subst before; exact List.Subset.refl _
    · exact List.Subset.trans (ih (by omega))
        (receive_preserves_receipts code interface policy initial events receiver after (incoming after) _)

theorem usable_delivery_generates_or_reuses_one_receipt
    (events : List (Event Party Good Port Technology Instrument code.sites))
    (receiver : Fin code.sites) (incoming : Nat → Option (Envelope code))
    (n : Nat) (wire : Envelope code)
    (usable : usableAt code interface policy initial events receiver incoming n = some wire) :
    ∃ receipt ∈ (run code interface policy initial events receiver incoming (n + 1)).receipts,
      receipt.wire = wire := by
  cases input : incoming n with
  | none => simp [usableAt, input] at usable
  | some submitted =>
    simp only [usableAt, input] at usable
    split_ifs at usable with ready
    · have same := Option.some.inj usable
      subst submitted
      obtain ⟨_, delivered, earlier, auth, recipient, scope, paid, _⟩ :=
        check_sound code interface policy initial events receiver n [] wire wire ready
      by_cases used : wire.occurrence ∈
          ((run code interface policy initial events receiver incoming n).receipts.map
            fun receipt => receipt.wire.occurrence)
      · obtain ⟨old, present, symbol⟩ := List.mem_map.mp used
        have oldAuth := (receipts_authenticated code interface policy initial events receiver incoming n old present).1
        exact ⟨old, receive_preserves_receipts code interface policy initial events receiver n (incoming n) _ present,
          same_symbol_same_message code interface policy initial events old.wire wire oldAuth auth symbol⟩
      · have accepted : check code interface policy initial events receiver n
            ((run code interface policy initial events receiver incoming n).receipts.map
              fun receipt => receipt.wire.occurrence) wire = .accepted wire := by
          simp [check, delivered, earlier, auth, recipient, scope, used]
          exact paid
        refine ⟨⟨wire, n⟩, ?_, rfl⟩
        simp only [run, receive, input, accepted]
        exact List.mem_append_right _ (by simp)

theorem ready_keys_have_actual_receipts
    (events : List (Event Party Good Port Technology Instrument code.sites))
    (receiver : Fin code.sites) (incoming : Nat → Option (Envelope code))
    (count : Nat) (scope : Scope) (value : Fin code.signals) :
    readyKeys code interface policy initial events receiver incoming count scope value ⊆
      Quorum.support code (run code interface policy initial events receiver incoming count) scope value := by
  intro key present
  obtain ⟨n, bounded, present⟩ := Finset.mem_biUnion.mp present
  have before : n < count := Finset.mem_range.mp bounded
  cases usable : usableAt code interface policy initial events receiver incoming n with
  | none => simp only [usable] at present; simp at present
  | some wire =>
    simp only [usable] at present
    split_ifs at present with matching
    · have keySame := Finset.mem_singleton.mp present
      obtain ⟨receipt, member, same⟩ := usable_delivery_generates_or_reuses_one_receipt code interface policy initial
        events receiver incoming n wire usable
      apply (Quorum.mem_support_iff code _ scope value key).mpr
      refine ⟨receipt, run_preserves_receipts code interface policy initial events receiver incoming
        (n + 1) count (by omega) member, ?_⟩
      rw [same]
      exact ⟨matching.1, matching.2, keySame.symm⟩
    · simp at present

/-- Bounded completion under a finite, executable communication condition.
The successful value is generated by the existing readout, not an input. -/
theorem finite_delivery_condition_generates_a_decision
    (events : List (Event Party Good Port Technology Instrument code.sites))
    (receiver : Fin code.sites) (incoming : Nat → Option (Envelope code))
    (count threshold : Nat) (scope : Scope) (value : Fin code.signals)
    (positive : 0 < threshold)
    (communication : threshold ≤ (readyKeys code interface policy initial events receiver incoming count scope value).card) :
    ∃ generated : Fin code.signals,
      Quorum.readout code (run code interface policy initial events receiver incoming count) scope threshold =
        .decided generated := by
  have enough := le_trans communication (Finset.card_le_card
    (ready_keys_have_actual_receipts code interface policy initial events receiver incoming count scope value))
  unfold Quorum.readout
  rw [if_neg (by omega : threshold ≠ 0)]
  cases found : (List.finRange code.signals).find?
      (fun candidate => decide (threshold ≤ (Quorum.support code
        (run code interface policy initial events receiver incoming count) scope candidate).card)) with
  | some generated => exact ⟨generated, rfl⟩
  | none =>
    have absent := List.find?_eq_none.mp found value (by simp)
    simp only [decide_eq_true_eq, not_le] at absent
    omega

theorem decided_value_has_an_actual_observation
    (events : List (Event Party Good Port Technology Instrument code.sites))
    (receiver : Fin code.sites) (incoming : Nat → Option (Envelope code))
    (count threshold : Nat) (scope : Scope) (value : Fin code.signals)
    (decided : Quorum.readout code (run code interface policy initial events receiver incoming count)
      scope threshold = .decided value) :
    ∃ receipt ∈ (run code interface policy initial events receiver incoming count).receipts,
      receipt.wire.scope = scope ∧ receipt.wire.payload = value ∧
      events[receipt.wire.occurrence]? = some (.send receipt.wire.key receiver) ∧
      receipt.wire.actor = code.siteParty receipt.wire.key ∧
      value = code.readLocal receipt.wire.key
        (code.snapshot receipt.wire.key (code.rawAt initial
          (frameAt code policy initial events receipt.wire.occurrence))) := by
  obtain ⟨positive, enough⟩ := Quorum.decided_has_quorum code _ scope threshold value decided
  have nonempty := Finset.card_pos.mp (lt_of_lt_of_le positive enough)
  obtain ⟨key, member⟩ := nonempty
  obtain ⟨receipt, present, slot, payload, _⟩ := (Quorum.mem_support_iff code _ scope value key).mp member
  obtain ⟨auth, recipient, _⟩ := receipts_authenticated code interface policy initial events receiver incoming count receipt present
  obtain ⟨actual, body, _, actor, _⟩ := authenticated_origin code interface policy initial events receipt.wire auth
  refine ⟨receipt, present, slot, payload, ?_, actor, ?_⟩
  · simpa only [recipient] using actual
  · rw [← payload, body]
    rfl

/-- Agreement, origin validity and bounded completion share one actual source.
The communication and budget conditions are computed from its finite history. -/
theorem finite_source_protocol_result
    (ports : Fin code.sites → Port)
    (events : List (Event Party Good Port Technology Instrument code.sites))
    (receiver : Fin code.sites) (incoming : Nat → Option (Envelope code))
    (count threshold : Nat) (scope : Scope) (proposed : Fin code.signals)
    (positive : 0 < threshold)
    (communication : threshold ≤ (readyKeys code interface policy initial events receiver incoming count scope proposed).card)
    (budget : code.sites + SourceExposure.budget code ports policy initial events count < threshold + threshold) :
    ∃ generated : Fin code.signals,
      Quorum.readout code (run code interface policy initial events receiver incoming count) scope threshold = .decided generated ∧
      (∀ (otherSite : Fin code.sites) (otherInput : Nat → Option (Envelope code))
          (otherCount : Nat) (otherValue : Fin code.signals), otherCount ≤ count →
        Quorum.readout code (run code interface policy initial events otherSite otherInput otherCount)
          scope threshold = .decided otherValue → generated = otherValue) ∧
      (∃ receipt ∈ (run code interface policy initial events receiver incoming count).receipts,
        receipt.wire.scope = scope ∧ receipt.wire.payload = generated ∧
        events[receipt.wire.occurrence]? = some (.send receipt.wire.key receiver) ∧
        receipt.wire.actor = code.siteParty receipt.wire.key ∧
        generated = code.readLocal receipt.wire.key
          (code.snapshot receipt.wire.key (code.rawAt initial
            (frameAt code policy initial events receipt.wire.occurrence)))) := by
  obtain ⟨generated, decided⟩ := finite_delivery_condition_generates_a_decision code interface policy initial
    events receiver incoming count threshold scope proposed positive communication
  refine ⟨generated, decided, ?_,
    decided_value_has_an_actual_observation code interface policy initial events receiver incoming count threshold scope generated decided⟩
  intro otherSite otherInput otherCount otherValue bounded otherDecided
  exact Timing.agreement_across_actual_cuts code interface policy initial ports events receiver otherSite incoming otherInput
    count otherCount count threshold scope generated otherValue (le_refl _) bounded decided otherDecided budget

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.Progress
