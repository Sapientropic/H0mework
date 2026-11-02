import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReceiptFold

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.QueueScheduler

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (code : Code Party Good Port (Mandate.State Party Technology) Instrument)

def address : Event Party Good Port (Mandate.State Party Technology) Instrument code.sites → Option Nat
  | .deliver serial => some serial
  | _ => none

def admitted : Finset Nat := (code.eventAlphabet.filterMap (address code)).toFinset

def attempted (baseline : Nat) (past : Events code) : Finset Nat :=
  ((past.drop baseline).filterMap (address code)).toFinset

def untried (baseline : Nat) (past : Events code) : Finset Nat :=
  admitted code \ attempted code baseline past

def eligible (baseline : Nat) (past : Events code) (frame : code.Frame)
    (event : Choice code) : Bool :=
  match event.val with
  | .deliver serial => decide (serial < frame.sent.length ∧ serial ∉ attempted code baseline past)
  | _ => false

/-- The public finite event interface supplies the move; the actual queue and
post-installation event memory supply availability and freshness. -/
def opponent (baseline : Nat) : Opponent code := fun _ past frame =>
  code.eventAlphabet.attach.find? (eligible code baseline past frame)

omit [DecidableEq Port] [DecidableEq Technology] in
theorem generated_move_has_actual_queue_and_fresh_address
    (baseline : Nat) (history : History) (past : Events code) (frame : code.Frame)
    (event : Choice code) (chosen : opponent code baseline history past frame = some event) :
    ∃ serial, event.val = .deliver serial ∧ serial < frame.sent.length ∧
      serial ∈ untried code baseline past := by
  have allowed := List.find?_some chosen
  rcases event with ⟨event, supported⟩
  cases event <;> simp only [eligible, Bool.false_eq_true] at allowed
  rename_i serial
  obtain ⟨present, fresh⟩ := of_decide_eq_true allowed
  refine ⟨serial, rfl, present, Finset.mem_sdiff.mpr ⟨?_, fresh⟩⟩
  exact List.mem_toFinset.mpr (List.mem_filterMap.mpr ⟨.deliver serial, supported, rfl⟩)

omit [DecidableEq Port] [DecidableEq Technology] in
theorem a_pending_admitted_packet_generates_a_move
    (baseline : Nat) (history : History) (past : Events code) (frame : code.Frame)
    (serial : Nat) (present : serial < frame.sent.length)
    (pending : serial ∈ untried code baseline past) :
    ∃ event, opponent code baseline history past frame = some event := by
  have accepted := Finset.mem_sdiff.mp pending
  obtain ⟨event, supported, encoded⟩ := List.mem_filterMap.mp (List.mem_toFinset.mp accepted.1)
  have kind : event = .deliver serial := by cases event <;> simp_all [address]
  subst event
  cases chosen : opponent code baseline history past frame with
  | some event => exact ⟨event, rfl⟩
  | none =>
    have missing := List.find?_eq_none.mp chosen ⟨.deliver serial, supported⟩ (List.mem_attach _ _)
    simp only [eligible, decide_eq_true_eq, not_and] at missing
    exact False.elim (missing present accepted.2)

omit [DecidableEq Port] [DecidableEq Technology] in
theorem delivered_address_strictly_decreases_the_source_rank
    (baseline : Nat) (past : Events code) (bounded : baseline ≤ past.length)
    (serial : Nat) (pending : serial ∈ untried code baseline past) :
    (untried code baseline (past ++ [.deliver serial])).card <
      (untried code baseline past).card := by
  have next : untried code baseline (past ++ [.deliver serial]) =
      (untried code baseline past).erase serial := by
    ext key
    simp [untried, attempted, List.drop_append_of_le_length bounded, address]
    tauto
  rw [next]
  exact Finset.card_erase_lt_of_mem pending

omit [DecidableEq Port] [DecidableEq Technology] in
theorem untried_append_subset (baseline : Nat) (past more : Events code)
    (bounded : baseline ≤ past.length) :
    untried code baseline (past ++ more) ⊆ untried code baseline past := by
  intro key inside
  simp only [untried, attempted, List.drop_append_of_le_length bounded,
    List.filterMap_append, List.toFinset_append, Finset.mem_sdiff, Finset.mem_union,
    not_or] at inside ⊢
  exact ⟨inside.1, inside.2.1⟩

omit [DecidableEq Port] [DecidableEq Technology] in
theorem advance_preserves_memory_and_queue (policy : Option code.Policy)
    (input : Input code) (current : State code) :
    current.past <+: (advance code policy input current).past ∧
      current.frame.sent <+: (advance code policy input current).frame.sent := by
  cases policy <;> cases chosen : decision code input current <;>
    simp only [advance, chosen] <;> constructor <;>
    first | exact List.prefix_refl _ | exact List.prefix_append _ _

variable (source : Machine Party Good Port (Mandate.State Party Technology) Instrument)
  (input : Input source.code) (cut : Nat)
  (protocol : Distributed.Recall.Information.Agency.Protocol.Rule source.code)

abbrev environment := opponent source.code (source.feedbackState input cut).past.length
abbrev state (n : Nat) := AttestationTransport.state source input cut protocol
  (environment source input cut) n
abbrev move (n : Nat) := AttestationTransport.move source input cut protocol
  (environment source input cut) n
abbrev baseline := (source.feedbackState input cut).past.length
abbrev rank (n : Nat) := (untried source.code (baseline source input cut)
  (state source input cut protocol n).past).card

theorem actual_step (n : Nat) :
    state source input cut protocol (n + 1) = advance source.code
      ((OwnedAttestation.actual source input cut protocol (environment source input cut)).feedbackPolicy (cut + n))
      (AttestationTransport.actualInput source input cut protocol (environment source input cut))
      (state source input cut protocol n) := rfl

theorem actual_active_step (n : Nat) (bounded : n < (source.feedbackState input cut).remaining) :
    state source input cut protocol (n + 1) = advance source.code (some protocol.work.val)
      (AttestationTransport.actualInput source input cut protocol (environment source input cut))
      (state source input cut protocol n) := by
  rw [actual_step, Execution.policy_at]
  congr 1
  simp only [Residual.scheduleAt, Distributed.Recall.Information.Agency.Protocol.term,
    List.getElem?_replicate, if_pos bounded, Option.getD_some]

theorem actual_memory_and_queue_extend (n : Nat) :
    (state source input cut protocol n).past <+: (state source input cut protocol (n + 1)).past ∧
      (state source input cut protocol n).frame.sent <+: (state source input cut protocol (n + 1)).frame.sent := by
  rw [actual_step]
  exact advance_preserves_memory_and_queue source.code _ _ _

theorem actual_installation_memory_is_preserved (n : Nat) :
    (source.feedbackState input cut).past <+: (state source input cut protocol n).past := by
  induction n with
  | zero =>
    change _ <+: ((Future.target source input cut _ _).feedbackState _ (cut + 0)).past
    rw [Future.the_whole_future_run_is_the_actual_state]
    exact List.prefix_refl _
  | succ n ih => exact ih.trans (actual_memory_and_queue_extend source input cut protocol n).1

theorem actual_untried_at_later_is_a_subset (n m : Nat) (later : n ≤ m) :
    untried source.code (baseline source input cut) (state source input cut protocol m).past ⊆
      untried source.code (baseline source input cut) (state source input cut protocol n).past := by
  induction m, later using Nat.le_induction with
  | base => exact Finset.Subset.refl _
  | succ m _ ih =>
    apply Finset.Subset.trans _ ih
    obtain ⟨more, same⟩ := (actual_memory_and_queue_extend source input cut protocol m).1
    rw [← same]
    exact untried_append_subset source.code _ _ _
      (actual_installation_memory_is_preserved source input cut protocol m).length_le

theorem actual_queue_length_never_decreases (n m : Nat) (later : n ≤ m) :
    (state source input cut protocol n).frame.sent.length ≤ (state source input cut protocol m).frame.sent.length := by
  induction m, later using Nat.le_induction with
  | base => exact Nat.le_refl _
  | succ m _ ih => exact le_trans ih (actual_memory_and_queue_extend source input cut protocol m).2.length_le

theorem actual_history_and_remaining (n : Nat) :
    (state source input cut protocol n).history.length = source.history.length + 1 + cut + n ∧
      (state source input cut protocol n).remaining = (source.feedbackState input cut).remaining - n := by
  rw [state, AttestationTransport.state, OwnedAttestation.localState,
    Distributed.Recall.Information.Agency.Protocol.state, Future.the_whole_future_run_is_the_actual_state]
  constructor
  · induction n with
    | zero =>
      change (source.feedbackState input cut).history.length = _
      induction cut with
      | zero => simp [Machine.feedbackState, Machine.feedbackInitial]
      | succ cut ih =>
        change (advance source.code _ _ _).history.length = _
        rw [history_keeps_every_actual_word, List.length_append, List.length_singleton, ih]
        omega
    | succ n ih =>
      rw [Residual.run, history_keeps_every_actual_word, List.length_append, List.length_singleton, ih]
      omega
  · exact Residual.remaining_is_the_seed_budget _ _ _ _ _

theorem actual_external_turn_uses_the_queue
    (n : Nat) (bounded : n < (source.feedbackState input cut).remaining)
    (external : Distributed.Recall.Information.Agency.ownerAt source.code
      (Distributed.Recall.Information.Agency.start source cut) (state source input cut protocol n).history.length = none) :
    move source input cut protocol n =
      environment source input cut (state source input cut protocol n).history
        (state source input cut protocol n).past (state source input cut protocol n).frame := by
  have facts := actual_history_and_remaining source input cut protocol n
  have active : (state source input cut protocol n).remaining ≠ 0 := by omega
  unfold move AttestationTransport.move
  simp only [decision, if_neg active]
  change (if _ then _ else _) = _
  rw [if_neg (by rw [facts.1]; omega)]
  simp only [Distributed.Recall.Information.Agency.Protocol.controller,
    Distributed.Recall.Information.Agency.Protocol.driver, external]
  cases chosen : environment source input cut (state source input cut protocol n).history
      (state source input cut protocol n).past (state source input cut protocol n).frame with
  | none => rfl
  | some event =>
    obtain ⟨serial, kind, _, _⟩ := generated_move_has_actual_queue_and_fresh_address source.code
      _ _ _ _ event chosen
    simp only [Distributed.Recall.Information.Agency.externalChoice, kind]

theorem pending_packet_on_an_actual_external_turn_decreases_rank
    (n serial : Nat) (bounded : n < (source.feedbackState input cut).remaining)
    (external : Distributed.Recall.Information.Agency.ownerAt source.code
      (Distributed.Recall.Information.Agency.start source cut) (state source input cut protocol n).history.length = none)
    (present : serial < (state source input cut protocol n).frame.sent.length)
    (pending : serial ∈ untried source.code (baseline source input cut) (state source input cut protocol n).past) :
    ∃ delivered, AttestationReception.deliveredAt source input cut protocol (environment source input cut) n delivered = true ∧
      rank source input cut protocol (n + 1) < rank source input cut protocol n := by
  obtain ⟨event, chosen⟩ := a_pending_admitted_packet_generates_a_move source.code _ _ _ _ serial present pending
  obtain ⟨delivered, kind, _, fresh⟩ := generated_move_has_actual_queue_and_fresh_address source.code _ _ _ _ event chosen
  have selected : move source input cut protocol n = some event :=
    (actual_external_turn_uses_the_queue source input cut protocol n bounded external).trans chosen
  refine ⟨delivered, ?_, ?_⟩
  · unfold AttestationReception.deliveredAt
    dsimp only [move] at selected
    rw [if_pos bounded, selected]
    dsimp only
    rw [kind]
    exact beq_self_eq_true delivered
  · unfold rank
    rw [actual_active_step source input cut protocol n bounded,
      event_memory_is_extended source.code protocol.work.val _ _ event selected, kind]
    exact delivered_address_strictly_decreases_the_source_rank source.code _ _
      (actual_installation_memory_is_preserved source input cut protocol n).length_le delivered fresh

theorem every_odd_cut_is_an_external_turn (n : Nat) :
    Distributed.Recall.Information.Agency.ownerAt source.code
      (Distributed.Recall.Information.Agency.start source cut) (state source input cut protocol (2 * n + 1)).history.length = none := by
  rw [(actual_history_and_remaining source input cut protocol _).1]
  simp [Distributed.Recall.Information.Agency.ownerAt, Distributed.Recall.Information.Agency.start,
    Nat.add_mod]

/-- A finite public interface bounds interference from later sends as well:
each admitted address can be attempted at most once after installation. -/
theorem every_existing_admitted_packet_is_attempted_in_a_finite_window
    (start serial : Nat)
    (enough : 2 * (start + (admitted source.code).card) ≤ (source.feedbackState input cut).remaining)
    (present : serial < (state source input cut protocol (2 * start)).frame.sent.length)
    (supported : serial ∈ admitted source.code) :
    serial ∈ attempted source.code (baseline source input cut)
      (state source input cut protocol (2 * (start + (admitted source.code).card))).past := by
  by_contra missing
  let cap := (admitted source.code).card
  let stop := 2 * (start + cap)
  have pending : serial ∈ untried source.code (baseline source input cut)
      (state source input cut protocol stop).past := Finset.mem_sdiff.mpr ⟨supported, missing⟩
  have descent : ∀ k ≤ cap,
      rank source input cut protocol (2 * (start + k)) + k ≤ rank source input cut protocol (2 * start) := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro bounded
      have previous := ih (by omega)
      have earlier : 2 * (start + k) + 1 ≤ stop := by dsimp [stop]; omega
      have stillPending := actual_untried_at_later_is_a_subset source input cut protocol _ _ earlier pending
      have stillPresent := lt_of_lt_of_le present
        (actual_queue_length_never_decreases source input cut protocol _ (2 * (start + k) + 1) (by omega))
      obtain ⟨_, _, drops⟩ := pending_packet_on_an_actual_external_turn_decreases_rank source input cut protocol
        (2 * (start + k) + 1) serial (by dsimp [stop] at earlier; dsimp [cap] at bounded; omega)
        (every_odd_cut_is_an_external_turn source input cut protocol (start + k)) stillPresent stillPending
      have monotone := Finset.card_le_card (actual_untried_at_later_is_a_subset source input cut protocol
        (2 * (start + k)) (2 * (start + k) + 1) (by omega))
      change rank source input cut protocol (2 * (start + k) + 1) ≤
        rank source input cut protocol (2 * (start + k)) at monotone
      have next : 2 * (start + (k + 1)) = (2 * (start + k) + 1) + 1 := by omega
      rw [next]
      omega
  have counted := descent cap (Nat.le_refl _)
  have positive : 0 < rank source input cut protocol stop := Finset.card_pos.mpr ⟨serial, pending⟩
  have maximum : rank source input cut protocol (2 * start) ≤ cap :=
    Finset.card_le_card Finset.sdiff_subset
  change rank source input cut protocol stop + cap ≤ _ at counted
  omega

theorem attempted_memory_is_the_actual_delivery_history
    (count serial : Nat) (bounded : count ≤ (source.feedbackState input cut).remaining) :
    serial ∈ attempted source.code (baseline source input cut) (state source input cut protocol count).past ↔
      ∃ n < count, AttestationReception.deliveredAt source input cut protocol (environment source input cut) n serial = true := by
  induction count with
  | zero =>
    change serial ∈ attempted source.code _ ((Future.target source input cut _ _).feedbackState _ (cut + 0)).past ↔ _
    rw [Future.the_whole_future_run_is_the_actual_state]
    simp [attempted, baseline, Residual.seed, Residual.run]
  | succ count ih =>
    have before : count < (source.feedbackState input cut).remaining := by omega
    have originBound := (actual_installation_memory_is_preserved source input cut protocol count).length_le
    have next : serial ∈ attempted source.code (baseline source input cut) (state source input cut protocol (count + 1)).past ↔
        serial ∈ attempted source.code (baseline source input cut) (state source input cut protocol count).past ∨
          AttestationReception.deliveredAt source input cut protocol (environment source input cut) count serial = true := by
      rw [actual_active_step source input cut protocol count before]
      simp only [AttestationReception.deliveredAt, if_pos before, AttestationTransport.move]
      cases chosen : decision source.code (AttestationTransport.actualInput source input cut protocol (environment source input cut))
          (state source input cut protocol count) with
      | none => simp only [advance, chosen, Bool.false_eq_true, or_false]
      | some event =>
        rw [event_memory_is_extended source.code protocol.work.val _ _ event chosen]
        rcases event with ⟨event, supported⟩
        cases event <;> simp [attempted, List.drop_append_of_le_length originBound, address]
        constructor
        · rintro (same | previous)
          · exact Or.inr same.symm
          · exact Or.inl previous
        · rintro (previous | same)
          · exact Or.inr previous
          · exact Or.inl same.symm
    rw [next, ih (by omega)]
    constructor
    · rintro (⟨n, earlier, delivered⟩ | delivered)
      · exact ⟨n, by omega, delivered⟩
      · exact ⟨count, Nat.lt_succ_self _, delivered⟩
    · rintro ⟨n, earlier, delivered⟩
      by_cases same : n = count
      · exact Or.inr (same ▸ delivered)
      · exact Or.inl ⟨n, by omega, delivered⟩

theorem finite_window_generates_an_actual_delivery_attempt
    (start serial : Nat)
    (enough : 2 * (start + (admitted source.code).card) ≤ (source.feedbackState input cut).remaining)
    (present : serial < (state source input cut protocol (2 * start)).frame.sent.length)
    (supported : serial ∈ admitted source.code) :
    ∃ n < 2 * (start + (admitted source.code).card),
      AttestationReception.deliveredAt source input cut protocol (environment source input cut) n serial = true :=
  (attempted_memory_is_the_actual_delivery_history source input cut protocol _ serial enough).mp
    (every_existing_admitted_packet_is_attempted_in_a_finite_window source input cut protocol start serial enough present supported)

theorem a_pending_packet_is_attempted_during_its_source_window
    (start serial : Nat)
    (enough : 2 * ((start + 1) / 2 + (admitted source.code).card) ≤ (source.feedbackState input cut).remaining)
    (present : serial < (state source input cut protocol start).frame.sent.length)
    (supported : serial ∈ admitted source.code)
    (fresh : serial ∉ attempted source.code (baseline source input cut) (state source input cut protocol start).past) :
    ∃ n, start ≤ n ∧ n < 2 * ((start + 1) / 2 + (admitted source.code).card) ∧
      AttestationReception.deliveredAt source input cut protocol (environment source input cut) n serial = true := by
  have aligned : start ≤ 2 * ((start + 1) / 2) := by omega
  have later := lt_of_lt_of_le present (actual_queue_length_never_decreases source input cut protocol _ _ aligned)
  obtain ⟨n, bounded, delivered⟩ := finite_window_generates_an_actual_delivery_attempt source input cut protocol
    ((start + 1) / 2) serial enough later supported
  refine ⟨n, ?_, bounded, delivered⟩
  by_contra earlier
  exact fresh ((attempted_memory_is_the_actual_delivery_history source input cut protocol start serial (by omega)).mpr
    ⟨n, by omega, delivered⟩)

theorem source_window_submits_the_original_delivery_cost
    (empty : source.continuation = []) (start serial : Nat)
    (enough : 2 * ((start + 1) / 2 + (admitted source.code).card) ≤ (source.feedbackState input cut).remaining)
    (present : serial < (state source input cut protocol start).frame.sent.length)
    (supported : serial ∈ admitted source.code)
    (fresh : serial ∉ attempted source.code (baseline source input cut) (state source input cut protocol start).past) :
    ∃ n packet, start ≤ n ∧ n < 2 * ((start + 1) / 2 + (admitted source.code).card) ∧
      AttestationReception.deliveredAt source input cut protocol (environment source input cut) n serial = true ∧
      (state source input cut protocol n).frame.sent[serial]? = some packet ∧
      (AttestationTransport.execution source input cut protocol (environment source input cut) n).submitted =
        source.code.deliveryCost packet.recipient := by
  obtain ⟨n, later, bounded, delivered⟩ := a_pending_packet_is_attempted_during_its_source_window
    source input cut protocol start serial enough present supported fresh
  have queued := lt_of_lt_of_le present (actual_queue_length_never_decreases source input cut protocol start n later)
  let packet := (state source input cut protocol n).frame.sent[serial]
  have actual : (state source input cut protocol n).frame.sent[serial]? = some packet := List.getElem?_eq_getElem queued
  exact ⟨n, packet, later, bounded, delivered, actual,
    AttestationReception.actual_delivery_submits_the_original_cost source input cut protocol
      (environment source input cut) empty n serial packet delivered actual⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.QueueScheduler
