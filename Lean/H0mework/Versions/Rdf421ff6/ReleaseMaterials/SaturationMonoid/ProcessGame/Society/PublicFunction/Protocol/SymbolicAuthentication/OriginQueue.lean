import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AdmissionRuntime

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.OriginQueue

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}

theorem execute_append (cursor : Cursor code) (first second : List (EventHistory.Stage (code := code))) :
    EventHistory.execute cursor (first ++ second) = EventHistory.execute (EventHistory.execute cursor first) second := by
  induction first generalizing cursor with
  | nil => rfl
  | cons stage tail ih => exact ih (cursor.after stage.1 stage.2)

theorem records_append (cursor : Cursor code) (first second : List (EventHistory.Stage (code := code))) :
    StageTrace.records cursor (first ++ second) =
      StageTrace.records cursor first ++ StageTrace.records (EventHistory.execute cursor first) second := by
  induction first generalizing cursor with
  | nil => rfl
  | cons stage tail ih => simp only [List.cons_append, StageTrace.records, EventHistory.execute, ih]

variable (origin cursor : Cursor code) (protocols : Nat → Rule code)

abbrev baseline := (EventStep.seed origin).past.length
abbrev environment := QueueScheduler.opponent code (baseline origin)

/-- The source origin owns the attempt baseline across continuation boundaries. -/
def cursorAt : Nat → Cursor code
  | 0 => cursor
  | n + 1 => (cursorAt n).after (protocols n) (environment origin)

def stages : Nat → List (EventHistory.Stage (code := code))
  | 0 => []
  | n + 1 => stages n ++ [(protocols n, environment origin)]

abbrev state (n : Nat) := EventStep.seed (cursorAt origin cursor protocols n)
abbrev row (n : Nat) := StageTrace.material (cursorAt origin cursor protocols n) (protocols n) (environment origin)
abbrev rank (n : Nat) := (QueueScheduler.untried code (baseline origin) (state origin cursor protocols n).past).card
abbrev warmup := cursor.ownerStart - (EventStep.seed cursor).history.length
abbrev initialRank := (QueueScheduler.untried code (baseline origin) (EventStep.seed cursor).past).card
abbrev horizon := warmup cursor + 2 * initialRank origin cursor

theorem stage_count (count : Nat) : (stages origin protocols count).length = count := by
  induction count with
  | zero => rfl
  | succ count ih => simp only [stages, List.length_append, List.length_singleton, ih]

theorem executed_stages_are_the_actual_cursor (count : Nat) :
    EventHistory.execute cursor (stages origin protocols count) = cursorAt origin cursor protocols count := by
  induction count with
  | zero => rfl
  | succ count ih => rw [stages, execute_append, ih]; rfl

theorem records_succ (count : Nat) :
    StageTrace.records cursor (stages origin protocols (count + 1)) =
      StageTrace.records cursor (stages origin protocols count) ++ [row origin cursor protocols count] := by
  rw [stages, records_append, executed_stages_are_the_actual_cursor]
  rfl

theorem row_at_its_actual_index (count index : Nat) (bounded : index < count) :
    (StageTrace.records cursor (stages origin protocols count))[index]? = some (row origin cursor protocols index) := by
  induction count with
  | zero => omega
  | succ count ih =>
    rw [records_succ, List.getElem?_append, StageTrace.record_count, stage_count]
    split
    · exact ih (by omega)
    · have same : index = count := by omega
      subst index
      simp

theorem clocks_and_roster (count : Nat) :
    (state origin cursor protocols count).history.length = (EventStep.seed cursor).history.length + count ∧
      (state origin cursor protocols count).remaining = (EventStep.seed cursor).remaining - count ∧
      (cursorAt origin cursor protocols count).ownerStart = cursor.ownerStart := by
  induction count with
  | zero => exact ⟨rfl, rfl, rfl⟩
  | succ count ih =>
    have next := EventStep.actual_next_state (cursorAt origin cursor protocols count) (protocols count) (environment origin)
    refine ⟨?_, ?_, ih.2.2⟩
    · change (EventStep.seed ((cursorAt origin cursor protocols count).after _ _)).history.length = _
      rw [next]
      change ((state origin cursor protocols count).history ++ [_]).length = _
      simp only [List.length_append, List.length_singleton, ih.1]
      omega
    · change (EventStep.seed ((cursorAt origin cursor protocols count).after _ _)).remaining = _
      rw [next]
      change (state origin cursor protocols count).remaining - 1 = _
      rw [ih.2.1]
      omega

theorem memory_and_queue_extend_one_step (count : Nat) :
    (state origin cursor protocols count).past <+: (state origin cursor protocols (count + 1)).past ∧
      (state origin cursor protocols count).frame.sent <+: (state origin cursor protocols (count + 1)).frame.sent := by
  simpa only [state, cursorAt, EventStep.actual_next_state] using
    QueueScheduler.advance_preserves_memory_and_queue code (some (protocols count).work.val)
      (EventStep.applied (cursorAt origin cursor protocols count) (protocols count) (environment origin))
      (state origin cursor protocols count)

theorem memory_and_queue_extend (first last : Nat) (later : first ≤ last) :
    (state origin cursor protocols first).past <+: (state origin cursor protocols last).past ∧
      (state origin cursor protocols first).frame.sent <+: (state origin cursor protocols last).frame.sent := by
  induction last, later using Nat.le_induction with
  | base => exact ⟨List.prefix_refl _, List.prefix_refl _⟩
  | succ last _ ih =>
    have next := memory_and_queue_extend_one_step origin cursor protocols last
    exact ⟨ih.1.trans next.1, ih.2.trans next.2⟩

variable (fits : baseline origin ≤ (EventStep.seed cursor).past.length)

include fits in
theorem later_untried_is_a_subset (first last : Nat) (later : first ≤ last) :
    QueueScheduler.untried code (baseline origin) (state origin cursor protocols last).past ⊆
      QueueScheduler.untried code (baseline origin) (state origin cursor protocols first).past := by
  obtain ⟨more, same⟩ := (memory_and_queue_extend origin cursor protocols first last later).1
  rw [← same]
  exact QueueScheduler.untried_append_subset code _ _ _
    (fits.trans (memory_and_queue_extend origin cursor protocols 0 first (Nat.zero_le _)).1.length_le)

theorem an_external_turn_occurs_in_each_pair (count : Nat) (started : warmup cursor ≤ count) :
    ∃ offset < 2, Distributed.Recall.Information.Agency.ownerAt code
      (cursorAt origin cursor protocols (count + offset)).ownerStart (state origin cursor protocols (count + offset)).history.length = none := by
  have reached : cursor.ownerStart ≤ (EventStep.seed cursor).history.length + count := by
    dsimp only [warmup] at started
    omega
  by_cases positive : 0 < code.sites
  · by_cases even : ((EventStep.seed cursor).history.length + count - cursor.ownerStart) % 2 = 0
    · refine ⟨1, by omega, ?_⟩
      rw [(clocks_and_roster origin cursor protocols _).1, (clocks_and_roster origin cursor protocols _).2.2]
      simp only [Distributed.Recall.Information.Agency.ownerAt, dif_pos positive]
      rw [if_neg (by omega)]
    · refine ⟨0, by omega, ?_⟩
      rw [(clocks_and_roster origin cursor protocols _).1, (clocks_and_roster origin cursor protocols _).2.2]
      simp only [Nat.add_zero, Distributed.Recall.Information.Agency.ownerAt, dif_pos positive, if_neg even]
  · exact ⟨0, by omega, by simp only [Distributed.Recall.Information.Agency.ownerAt, dif_neg positive]⟩

include fits in
theorem an_external_pending_packet_decreases_the_actual_rank
    (count serial : Nat) (active : count < (EventStep.seed cursor).remaining)
    (external : Distributed.Recall.Information.Agency.ownerAt code (cursorAt origin cursor protocols count).ownerStart
      (state origin cursor protocols count).history.length = none)
    (present : serial < (state origin cursor protocols count).frame.sent.length)
    (pending : serial ∈ QueueScheduler.untried code (baseline origin) (state origin cursor protocols count).past) :
    ∃ delivered, StageReception.delivered (row origin cursor protocols count) delivered = true ∧
      rank origin cursor protocols (count + 1) < rank origin cursor protocols count := by
  obtain ⟨event, chosen⟩ := QueueScheduler.a_pending_admitted_packet_generates_a_move code
    (baseline origin) (state origin cursor protocols count).history (state origin cursor protocols count).past
      (state origin cursor protocols count).frame serial present pending
  obtain ⟨delivered, kind, _, fresh⟩ := QueueScheduler.generated_move_has_actual_queue_and_fresh_address code
    (baseline origin) _ _ _ event chosen
  have live : (state origin cursor protocols count).remaining ≠ 0 := by
    rw [(clocks_and_roster origin cursor protocols count).2.1]
    omega
  have selected : decision code (EventStep.applied (cursorAt origin cursor protocols count) (protocols count) (environment origin))
      (state origin cursor protocols count) = some event := by
    simp only [decision, if_neg live, Cursor.controller, driver, external]
    unfold environment
    rw [chosen]
    simp only [Distributed.Recall.Information.Agency.externalChoice, kind]
  have admitted : StageTransport.admission (row origin cursor protocols count) = some event := by
    change ControlExecution.admitted code (StageTrace.capture _ _ _ _) = _
    rw [StageTrace.captured_admission_is_the_actual_decision]
    exact selected
  refine ⟨delivered, ?_, ?_⟩
  · simp only [StageReception.delivered, admitted, kind, beq_self_eq_true]
  · unfold rank
    change (QueueScheduler.untried code (baseline origin) (EventStep.seed ((cursorAt origin cursor protocols count).after _ _)).past).card < _
    rw [EventStep.actual_next_state, event_memory_is_extended code _ _ _ event selected, kind]
    exact QueueScheduler.delivered_address_strictly_decreases_the_source_rank code _ _
      (fits.trans (memory_and_queue_extend origin cursor protocols 0 count (Nat.zero_le _)).1.length_le) delivered fresh

include fits in
theorem attempted_memory_is_the_actual_stage_delivery_history (count serial : Nat) :
    serial ∈ QueueScheduler.attempted code (baseline origin) (state origin cursor protocols count).past ↔
      serial ∈ QueueScheduler.attempted code (baseline origin) (EventStep.seed cursor).past ∨
        ∃ index < count, StageReception.delivered (row origin cursor protocols index) serial = true := by
  induction count with
  | zero => simp [state, cursorAt]
  | succ count ih =>
    have bounded := fits.trans (memory_and_queue_extend origin cursor protocols 0 count (Nat.zero_le _)).1.length_le
    change baseline origin ≤ (state origin cursor protocols count).past.length at bounded
    have admitted : StageTransport.admission (row origin cursor protocols count) =
        decision code (EventStep.applied (cursorAt origin cursor protocols count) (protocols count) (environment origin)) (state origin cursor protocols count) :=
      StageTrace.captured_admission_is_the_actual_decision _ _ _ _
    have next : serial ∈ QueueScheduler.attempted code (baseline origin) (state origin cursor protocols (count + 1)).past ↔
        serial ∈ QueueScheduler.attempted code (baseline origin) (state origin cursor protocols count).past ∨
          StageReception.delivered (row origin cursor protocols count) serial = true := by
      change serial ∈ QueueScheduler.attempted code _ (EventStep.seed ((cursorAt origin cursor protocols count).after _ _)).past ↔ _
      rw [EventStep.actual_next_state]
      simp only [StageReception.delivered, admitted]
      cases selected : decision code (EventStep.applied (cursorAt origin cursor protocols count) (protocols count) (environment origin))
          (state origin cursor protocols count) with
      | none => simp only [Reaction.Feedback.advance, selected, Bool.false_eq_true, or_false]
      | some event =>
        rw [event_memory_is_extended code _ _ _ event selected]
        rcases event with ⟨event, supported⟩
        cases event <;> simp [QueueScheduler.attempted, List.drop_append_of_le_length bounded, QueueScheduler.address]
        constructor
        · rintro (same | previous)
          · exact Or.inr same.symm
          · exact Or.inl previous
        · rintro (previous | same)
          · exact Or.inr previous
          · exact Or.inl same.symm
    rw [next, ih]
    constructor
    · rintro ((initial | ⟨index, before, delivered⟩) | delivered)
      · exact Or.inl initial
      · exact Or.inr ⟨index, by omega, delivered⟩
      · exact Or.inr ⟨count, by omega, delivered⟩
    · rintro (initial | ⟨index, before, delivered⟩)
      · exact Or.inl (Or.inl initial)
      · by_cases same : index = count
        · exact Or.inr (same ▸ delivered)
        · exact Or.inl (Or.inr ⟨index, by omega, delivered⟩)

include fits in
theorem the_source_window_generates_an_actual_delivery_attempt
    (serial : Nat) (enough : horizon origin cursor ≤ (EventStep.seed cursor).remaining)
    (present : serial < (EventStep.seed cursor).frame.sent.length)
    (initial : serial ∈ QueueScheduler.untried code (baseline origin) (EventStep.seed cursor).past) :
    ∃ index < horizon origin cursor, StageReception.delivered (row origin cursor protocols index) serial = true := by
  by_contra missingDelivery
  have missing : serial ∉ QueueScheduler.attempted code (baseline origin) (state origin cursor protocols (horizon origin cursor)).past := by
    intro attempted
    rcases (attempted_memory_is_the_actual_stage_delivery_history origin cursor protocols fits _ serial).mp attempted with old | generated
    · exact (Finset.mem_sdiff.mp initial).2 old
    · exact missingDelivery generated
  let cap := initialRank origin cursor
  let stop := horizon origin cursor
  have pending : serial ∈ QueueScheduler.untried code (baseline origin) (state origin cursor protocols stop).past :=
    Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp initial).1, missing⟩
  have descent : ∀ k ≤ cap,
      rank origin cursor protocols (warmup cursor + 2 * k) + k ≤ rank origin cursor protocols (warmup cursor) := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro bounded
      have previous := ih (by omega)
      obtain ⟨offset, small, external⟩ := an_external_turn_occurs_in_each_pair origin cursor protocols
        (warmup cursor + 2 * k) (by omega)
      have earlier : warmup cursor + 2 * k + offset < stop := by dsimp only [stop, horizon]; dsimp only [cap] at bounded; omega
      have stillPending := later_untried_is_a_subset origin cursor protocols fits _ _ (Nat.le_of_lt earlier) pending
      have stillPresent := lt_of_lt_of_le present (memory_and_queue_extend origin cursor protocols 0
        (warmup cursor + 2 * k + offset) (Nat.zero_le _)).2.length_le
      obtain ⟨_, _, drops⟩ := an_external_pending_packet_decreases_the_actual_rank origin cursor protocols fits _ serial
        (by dsimp only [stop] at earlier; omega) external stillPresent stillPending
      have before := Finset.card_le_card (later_untried_is_a_subset origin cursor protocols fits
        (warmup cursor + 2 * k) (warmup cursor + 2 * k + offset) (by omega))
      have after := Finset.card_le_card (later_untried_is_a_subset origin cursor protocols fits
        (warmup cursor + 2 * k + offset + 1) (warmup cursor + 2 * (k + 1)) (by omega))
      change rank origin cursor protocols _ ≤ rank origin cursor protocols _ at before after
      omega
  have counted := descent cap (Nat.le_refl _)
  have positive : 0 < rank origin cursor protocols stop := Finset.card_pos.mpr ⟨serial, pending⟩
  have maximum : rank origin cursor protocols (warmup cursor) ≤ cap :=
    Finset.card_le_card (later_untried_is_a_subset origin cursor protocols fits 0 _ (Nat.zero_le _))
  change rank origin cursor protocols stop + cap ≤ _ at counted
  omega

theorem an_actual_prefix_retains_the_original_baseline (start : Cursor code)
    (past : List (EventHistory.Stage (code := code))) :
    (EventStep.seed start).past <+: (EventStep.seed (EventHistory.execute start past)).past := by
  induction past generalizing start with
  | nil => exact List.prefix_refl _
  | cons stage tail ih =>
    have next : (EventStep.seed start).past <+: (EventStep.seed (start.after stage.1 stage.2)).past := by
      rw [EventStep.actual_next_state]
      exact (QueueScheduler.advance_preserves_memory_and_queue code (some stage.1.work.val)
        (EventStep.applied start stage.1 stage.2) (EventStep.seed start)).1
    exact next.trans (ih (start.after stage.1 stage.2))

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.OriginQueue
