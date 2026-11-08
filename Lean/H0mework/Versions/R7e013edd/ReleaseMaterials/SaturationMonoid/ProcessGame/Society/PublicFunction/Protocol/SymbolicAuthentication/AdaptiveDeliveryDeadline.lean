import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AdaptiveDeliveryProgress

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AdaptiveDeliveryDeadline
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open AdaptiveDeliveryTrace AdaptiveDeliveryProgress

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}
  (start : Cursor code) (protocols : Nat → Rule code) (rivals : Nat → Opponent code)

abbrev opportunities (allowance : Nat) := (QueueScheduler.admitted code).card * (allowance + 1)
abbrev windowStart (birth : Nat) := max (warmup start) birth
abbrev horizon (allowance birth : Nat) := windowStart start birth + 2 * opportunities (code := code) allowance
abbrev Compliant (allowance stop : Nat) := ∀ n < stop,
  InterferenceEnvelope.intake (cursorAt start protocols rivals n) (rivals n) ∈
    InterferenceEnvelope.choices start (stages protocols rivals n) allowance

theorem pending_potential_never_increases
    (allowance serial first last : Nat) (later : first ≤ last)
    (active : last ≤ (EventStep.seed start).remaining)
    (present : serial < (state start protocols rivals first).frame.sent.length)
    (pending : serial ∈ QueueScheduler.untried code (baseline start) (state start protocols rivals last).past)
    (compliant : Compliant start protocols rivals allowance last) :
    potential start protocols rivals allowance last ≤ potential start protocols rivals allowance first := by
  induction last, later using Nat.le_induction with
  | base => exact Nat.le_refl _
  | succ last _ ih =>
    have previous := later_untried start protocols rivals last (last + 1) (by omega) pending
    have before := ih (by omega) previous (fun n hn => compliant n (by omega))
    have step := each_pending_external_turn_spends_the_source_generated_potential start protocols rivals allowance last serial
      (by omega) (lt_of_lt_of_le present (memory_queue start protocols rivals first last (by omega)).2.length_le)
      previous (compliant last (by omega))
    omega

theorem attempted_memory_is_actual_delivery_history (count serial : Nat) :
    serial ∈ QueueScheduler.attempted code (baseline start) (state start protocols rivals count).past ↔
      ∃ index < count, StageReception.delivered (row start protocols rivals index) serial = true := by
  induction count with
  | zero => simp [QueueScheduler.attempted, baseline, OriginQueue.baseline, AdaptiveDeliveryTrace.state, cursorAt]
  | succ count ih =>
    have bounded := (memory_queue start protocols rivals 0 count (Nat.zero_le _)).1.length_le
    change baseline start ≤ (state start protocols rivals count).past.length at bounded
    have admitted : StageTransport.admission (row start protocols rivals count) =
        decision code (EventStep.applied (cursorAt start protocols rivals count) (protocols count) (rivals count))
          (state start protocols rivals count) := StageTrace.captured_admission_is_the_actual_decision _ _ _ _
    have next : serial ∈ QueueScheduler.attempted code (baseline start) (state start protocols rivals (count + 1)).past ↔
        serial ∈ QueueScheduler.attempted code (baseline start) (state start protocols rivals count).past ∨
          StageReception.delivered (row start protocols rivals count) serial = true := by
      change serial ∈ QueueScheduler.attempted code _ (EventStep.seed ((cursorAt start protocols rivals count).after _ _)).past ↔ _
      rw [EventStep.actual_next_state]
      simp only [StageReception.delivered, admitted]
      cases selected : decision code (EventStep.applied (cursorAt start protocols rivals count) (protocols count) (rivals count))
          (state start protocols rivals count) with
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
    · rintro (⟨index, before, delivered⟩ | delivered)
      · exact ⟨index, by omega, delivered⟩
      · exact ⟨count, by omega, delivered⟩
    · rintro ⟨index, before, delivered⟩
      by_cases same : index = count
      · exact Or.inr (same ▸ delivered)
      · exact Or.inl ⟨index, by omega, delivered⟩

theorem every_compliant_adaptive_execution_attempts_each_pending_packet_before_the_source_deadline
    (allowance birth serial : Nat) (enough : horizon start allowance birth ≤ (EventStep.seed start).remaining)
    (present : serial < (state start protocols rivals birth).frame.sent.length)
    (untried : serial ∈ QueueScheduler.untried code (baseline start) (state start protocols rivals birth).past)
    (compliant : Compliant start protocols rivals allowance (horizon start allowance birth)) :
    ∃ index, birth ≤ index ∧ index < horizon start allowance birth ∧
      StageReception.delivered (row start protocols rivals index) serial = true := by
  have attempted : serial ∈ QueueScheduler.attempted code (baseline start)
      (state start protocols rivals (horizon start allowance birth)).past := by
    by_contra missing
    let cap := opportunities (code := code) allowance
    let stop := horizon start allowance birth
    have pending : serial ∈ QueueScheduler.untried code (baseline start) (state start protocols rivals stop).past :=
      Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp untried).1, missing⟩
    have monotone : ∀ first last, birth ≤ first → first ≤ last → last ≤ stop →
        potential start protocols rivals allowance last ≤ potential start protocols rivals allowance first := by
      intro first last born later bounded
      exact pending_potential_never_increases start protocols rivals allowance serial first last later
        (by omega) (lt_of_lt_of_le present (memory_queue start protocols rivals birth first born).2.length_le) (later_untried start protocols rivals last stop bounded pending)
        (fun n hn => compliant n (by omega))
    have descent : ∀ k ≤ cap,
        potential start protocols rivals allowance (windowStart start birth + 2 * k) + k ≤
          potential start protocols rivals allowance (windowStart start birth) := by
      intro k
      induction k with
      | zero => intro _; simp
      | succ k ih =>
        intro bounded
        have previous := ih (by omega)
        obtain ⟨offset, small, owner⟩ := external_in_each_pair start protocols rivals (windowStart start birth + 2 * k) (by dsimp [windowStart]; omega)
        let index := windowStart start birth + 2 * k + offset
        have beforeStop : index < stop := by dsimp only [index, stop, horizon]; omega
        have before := monotone (windowStart start birth + 2 * k) index (by dsimp [windowStart]; omega) (by dsimp [index]; omega) (by omega)
        have after := monotone (index + 1) (windowStart start birth + 2 * (k + 1)) (by dsimp [index, windowStart]; omega) (by dsimp [index]; omega) (by dsimp only [stop, horizon]; omega)
        have live : (state start protocols rivals index).remaining ≠ 0 := by
          rw [(clocks start protocols rivals index).2.1]; omega
        change Distributed.Recall.Information.Agency.ownerAt code
          (cursorAt start protocols rivals index).ownerStart (state start protocols rivals index).history.length = none at owner
        have ext : external start protocols rivals index = true := by
          simp only [external, row, StageTrace.material, StageTrace.capture, if_neg live, owner]
        have step := each_pending_external_turn_spends_the_source_generated_potential start protocols rivals allowance index serial
          (by omega) (lt_of_lt_of_le present (memory_queue start protocols rivals birth index (by dsimp [index, windowStart]; omega)).2.length_le)
          (later_untried start protocols rivals index stop (by omega) pending) (compliant index beforeStop)
        rw [ext] at step
        simp only [↓reduceIte] at step
        omega
    have counted := descent cap (Nat.le_refl _)
    have positive : 1 ≤ rank start protocols rivals stop := Finset.card_pos.mpr ⟨serial, pending⟩
    have minimum := Nat.mul_le_mul_right (allowance + 1) positive
    have maximum : rank start protocols rivals (windowStart start birth) ≤ (QueueScheduler.admitted code).card :=
      Finset.card_le_card Finset.sdiff_subset
    have product := Nat.mul_le_mul_right (allowance + 1) maximum
    change potential start protocols rivals allowance stop + cap ≤ _ at counted
    dsimp only [potential] at counted
    dsimp only [cap, opportunities] at counted
    simp only [Nat.one_mul] at minimum
    omega

  obtain ⟨index, bounded, delivered⟩ := (attempted_memory_is_actual_delivery_history start protocols rivals _ serial).mp attempted
  refine ⟨index, ?_, bounded, delivered⟩
  by_contra earlier
  have previous := (attempted_memory_is_actual_delivery_history start protocols rivals birth serial).mpr ⟨index, by omega, delivered⟩
  exact (Finset.mem_sdiff.mp untried).2 previous

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AdaptiveDeliveryDeadline
