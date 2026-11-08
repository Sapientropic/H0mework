import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AdaptiveDeliveryBudget

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ResidualAdaptiveDeadline
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open AdaptiveDeliveryTrace AdaptiveDeliveryProgress

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}
  (start : Cursor code) (protocols : Nat → Rule code) (rivals : Nat → Opponent code)

-- The origin owns the attempt baseline; begin selects an actual later resource window.
abbrev opportunities (begin allowance : Nat) := rank start protocols rivals begin * (allowance + 1)
abbrev windowStart (birth : Nat) := max (warmup start) birth
abbrev horizon (begin allowance birth : Nat) :=
  windowStart start birth + 2 * opportunities start protocols rivals begin allowance
abbrev Compliant (begin allowance stop : Nat) := ∀ n, begin ≤ n → n < stop →
  InterferenceEnvelope.intake (cursorAt start protocols rivals n) (rivals n) ∈
    InterferenceEnvelope.choices start (stages protocols rivals n) allowance

theorem pending_potential_never_increases
    (begin allowance serial first last : Nat) (born : begin ≤ first) (later : first ≤ last)
    (active : last ≤ (EventStep.seed start).remaining)
    (present : serial < (state start protocols rivals first).frame.sent.length)
    (pending : serial ∈ QueueScheduler.untried code (baseline start) (state start protocols rivals last).past)
    (compliant : Compliant start protocols rivals begin allowance last) :
    potential start protocols rivals allowance last ≤ potential start protocols rivals allowance first := by
  induction last, later using Nat.le_induction with
  | base => exact Nat.le_refl _
  | succ last _ ih =>
    have previous := later_untried start protocols rivals last (last + 1) (by omega) pending
    have before := ih (by omega) previous (fun n lower hn => compliant n lower (by omega))
    have step := each_pending_external_turn_spends_the_source_generated_potential start protocols rivals allowance last serial
      (by omega) (lt_of_lt_of_le present (memory_queue start protocols rivals first last (by omega)).2.length_le)
      previous (compliant last (by omega) (by omega))
    omega

theorem every_source_pending_packet_is_attempted_before_the_residual_deadline
    (begin allowance birth serial : Nat) (begun : begin ≤ birth) (enough : horizon start protocols rivals begin allowance birth ≤ (EventStep.seed start).remaining)
    (present : serial < (state start protocols rivals birth).frame.sent.length)
    (untried : serial ∈ QueueScheduler.untried code (baseline start) (state start protocols rivals birth).past)
    (compliant : Compliant start protocols rivals begin allowance (horizon start protocols rivals begin allowance birth)) :
    ∃ index, birth ≤ index ∧ index < horizon start protocols rivals begin allowance birth ∧
      StageReception.delivered (row start protocols rivals index) serial = true := by
  have attempted : serial ∈ QueueScheduler.attempted code (baseline start)
      (state start protocols rivals (horizon start protocols rivals begin allowance birth)).past := by
    by_contra missing
    let cap := opportunities start protocols rivals begin allowance
    let stop := horizon start protocols rivals begin allowance birth
    have pending : serial ∈ QueueScheduler.untried code (baseline start) (state start protocols rivals stop).past :=
      Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp untried).1, missing⟩
    have monotone : ∀ first last, birth ≤ first → first ≤ last → last ≤ stop →
        potential start protocols rivals allowance last ≤ potential start protocols rivals allowance first := by
      intro first last born later bounded
      exact pending_potential_never_increases start protocols rivals begin allowance serial first last (by omega) later
        (by omega) (lt_of_lt_of_le present (memory_queue start protocols rivals birth first born).2.length_le) (later_untried start protocols rivals last stop bounded pending)
        (fun n lower hn => compliant n lower (by omega))
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
          (later_untried start protocols rivals index stop (by omega) pending) (compliant index (by dsimp [index,windowStart];omega) beforeStop)
        rw [ext] at step
        simp only [↓reduceIte] at step
        omega
    have counted := descent cap (Nat.le_refl _)
    have positive : 1 ≤ rank start protocols rivals stop := Finset.card_pos.mpr ⟨serial, pending⟩
    have minimum := Nat.mul_le_mul_right (allowance + 1) positive
    have maximum : rank start protocols rivals (windowStart start birth) ≤ rank start protocols rivals begin :=
      Finset.card_le_card (later_untried start protocols rivals begin (windowStart start birth) (by dsimp [windowStart];omega))
    have product := Nat.mul_le_mul_right (allowance + 1) maximum
    change potential start protocols rivals allowance stop + cap ≤ _ at counted
    dsimp only [potential] at counted
    dsimp only [cap, opportunities] at counted
    simp only [Nat.one_mul] at minimum
    omega

  obtain ⟨index, bounded, delivered⟩ := (AdaptiveDeliveryDeadline.attempted_memory_is_actual_delivery_history start protocols rivals _ serial).mp attempted
  refine ⟨index, ?_, bounded, delivered⟩
  by_contra earlier
  have previous := (AdaptiveDeliveryDeadline.attempted_memory_is_actual_delivery_history start protocols rivals birth serial).mpr ⟨index, by omega, delivered⟩
  exact (Finset.mem_sdiff.mp untried).2 previous

theorem continuation_preserves_the_actual_prefix_interface_spending
    (begin allowance stop : Nat)
    (compliant : Compliant start protocols rivals begin allowance stop) :
    ∀ n, begin ≤ n → n ≤ stop →
      InterferenceEnvelope.spent start (stages protocols rivals n) ≤
        max code.eventLimit (InterferenceEnvelope.spent start (stages protocols rivals begin)) := by
  intro n born last
  induction n, born using Nat.le_induction with
  | base => exact Nat.le_max_right _ _
  | succ n lower ih =>
    have previous := ih (by omega)
    have counts : InterferenceEnvelope.spent start (stages protocols rivals (n + 1)) =
        InterferenceEnvelope.spent start (stages protocols rivals n) +
          if InterferenceEnvelope.interference start (row start protocols rivals n) then 1 else 0 := by
      simp only [InterferenceEnvelope.spent, records_succ, List.filter_append, List.length_append]
      split <;> simp_all
    rw [counts]
    split
    · have capacity := AdaptiveDeliveryBudget.a_charged_actual_callback_needs_unspent_source_capacity
        start protocols rivals allowance n (compliant n lower (by omega)) (by assumption)
      omega
    · omega

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ResidualAdaptiveDeadline
